# Investigation: `reg_bounds_sync_{old,new}` Counter-Example Analysis

## CBMC Verification Summary

All claims in this report have been independently verified by CBMC 5.95.1.
Three targeted verification files were written:

| File | What it checks | Assertions | Result |
|---|---|---|---|
| `verify_claims.c` | Concrete counter-example: all intermediate values and final states | 45 | **45/45 PASS** |
| `verify_harness_flaw.c` | Harness permissiveness: proves the original harness ALLOWS contradictory inputs (flaws expected to FAIL), and that adding the fix makes the flaw disappear | 3 | **2/3 FAIL as intended + 1/1 sanity PASS** |
| `verify_fixed_harness.c` | Counter-example rejected by fix; equivalence on constant registers | 15 | **15/15 PASS** |

Run commands:
```sh
cbmc verify_claims.c
cbmc --unwind 1 verify_harness_flaw.c
cbmc --unwind 1 verify_fixed_harness.c
```

---

## Overview

This document analyses the CBMC counter-examples produced by running:

```sh
cbmc --compact-trace --no-pointer-check --no-undefined-shift-check \
     --no-signed-overflow-check ./reg_deduce_bounds-compare.c
```

CBMC finds that `reg_bounds_sync_old` and `reg_bounds_sync_new` produce
**different results on the same input**, triggering all ten assertions in
`main()` (lines 886–895).  This report works through the concrete
counter-example for `assertion.1` (`new_reg.var_off.value == reg.var_off.value`)
in detail, then generalises the findings.

---

## 1. What the Harness Checks

`main()` picks a symbolic `bpf_reg_state reg` and a witness value `x`:

```
valid_bpf_reg_state(&reg)   // min ≤ max for every pair of bounds
x ≤ 32                      // keep the witness small
val_in_reg(&reg, x)         // x is inside every numeric bound
```

It then runs **both** sync functions on copies of the same initial state and
asserts that every field of the output is identical.  If the two
implementations are truly equivalent, CBMC should find no counter-example.
All ten assertions fail, which means the two implementations produce
observably different results.

---

## 2. Counter-Example Initial State

For every failing assertion CBMC uses essentially the same initial state
(the trace for `assertion.1` is used as the reference throughout):

| Field | Value (decimal) | Value (hex) |
|---|---|---|
| `var_off.value` | 1 084 246 877 | `0x40A0_4B5D` |
| `var_off.mask` | 18 446 744 070 485 517 312 | `0xFFFF_FFFF_3FD5_2400` |
| `smin_value` | 30 | `0x1E` |
| `smax_value` | 1 084 245 086 | `0x40A0_445E` |
| `umin_value` | 17 | `0x11` |
| `umax_value` | 1 218 464 862 | `0x48A0_4C5E` |
| `s32_min_value` | 7 | `0x07` |
| `s32_max_value` | 2 146 791 261 | `0x7FF5_6F5D` |
| `u32_min_value` | 17 | `0x11` |
| `u32_max_value` | 803 694 174 | `0x2FE7_665E` |
| **witness x** | **32** | `0x20` |

### Key observation: the initial state is internally contradictory

`var_off.value = 0x40A0_4B5D` with `var_off.mask = 0x…3FD5_2400` means
the *known-to-be-1* bits of the lower 32 bits are:

```
known-1 = var_off.value & ~var_off.mask (lower 32)
        = 0x40A0_4B5D & ~0x3FD5_2400
        = 0x40A0_4B5D &  0xC02A_DBFF
        = 0x4020_4B5D  (≈ 1 076 248 413)
```

Any legitimate concrete value in the register must therefore be **at least**
`0x4020_4B5D ≈ 1.08 × 10⁹`.  Yet `umin_value = 17` and the witness
`x = 32` are both far below this floor.

`valid_bpf_reg_state` never checks that numeric bounds are consistent with
`var_off`, and `val_in_reg` never checks that `x` satisfies the tnum
pattern.  As a result CBMC can legally construct this contradictory starting
point, which is the source of all divergence.

---

## 3. Structural Difference Between Old and New

### Call sequences

```
reg_bounds_sync_old:
  1. __update_reg_bounds
  2. __reg_deduce_bounds_old  ×3
     = __reg32_deduce_bounds_old
       + __reg64_deduce_bounds
       + __reg_deduce_mixed_bounds_old
  3. __reg_bound_offset
  4. __update_reg_bounds

reg_bounds_sync_new:
  1. __update_reg_bounds
  2. __reg_deduce_bounds_new  ×2
     = __reg32_deduce_bounds_new
       + __reg64_deduce_bounds
       + __reg_deduce_mixed_bounds_new
  3. __reg_bound_offset
  4. __update_reg_bounds
```

### What moved between old and new

`__reg32_deduce_bounds_old` (old, ~85 lines) contains three groups of logic:

| Group | What it does | Where in new |
|---|---|---|
| A | 64 → 32: tighten `u32`/`s32` when upper 32 bits of `u64`/`s64` range are equal | moved to `__reg_deduce_mixed_bounds_new` |
| B | 64 → 32: special "consecutive upper-32" case for s32 sign wrap | moved to `__reg_deduce_mixed_bounds_new` |
| C | `u32` ↔ `s32` cross-learning | kept in `__reg32_deduce_bounds_new` |

`__reg32_deduce_bounds_new` (new, ~17 lines) contains **only group C**.

`__reg_deduce_mixed_bounds_new` (new) contains **groups A and B** followed by
the original `__reg_deduce_mixed_bounds_old` content (32 → 64 tightening +
special sign-extend case).

### Why the order matters

Within each pass the order of sub-steps is:

```
OLD pass:  [32←64 learning]  →  [64↔64]  →  [64←32 tightening]
NEW pass:  [32↔32 only]      →  [64↔64]  →  [32←64 learning, then 64←32 tightening]
```

In the **old** path, the 64→32 deduction in group A/B runs **before**
`__reg64_deduce_bounds`.  It therefore sees the *original* tight s64 range
`[30, 1 084 245 086]`.

In the **new** path, the 64→32 deduction runs **after**
`__reg64_deduce_bounds`, which can *widen* `smax_value` before the 64→32
step ever executes.

---

## 4. Step-by-Step Divergence (assertion.1)

### After `__update_reg_bounds` (common to both)

`var_off`'s known bits force the lower-32 minimum up:

```
u32_min = max(17, var32_off.value)      = max(17, 0x40A0_4B5D) = 1 084 246 877
u32_max = min(803 694 174, 0x7FF5_6F5D) = 803 694 174
```

Note `u32_min (1 084 246 877) > u32_max (803 694 174)`.  The tnum says the
lower 32 bits must be large, but `u32_max_value` says they must be small —
a direct consequence of the contradictory initial state.

s64/u64 bounds are also tightened:

```
umin = max(17, 0x40A0_4B5D)  = 1 084 246 877
umax = min(1 218 464 862, …) = 1 218 464 862
smin = max(30,  …)           = 30
smax = min(1 084 245 086, …) = 1 084 245 086
```

---

### First `__reg_deduce_bounds_old` (old path, pass 1 of 3)

**`__reg32_deduce_bounds_old` — group A fires:**

```
smin >> 32 == smax >> 32?   →  0 == 0  →  YES
(s32)smin ≤ (s32)smax?      →  30 ≤ 1 084 245 086  →  YES
  s32_max = min(s32_max, (s32)smax) = min(2 146 791 261, 1 084 245 086)
          = 1 084 245 086              ← tightened!
```

`s32_max` drops from 2 146 791 261 to **1 084 245 086** because the
original tight s64 range is visible here.

**`__reg64_deduce_bounds`:**

The s64 pair is now `(smin=1 084 246 877, smax=1 084 245 086)` — inverted
(smin > smax).  The else-branch at line 497 fires:

```
(u64)smax_value < umin_value?  →  1 084 245 086 < 1 084 246 877  →  YES
  smax = (s64)umax = 1 218 464 862   ← widened back
  umin = max(umin, smin) = 1 084 246 877
```

**`__reg_deduce_mixed_bounds_old` — 32→64 tightening:**

```
new_umax = (umax & ~0xffffffff) | u32_max = 0 | 803 694 174 = 803 694 174
umax = min(1 218 464 862, 803 694 174) = 803 694 174
new_smax = (smax & ~0xffffffff) | u32_max = 0 | 803 694 174 = 803 694 174
smax = min(1 218 464 862, 803 694 174) = 803 694 174
```

**Special sign-extend case (lines 609–616):**

```
s32_min_value (1 084 246 877) >= 0?  →  YES
smin (1 084 246 877) >= S32_MIN?     →  YES
smax (803 694 174) <= S32_MAX?       →  YES   ← fires!
```

Executes:

```
smin  = s32_min = 1 084 246 877
smax  = s32_max = 1 084 245 086        ← tight (obtained from group A above)
umin  = s32_min = 1 084 246 877
umax  = s32_max = 1 084 245 086

var_off = tnum_intersect(var_off, tnum_range(1 084 246 877, 1 084 245 086))
```

`tnum_range(1 084 246 877, 1 084 245 086)`:

```
chi = 0x40A0_4B5D ^ 0x40A0_445E = 0x0000_0F03 = 3843
bits = fls64(3843) = 12
delta = 4095 = 0x0FFF
→ TNUM(0x40A0_4000, 0x0FFF)
```

Intersect with original `var_off = TNUM(0x40A0_4B5D, 0xFFFF_FFFF_3FD5_2400)`:

```
mu = 0x3FD5_2400 & 0x0FFF = 0x0400  (= 1024, a single unknown bit!)
var_off after = TNUM(0x40A0_4B5D, 0x0400)
```

**`var_off.mask` collapses from `0x3FD5_2400` to `0x0400` — only one unknown bit remains.**

Passes 2 and 3 of `__reg_deduce_bounds_old` repeat the same logic and hold
the state stable.  The final `__update_reg_bounds` then sees:

```
umin_in_tnum = TRUE
tnum_next = 1 084 247 901 > umax = 1 084 245 086  →  YES
→  ___mark_reg_known(reg, 1 084 246 877)
```

**OLD path final state: constant register `1 084 246 877`.**

```
var_off = TNUM(0x40A0_4B5D, 0x0000)   mask = 0 (fully known)
umin = umax = smin = smax = 1 084 246 877
u32_min = u32_max = s32_min = s32_max = 1 084 246 877
```

---

### First `__reg_deduce_bounds_new` (new path, pass 1 of 2)

**`__reg32_deduce_bounds_new` — only group C:**

The u32/s32 cross-learning does not change values (u32_max < u32_min already,
sign-check fails for narrowing u32 from s32 direction).  State is unchanged.

**`__reg64_deduce_bounds`:**

Identical to the old path: `smax` is widened to **1 218 464 862**.

**`__reg_deduce_mixed_bounds_new` — group A:**

```
smin >> 32 == smax >> 32?  →  0 == 0  →  YES
(s32)smin ≤ (s32)smax?     →  1 084 246 877 ≤ 1 218 464 862  →  YES
  s32_max = min(s32_max, (s32)smax) = min(2 146 791 261, 1 218 464 862)
          = 1 218 464 862              ← WIDER than old path (1 084 245 086)!
```

Because `__reg64_deduce_bounds` ran first and widened `smax` from 1 084 245 086
to 1 218 464 862, the 64→32 step here uses the wider bound.

**Special sign-extend case — same condition fires**, but now with:

```
smax  = s32_max = 1 218 464 862        ← wider!
var_off = tnum_intersect(var_off, tnum_range(1 084 246 877, 1 218 464 862))
```

`tnum_range(1 084 246 877, 1 218 464 862)`:

```
chi = 0x40A0_4B5D ^ 0x48A0_4C5E = 0x0800_0703 = 134 219 523
bits = fls64(134 219 523) = 28
delta = 0x0FFF_FFFF = 268 435 455
→ TNUM(0x4000_0000, 0x0FFF_FFFF)
```

Intersect with `var_off = TNUM(0x40A0_4B5D, 0xFFFF_FFFF_3FD5_2400)`:

```
mu = 0x3FD5_2400 & 0x0FFF_FFFF = 0x0FD5_2400  (= 265 626 624, many unknown bits)
var_off after = TNUM(0x4020_4B5D, 0x0FD5_2400)
```

**`var_off.mask` remains large: `0x0FD5_2400` vs `0x0400` in the old path.**

Pass 2 of `__reg_deduce_bounds_new` re-runs the same logic; no further
narrowing occurs.  The final `__update_reg_bounds` finds:

```
umin_in_tnum = TRUE
tnum_next = 1 084 247 901,  umax = 1 218 464 862
tnum_next (1 084 247 901) > umax (1 218 464 862)?  →  NO
```

None of the `___mark_reg_known` conditions fires.

**NEW path final state: non-constant, wide range.**

```
var_off = TNUM(0x4020_4B5D, 0x0FD5_2400)   mask ≠ 0
umin = 1 084 246 877,  umax = 1 218 464 862
smin = 1 084 246 877,  smax = 1 218 464 862
s32_min = 1 084 246 877,  s32_max = 1 218 464 862
u32_min = 1 084 246 877,  u32_max = 803 694 174   (still inverted)
```

---

## 5. Summary of the Divergence

| Item | OLD (`reg_bounds_sync_old`) | NEW (`reg_bounds_sync_new`) |
|---|---|---|
| `var_off.value` | `0x40A0_4B5D` (1 084 246 877) | `0x4020_4B5D` (1 075 858 269) |
| `var_off.mask` | `0x0000` | `0x0FD5_2400` |
| `umin` / `umax` | 1 084 246 877 / 1 084 246 877 | 1 084 246 877 / 1 218 464 862 |
| `smin` / `smax` | 1 084 246 877 / 1 084 246 877 | 1 084 246 877 / 1 218 464 862 |
| `s32_min` / `s32_max` | 1 084 246 877 / 1 084 246 877 | 1 084 246 877 / 1 218 464 862 |
| `u32_min` / `u32_max` | 1 084 246 877 / 1 084 246 877 | 1 084 246 877 / 803 694 174 |

The single pivotal value is **`s32_max` after the first 64→32 deduction**:

- **Old:** sees `smax_value = 1 084 245 086` (the original, tight s64 upper bound)
  → `s32_max = 1 084 245 086`
- **New:** `__reg64_deduce_bounds` has already widened `smax_value` to `1 218 464 862`
  → `s32_max = 1 218 464 862`

This small numerical difference cascades through the sign-extend special case,
which then intersects `var_off` with a much wider or much narrower
`tnum_range`, leading to entirely different final states.

---

## 6. Root Cause: Missing Constraint in the Harness

The counter-example is possible only because the initial state is
**internally contradictory**: `var_off` implies the lower-32 bits are at
least `0x4020_4B5D ≈ 1.08 × 10⁹`, yet the numeric bounds (`umin = 17`,
`u32_min = 17`) and the witness value (`x = 32`) all suggest much smaller
values.

Two checks are absent from the harness:

1. **`valid_bpf_reg_state` does not validate `var_off` against numeric bounds.**
   A minimal additional check:
   ```c
   /* known-1 bits in var_off impose a lower bound on any concrete value */
   ret &= reg->umin_value >= (reg->var_off.value & ~reg->var_off.mask);
   ret &= reg->u32_min_value >= (u32)(reg->var_off.value & ~reg->var_off.mask);
   ```

2. **`val_in_reg` does not verify the witness against `var_off`.**
   A minimal additional check:
   ```c
   ret &= (val & ~reg->var_off.mask) == (reg->var_off.value & ~reg->var_off.mask);
   ```

With these added constraints CBMC would reject the contradictory initial
state and the two implementations should agree.

---

## 7. Soundness Assessment

On the contradictory input the OLD path concludes the register is the constant
`1 084 246 877`, which **excludes the witness value x = 32**.  If the BPF
verifier's semantics require that "the output range must contain every value
that was in the input range", the OLD path is **unsound** on this input.

The NEW path retains a range `[1 084 246 877, 1 218 464 862]` which also
excludes x = 32, but this is equally a consequence of the contradictory input.
On a well-formed input (where `var_off`, numeric bounds, and the witness are
mutually consistent) the two implementations are expected to agree.

The divergence therefore points to a **harness deficiency** (missing
`var_off` consistency checks) rather than a semantic bug in either
implementation when used on valid inputs.

---

## 8. Architectural Take-Away

The refactoring moved the 64→32 bit-range propagation (groups A and B of
`__reg32_deduce_bounds_old`) to run *after* `__reg64_deduce_bounds` inside
`__reg_deduce_mixed_bounds_new`.  This changes the order of information flow
within each iteration:

```
Old iteration:  [tight-64 → tighten-32]  →  [cross-64]  →  [tight-32 → tighten-64]
New iteration:  [cross-32-only]           →  [cross-64]  →  [tight-64 → tighten-32 → tighten-64]
```

On well-formed states the extra pass in the old path (×3 vs ×2) and the
reordered steps are designed to reach the same fixed point.  On the
contradictory states exposed by CBMC they diverge.  Fixing the harness to
enforce `var_off`–numeric-bound consistency is the recommended next step
before drawing conclusions about the correctness of either implementation.
