# Divergence Investigation Plan: `reg_bounds_sync_old` vs `reg_bounds_sync_new`

## Status

- [x] Phase 1 — Initial counter-example analysis (`INVESTIGATION.md`)
- [x] Phase 2 — Harness fix: tnum consistency constraints added to `valid_bpf_reg_state`
         and `val_in_reg` (`reg_deduce_bounds-compare.c`)
- [ ] Phase 3 — **This plan**: characterise genuine divergences on valid inputs

---

## What We Know

After the harness fix, CBMC still finds 10/10 assertions failing.  The
fixed harness rejects malformed tnums, so the remaining counter-examples
represent **real algorithmic differences** between old and new on
well-formed register states.

Four distinct initial states appear across the ten failing assertions.
All share a characteristic shape: `umax` has the sign bit set
(`umax > S64_MAX`) while `smax` is small and positive, and `smin` is
negative.  This is the "straddles zero as signed, includes large-unsigned"
pattern common in BPF register tracking.

| CE | x  | var_off.value | var_off.mask (hex)     | smin        | smax      | umin | umax (hex)          |
|----|----|---------------|------------------------|-------------|-----------|------|---------------------|
| A  |  5 | `0x01`        | `0xFFFFFFFF_800000D4`  | -1968178437 |        13 |    4 | `0xFFFFFFFF_80000072` |
| B  | 21 | `0x01`        | `0xFFFFFFFF_A0000016`  | -2147483627 | 536870933 |   17 | `0xFFFFFFFF_80000004` |
| C  | 32 | `0x00`        | `0xFFFFFFFF_800000B0`  | -2147483536 |        35 |   24 | `0xFFFFFFFF_800000B0` |
| D  |  6 | `0x02`        | `0xFFFFFFFF_800009A4`  | -2147482622 |      1066 |    3 | `0xFFFFFFFF_800009A6` |

---

## Goals

1. **Soundness** — does either path produce output bounds that *exclude* the
   witness `x`?  An algorithm that drops a known-valid value is unsound and
   potentially dangerous.

2. **Precision** — when they differ, which path produces tighter (more
   informative) output bounds?  A more precise result allows the verifier to
   accept more safe programs.

3. **Root-cause mapping** — which specific code-path difference (ordering of
   `__reg32_deduce_bounds` vs `__reg64_deduce_bounds`) is responsible, and
   under what input condition does it fire?

4. **Hypothesis verification** — write a CBMC harness to confirm or falsify
   the structural hypothesis derived from manual analysis.

---

## Proposed Investigation Steps

### Step 1 — Soundness harness (`reg_soundness-compare.c`)

Write a new harness that, for every valid input with witness `x`, checks
that *both* output states still contain `x`:

```c
/* After running old and new sync: */
__CPROVER_assert(val_in_reg(&old_reg, x), "old is sound: x in old output");
__CPROVER_assert(val_in_reg(&new_reg, x), "new is sound: x in new output");
```

Expected outcome options:
- Both PASS → neither path has a soundness bug; divergence is precision-only.
- Old FAILS → old produces over-tightened (unsound) bounds for some valid x.
- New FAILS → new produces over-tightened (unsound) bounds for some valid x.

If a soundness failure is found, the counter-example directly shows a
register value that a verifier would incorrectly classify as impossible.

### Step 2 — Precision comparison harness (`reg_precision-compare.c`)

For each of the ten output fields, check whether one path is *always* at
least as tight as the other:

```c
/* Example for umin/umax: larger umin = more precise lower bound */
__CPROVER_assert(old_reg.umin_value >= new_reg.umin_value,
    "old umin >= new umin (old as precise or better)");
__CPROVER_assert(new_reg.umax_value <= old_reg.umax_value,
    "new umax <= old umax (new as precise or better on upper bound)");
```

Run all ten pairs.  The results will classify each field as:
- **old strictly tighter** — old is always ≥ new for lower bounds, ≤ for upper bounds
- **new strictly tighter** — new is always ≥/≤ in the right direction
- **incomparable** — neither dominates (one path is better on some inputs,
  the other on others)

### Step 3 — Root-cause: sign-extend special case trigger condition

The structural difference between old and new is:

```
OLD path:  __reg32_deduce_bounds_old  ← groups A+B (32→64 sign-extend)
           __reg64_deduce_bounds      ← may widen smax
           (second pass of above, repeated ×3 total)

NEW path:  __reg64_deduce_bounds      ← widens smax FIRST
           __reg_deduce_mixed_bounds_new  ← groups A+B now see wider smax
```

The sign-extend special case in group A fires when:
```c
s32_min_value >= 0 && smin_value >= S32_MIN && smax_value <= S32_MAX
```

In OLD this condition is evaluated against the *original* `smax`.
In NEW it is evaluated after `__reg64_deduce_bounds` may have widened `smax`.

**Hypothesis**: divergence occurs iff the special-case condition evaluates
differently for old-smax vs new-smax, i.e. iff `old_smax <= S32_MAX` but
`new_smax > S32_MAX` (or vice versa) after the first call to
`__reg64_deduce_bounds`.

Write a harness to verify this by instrumenting the intermediate smax
value and checking whether the sign-extend branch fires in each path.

### Step 4 — Divergence condition harness (`reg_divergence-condition.c`)

Once the hypothesis is formulated, encode it as a CBMC `assume` and
check that the asserted equivalence holds when the triggering condition
is disabled:

```c
/* Assume the condition that would prevent the special-case from
 * firing differently.  If old ≡ new under this assume, the hypothesis
 * is confirmed. */
__CPROVER_assume(/* condition that makes both paths take the same branch */);

/* Now equivalence should hold */
__CPROVER_assert(old_reg.smax_value == new_reg.smax_value,
    "equivalent under restricted input");
```

If CBMC reports SUCCESS for all fields under the restricted assume,
the hypothesis is confirmed.  If CBMC still finds failures, the
hypothesis is incomplete and needs refinement.

### Step 5 — Document findings

Update `INVESTIGATION.md` with:
- Soundness verdict (which path, if any, is unsound)
- Precision verdict (which path produces tighter bounds and for which fields)
- Confirmed trigger condition
- Recommendation: is new a strict improvement over old, or does it trade
  precision in one dimension for another?

---

## File Layout

```
reg_soundness-compare.c        ← Step 1: soundness harness
reg_precision-compare.c        ← Step 2: precision comparison harness
reg_divergence-condition.c     ← Steps 3+4: trigger condition harness
```

All three files will reuse the types, tnum helpers, and
`valid_bpf_reg_state`/`val_in_reg` from `reg_deduce_bounds-compare.c` via
`#include`.  They can be run as:

```sh
cbmc --compact-trace reg_soundness-compare.c
cbmc --compact-trace reg_precision-compare.c
cbmc --compact-trace reg_divergence-condition.c
```

---

## Notes on Harness Correctness

The fixed `valid_bpf_reg_state` encodes these tnum invariants:

| Constraint | What it enforces |
|---|---|
| `value & mask == 0` | tnum well-formedness |
| `umin >= value` | u64 lower bound ≥ tnum minimum |
| `umax <= value \| mask` | u64 upper bound ≤ tnum maximum |
| `smin >= (s64)(value \| (mask & S64_MIN))` | s64 lower bound ≥ tnum signed minimum |
| `smax <= (s64)(value \| (mask & S64_MAX))` | s64 upper bound ≤ tnum signed maximum |
| u32/s32 analogues | same for 32-bit sub-register |

And `val_in_reg` now enforces `(x & ~mask) == value`, ensuring the
witness satisfies the tnum pattern.

If additional kernel invariants are discovered (e.g., `var_off` must
already be intersected with `tnum_range(umin, umax)`), they should be
added to `valid_bpf_reg_state` before concluding Step 1.
