---
name: cbmc-verify
description: Use when the user wants to formally verify C code with CBMC (C Bounded Model Checker), write CBMC harnesses, interpret CBMC output, or design symbolic proofs for data-structure invariants and algorithmic equivalence. Trigger on: "verify with CBMC", "write a CBMC harness", "CBMC proof", "symbolic verification", "bounded model checking".
---

# CBMC Verification Skill

Guide for writing and running CBMC harnesses, interpreting results, and designing effective symbolic proofs.

## What is CBMC?

CBMC is a Bounded Model Checker for C programs. It translates a C program (with bounds on loops) into a propositional formula and checks whether assertions can ever be violated. It finds concrete counter-examples when they exist.

## Workflow

Make a todo list and work through these steps one at a time.

### 1. Understand the Code Under Test

- Read the functions to verify and identify their data structures and invariants
- Identify what properties you want to prove (safety, equivalence, absence of UB)
- Understand any struct invariants that must hold for inputs to be valid

### 2. Write the Harness

A CBMC harness is a `main()` (or standalone function) that:
1. Creates **symbolic inputs** using `nondet_*()` functions
2. **Assumes** preconditions with `__CPROVER_assume(condition)`
3. Calls the function(s) under test
4. **Asserts** postconditions with `__CPROVER_assert(condition, "message")`

```c
#include <stdint.h>
#include <limits.h>
#include <stdbool.h>

/* Declare nondet functions — CBMC treats any nondet_* as symbolic */
unsigned long nondet_ulong(void);
long nondet_long(void);
unsigned int nondet_uint(void);
int nondet_int(void);

void main(void) {
    /* 1. Symbolic inputs */
    uint64_t x = nondet_ulong();
    uint64_t y = nondet_ulong();

    /* 2. Preconditions */
    __CPROVER_assume(x <= 100);
    __CPROVER_assume(y > 0);

    /* 3. Call function(s) */
    uint64_t result = my_function(x, y);

    /* 4. Postconditions */
    __CPROVER_assert(result < 200, "result is bounded");
}
```

### 3. Encode Struct Invariants Carefully

The most common harness mistake is **under-constraining symbolic inputs**. If a struct has invariants, ALL of them must be expressed as `__CPROVER_assume()` calls.

Example — BPF register state with tnum:
```c
/* tnum: {value, mask} where value & mask == 0 (no bit is simultaneously
 * known and unknown). The known-1 bits are (value & ~mask) = value (when
 * well-formed). Maximum concrete value = value | mask. */

static bool valid_bpf_reg_state(struct bpf_reg_state *reg) {
    bool ret = true;
    /* Range invariants */
    ret &= reg->umin_value <= reg->umax_value;
    ret &= reg->smin_value <= reg->smax_value;
    /* tnum well-formedness */
    ret &= (reg->var_off.value & reg->var_off.mask) == 0;
    /* tnum ↔ unsigned bounds */
    ret &= reg->umin_value >= reg->var_off.value;
    ret &= reg->umax_value <= (reg->var_off.value | reg->var_off.mask);
    /* tnum ↔ signed bounds (sign bit can be 0 or 1 in unknown positions) */
    ret &= reg->smin_value >= (int64_t)(reg->var_off.value |
                               (reg->var_off.mask & (uint64_t)INT64_MIN));
    ret &= reg->smax_value <= (int64_t)(reg->var_off.value |
                               (reg->var_off.mask & (uint64_t)INT64_MAX));
    return ret;
}
```

**Rule**: if a field value is constrained by another field in the real system, add that constraint as an `assume`. Missing invariants let CBMC construct contradictory or physically impossible states, producing spurious counter-examples.

### 4. Distinguish Genuine vs. Spurious Counter-Examples

When CBMC reports a failure, always check whether the counter-example state:
- Satisfies ALL invariants you assumed
- Represents a state that could actually occur in the real system

If the counter-example has an obviously impossible state (e.g., a `value & mask != 0` tnum, or `umin > umax`), strengthen `valid_*` and re-run. Repeat until counter-examples only show genuine bugs.

### 5. Run CBMC

```bash
# Basic run (CBMC 5.x / 6.x):
cbmc --unwind 1 harness.c

# With trace to see counter-example values:
cbmc --compact-trace harness.c

# Suppress checks that aren't relevant (CBMC 6.x):
cbmc --no-pointer-check --no-signed-overflow-check harness.c
```

**Version note**: CBMC 5.x vs 6.x have different flag names. CBMC 5.x has fewer `--no-*` flags (most checks are off by default). CBMC 6.x adds some that need explicit opt-out. Check `cbmc --version` and consult the man page.

### 6. Interpret Results

```
** Results:
[main.assertion.1] line 42 assertion result < 200: SUCCESS
[main.assertion.2] line 43 assertion x != y: FAILURE

** 1 of 2 failed (3 iterations)
VERIFICATION FAILED
```

- **SUCCESS**: the assertion holds for ALL inputs satisfying the assumes
- **FAILURE**: CBMC found concrete values (a counter-example) falsifying the assertion
- **Iterations**: SAT solver restarts; multiple failing assertions may produce separate counter-examples

### 7. Reading the Compact Trace

The `--compact-trace` output shows variable assignments in the counter-example execution. Look for:
- The initial symbolic inputs (near the `__bpf_reg_state_input` or `nondet_*` calls)
- Intermediate values showing where the paths diverge
- The final values that violate the assertion

Values are shown as both decimal and binary. Use the binary form to check bit patterns.

## Common Patterns

### Proving Two Functions Are Equivalent

```c
void main(void) {
    struct State s = symbolic_state();
    __CPROVER_assume(valid_state(&s));

    struct State old_s = s;   /* clone */
    struct State new_s = s;

    function_old(&old_s);
    function_new(&new_s);

    __CPROVER_assert(old_s.field == new_s.field, "field equivalence");
}
```

If CBMC reports failure, the concrete counter-example is a direct proof of divergence.

### Proving a Property of One Function (e.g., no overflow)

```c
void main(void) {
    uint32_t a = nondet_uint();
    uint32_t b = nondet_uint();
    __CPROVER_assume(a <= 1000 && b <= 1000);

    uint32_t sum = add_bounded(a, b);
    __CPROVER_assert(sum <= 2000, "no overflow");
}
```

### Verifying Harness Quality (Meta-Verification)

To confirm your harness constraints are not too tight (vacuous) or too loose (spurious), write a second harness that:
1. Applies the same constraints
2. Asserts a property you KNOW must sometimes be violated
3. Expects CBMC to **FAIL** (i.e., find a counter-example showing the harness is non-trivial)

```c
void check_harness_nontrivial(void) {
    struct State s = symbolic_state();
    __CPROVER_assume(valid_state(&s));
    /* Assert something we know is NOT always true — expect FAILURE */
    __CPROVER_assert(s.field == 42,
        "EXPECT FAILURE: field is not always 42");
}
```

If this PASSES, your constraints are vacuous (no states satisfy them).

### tnum Arithmetic

A `tnum {value, mask}` encodes a set of integers where:
- `value & mask == 0` (well-formedness invariant)
- Known-1 bits: `value` (or `value & ~mask`, equivalent when well-formed)
- Unknown bits: `mask`
- Minimum concrete value: `value`
- Maximum concrete value: `value | mask`

Signed bound from tnum (the sign bit can be 0 or 1 if unknown):
```c
/* Minimum signed value: set sign bit if unknown (worst-case negative) */
s64 smin_from_tnum = (s64)(value | (mask & (u64)S64_MIN));
/* Maximum signed value: clear sign bit if unknown (worst-case positive) */
s64 smax_from_tnum = (s64)(value | (mask & (u64)S64_MAX));
```

The same pattern applies to the u32/s32 subregister using `(u32)value` and `(u32)mask`.

## Pitfalls

| Pitfall | Fix |
|---|---|
| Missing struct invariants | Add every field relationship as `__CPROVER_assume` in `valid_*` helpers |
| `nondet_*` warnings | Declare them as `extern` or just ignore — CBMC treats any `nondet_*` as a built-in stub |
| `--no-*` flags not recognized | Check CBMC version; flags differ between 5.x and 6.x |
| Loop unwind needed | Add `__CPROVER_unwind(N)` or pass `--unwind N` on the command line |
| All assertions PASS on a trivially true predicate | Check that your assumes are not too tight (verify with a "must-fail" sanity check) |
| Counter-example looks physically impossible | Missing invariant in `valid_*`; strengthen and re-run |

## Example: Full Investigation Template

```c
/* Step 1: Concrete proof — hard-code a known bad state, check properties */
void concrete_proof(void) {
    struct State s = { .field = KNOWN_BAD_VALUE };
    int result = function_under_test(&s);
    __CPROVER_assert(result == EXPECTED,
        "concrete: known input gives expected output");
}

/* Step 2: Symbolic proof — all states satisfying invariants */
void symbolic_proof(void) {
    struct State s;
    /* fill with nondet */
    s.field = nondet_ulong();
    __CPROVER_assume(valid_state(&s));

    int result = function_under_test(&s);
    __CPROVER_assert(result >= 0, "output is non-negative");
}

/* Step 3: Harness quality check */
void harness_nontrivial_check(void) {
    struct State s;
    s.field = nondet_ulong();
    __CPROVER_assume(valid_state(&s));
    /* Must FAIL — proves harness is non-vacuous */
    __CPROVER_assert(s.field == 0,
        "EXPECT FAILURE: not all states have field==0");
}

void main(void) {
    concrete_proof();
    symbolic_proof();
    harness_nontrivial_check();
}
```

Run with:
```bash
cbmc --compact-trace harness.c 2>&1 | tee trace.txt
grep "assertion\|PASS\|FAIL\|SUCCESS\|FAILURE" trace.txt
```
