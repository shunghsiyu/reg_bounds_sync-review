/* verify_harness_flaw.c
 *
 * Symbolic CBMC proof that the original harness ALLOWS inputs where
 * var_off is inconsistent with the numeric bounds AND with the witness x.
 *
 * We use the SAME assumptions as the original harness (valid_bpf_reg_state +
 * val_in_reg + x <= 32), then show that these assumptions do NOT imply
 * var_off consistency.
 *
 * Run with:
 *   cbmc --unwind 1 verify_harness_flaw.c
 *
 * All three __CPROVER_assert in main() must FAIL (i.e. CBMC finds a
 * counter-example showing the harness is permissive), proving the flaw.
 */

#include <stdint.h>
#include <limits.h>
#include <stdbool.h>

typedef uint64_t u64;
typedef int64_t  s64;
typedef uint32_t u32;
typedef int32_t  s32;
typedef uint8_t  u8;

#define S32_MIN  INT32_MIN
#define S32_MAX  INT32_MAX
#define S64_MIN  INT64_MIN
#define S64_MAX  INT64_MAX
#define U32_MAX  UINT32_MAX

struct tnum { u64 value; u64 mask; };

struct bpf_reg_state {
    struct tnum var_off;
    s64 smin_value, smax_value;
    u64 umin_value, umax_value;
    s32 s32_min_value, s32_max_value;
    u32 u32_min_value, u32_max_value;
};

/* Verbatim from original harness */
static bool valid_bpf_reg_state(struct bpf_reg_state *reg) {
    bool ret = true;
    ret &= reg->umin_value     <= reg->umax_value;
    ret &= reg->smin_value     <= reg->smax_value;
    ret &= reg->u32_min_value  <= reg->u32_max_value;
    ret &= reg->s32_min_value  <= reg->s32_max_value;
    ret &= reg->umin_value     <= (u64)reg->u32_max_value;
    ret &= reg->umax_value     >= (u64)reg->u32_min_value;
    ret &= (s64)reg->smin_value <= (s64)reg->s32_max_value;
    ret &= (s64)reg->smax_value >= (s64)reg->s32_min_value;
    return ret;
}

static bool val_in_reg(struct bpf_reg_state *reg, u64 val) {
    bool ret = true;
    ret &= reg->umin_value     <= val;
    ret &= val                 <= reg->umax_value;
    ret &= reg->smin_value     <= (s64)val;
    ret &= (s64)val            <= reg->smax_value;
    ret &= reg->u32_min_value  <= (u32)val;
    ret &= (u32)val            <= reg->u32_max_value;
    ret &= reg->s32_min_value  <= (s32)val;
    ret &= (s32)val            <= reg->s32_max_value;
    return ret;
}

/* The MISSING check: does val satisfy the tnum pattern of var_off? */
static bool val_matches_tnum(struct tnum t, u64 val) {
    /* Known bits of tnum: value & ~mask
     * val is consistent iff (val & ~mask) == (t.value & ~mask) */
    return (val & ~t.mask) == (t.value & ~t.mask);
}

/* ================================================================
 * HARNESS FLAW PROOF 1
 *
 * Show: there EXISTS a symbolic state + witness where
 *   valid_bpf_reg_state(reg) AND val_in_reg(reg, x) AND x <= 32
 * BUT
 *   NOT val_matches_tnum(reg->var_off, x)
 *
 * We prove this by asserting the NEGATION and expecting CBMC to find
 * a counter-example (= a concrete state satisfying the flaw).
 * EXPECTED: FAILURE (CBMC finds the concrete counter-example state).
 * ================================================================ */
void harness_flaw_1_val_in_reg_misses_tnum(void) {
    struct bpf_reg_state reg;
    u64 x;

    /* Symbolic inputs (same as original harness) */
    reg.var_off.value  = nondet_ulong();
    reg.var_off.mask   = nondet_ulong();
    reg.smin_value     = nondet_long();
    reg.smax_value     = nondet_long();
    reg.umin_value     = nondet_ulong();
    reg.umax_value     = nondet_ulong();
    reg.s32_min_value  = nondet_int();
    reg.s32_max_value  = nondet_int();
    reg.u32_min_value  = nondet_uint();
    reg.u32_max_value  = nondet_uint();
    x = nondet_ulong();

    /* Original harness assumptions */
    __CPROVER_assume(valid_bpf_reg_state(&reg));
    __CPROVER_assume(x <= 32);
    __CPROVER_assume(val_in_reg(&reg, x));

    /* Assert that EVERY accepted witness DOES satisfy the tnum.
     * We EXPECT this to FAIL — CBMC will produce the concrete counter-example
     * showing that the harness accepts a (reg, x) where x violates var_off. */
    __CPROVER_assert(val_matches_tnum(reg.var_off, x),
        "HARNESS FLAW 1 (expect FAILURE): original harness allows x that "
        "violates var_off known-bit pattern");
}

/* ================================================================
 * HARNESS FLAW PROOF 2
 *
 * Show: there EXISTS a state where
 *   valid_bpf_reg_state(reg)
 * BUT
 *   reg.umin_value < (var_off.value & ~var_off.mask)
 *   i.e. the known-to-be-1 bits of var_off imply a minimum value
 *   that is HIGHER than umin_value.
 *
 * EXPECTED: FAILURE (CBMC finds state where numeric bounds don't
 * agree with var_off's implied minimum).
 * ================================================================ */
void harness_flaw_2_numeric_bounds_miss_tnum(void) {
    struct bpf_reg_state reg;

    reg.var_off.value  = nondet_ulong();
    reg.var_off.mask   = nondet_ulong();
    reg.smin_value     = nondet_long();
    reg.smax_value     = nondet_long();
    reg.umin_value     = nondet_ulong();
    reg.umax_value     = nondet_ulong();
    reg.s32_min_value  = nondet_int();
    reg.s32_max_value  = nondet_int();
    reg.u32_min_value  = nondet_uint();
    reg.u32_max_value  = nondet_uint();

    __CPROVER_assume(valid_bpf_reg_state(&reg));

    /* The minimum value any concrete register value can hold is the
     * known-to-be-1 bits of var_off (i.e. value & ~mask).
     * Assert that umin_value agrees with this lower bound.
     * We EXPECT this to FAIL. */
    u64 tnum_implied_min = reg.var_off.value & ~reg.var_off.mask;
    __CPROVER_assert(reg.umin_value >= tnum_implied_min,
        "HARNESS FLAW 2 (expect FAILURE): valid_bpf_reg_state allows "
        "umin_value < (var_off.value & ~var_off.mask)");
}

/* ================================================================
 * SANITY CHECK: with the FIXED additional constraint, the flaw 1
 * counter-example disappears.
 *
 * We add val_matches_tnum(reg.var_off, x) as an ASSUMPTION and then
 * assert that val_in_reg still holds — trivially true.  But more
 * importantly, we also assert the tnum consistency, which now passes
 * because it IS assumed.
 *
 * EXPECTED: SUCCESS (all properties verified when tnum is enforced).
 * ================================================================ */
void sanity_check_fixed_assumption(void) {
    struct bpf_reg_state reg;
    u64 x;

    reg.var_off.value  = nondet_ulong();
    reg.var_off.mask   = nondet_ulong();
    reg.smin_value     = nondet_long();
    reg.smax_value     = nondet_long();
    reg.umin_value     = nondet_ulong();
    reg.umax_value     = nondet_ulong();
    reg.s32_min_value  = nondet_int();
    reg.s32_max_value  = nondet_int();
    reg.u32_min_value  = nondet_uint();
    reg.u32_max_value  = nondet_uint();
    x = nondet_ulong();

    __CPROVER_assume(valid_bpf_reg_state(&reg));
    __CPROVER_assume(x <= 32);
    __CPROVER_assume(val_in_reg(&reg, x));
    /* ADDED assumption: x must satisfy the tnum pattern */
    __CPROVER_assume(val_matches_tnum(reg.var_off, x));

    /* Now the tnum check trivially holds */
    __CPROVER_assert(val_matches_tnum(reg.var_off, x),
        "SANITY (expect SUCCESS): after adding tnum assumption, x satisfies tnum");
}

void main(void) {
    harness_flaw_1_val_in_reg_misses_tnum();
    harness_flaw_2_numeric_bounds_miss_tnum();
    sanity_check_fixed_assumption();
}
