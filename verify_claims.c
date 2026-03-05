/* verify_claims.c
 *
 * Concrete CBMC verification of the specific claims made in INVESTIGATION.md.
 *
 * The counter-example initial state is hard-coded (no nondet). CBMC runs
 * this as a purely concrete execution and checks every __CPROVER_assert.
 * Because there is no nondet, any assertion failure is a definitive error
 * in the report.
 *
 * Run with:
 *   cbmc --no-pointer-check --no-undefined-shift-check \
 *        --no-signed-overflow-check verify_claims.c
 */

#include <stdint.h>
#include <limits.h>
#include <stdbool.h>
#include <assert.h>

typedef uint64_t u64;
typedef int64_t  s64;
typedef uint32_t u32;
typedef int32_t  s32;
typedef uint8_t  u8;

#define S32_MIN  INT32_MIN
#define S32_MAX  INT32_MAX
#define S64_MIN  INT64_MIN
#define S64_MAX  INT64_MAX
#define U64_MAX  UINT64_MAX
#define U32_MAX  UINT32_MAX

#define min_t(type,x,y) (((type)(x))<((type)(y))?((type)(x)):((type)(y)))
#define max_t(type,x,y) (((type)(x))>((type)(y))?((type)(x)):((type)(y)))

/* ---- tnum / bpf_reg_state (identical to original) ---- */
struct tnum { u64 value; u64 mask; };
#define TNUM(_v,_m) (struct tnum){.value=(_v),.mask=(_m)}

struct bpf_reg_state {
    struct tnum var_off;
    s64 smin_value, smax_value;
    u64 umin_value, umax_value;
    s32 s32_min_value, s32_max_value;
    u32 u32_min_value, u32_max_value;
};

/* ---- helpers (verbatim from original) ---- */
#define BITS_PER_LONG 64
static __always_inline unsigned int __fls(unsigned long word)
{
    unsigned int num = BITS_PER_LONG - 1;
    if (!(word & (~0ul << 32))) { num -= 32; word <<= 32; }
    if (!(word & (~0ul << (BITS_PER_LONG-16)))) { num -= 16; word <<= 16; }
    if (!(word & (~0ul << (BITS_PER_LONG-8))))  { num -= 8;  word <<= 8;  }
    if (!(word & (~0ul << (BITS_PER_LONG-4))))  { num -= 4;  word <<= 4;  }
    if (!(word & (~0ul << (BITS_PER_LONG-2))))  { num -= 2;  word <<= 2;  }
    if (!(word & (~0ul << (BITS_PER_LONG-1))))  num -= 1;
    return num;
}
static __always_inline int fls64(u64 x) { return x ? __fls(x)+1 : 0; }

struct tnum tnum_const(u64 v) { return TNUM(v,0); }
struct tnum tnum_range(u64 min, u64 max) {
    u64 chi = min ^ max, delta;
    u8 bits = fls64(chi);
    if (bits > 63) return TNUM(0, U64_MAX);
    delta = (1ULL << bits) - 1;
    return TNUM(min & ~delta, delta);
}
struct tnum tnum_intersect(struct tnum a, struct tnum b) {
    u64 v = a.value | b.value, mu = a.mask & b.mask;
    return TNUM(v & ~mu, mu);
}
struct tnum tnum_or(struct tnum a, struct tnum b) {
    u64 v = a.value | b.value, mu = a.mask | b.mask;
    return TNUM(v, mu & ~v);
}
struct tnum tnum_cast(struct tnum a, u8 size) {
    a.value &= (1ULL<<(size*8))-1; a.mask &= (1ULL<<(size*8))-1; return a;
}
struct tnum tnum_subreg(struct tnum a) { return tnum_cast(a,4); }
struct tnum tnum_rshift(struct tnum a, u8 s){ return TNUM(a.value>>s, a.mask>>s); }
struct tnum tnum_lshift(struct tnum a, u8 s){ return TNUM(a.value<<s, a.mask<<s); }
struct tnum tnum_clear_subreg(struct tnum a){ return tnum_lshift(tnum_rshift(a,32),32); }

static void ___mark_reg_known(struct bpf_reg_state *reg, u64 imm) {
    reg->var_off = tnum_const(imm);
    reg->smin_value = reg->smax_value = (s64)imm;
    reg->umin_value = reg->umax_value = imm;
    reg->s32_min_value = reg->s32_max_value = (s32)imm;
    reg->u32_min_value = reg->u32_max_value = (u32)imm;
}

u64 tnum_step(struct tnum t, u64 z) {
    u64 tmax, j, p, q, r, s, v, u, w, res; u8 k;
    tmax = t.value | t.mask;
    if (z >= tmax) return tmax;
    if (z < t.value) return t.value;
    j = t.value | (z & t.mask);
    if (j > z) {
        p = ~z & t.value & ~t.mask; k = fls64(p);
        q = U64_MAX << k; r = q & z; s = ~q & t.value; v = r | s; res = v;
    } else {
        p = z & ~t.value & ~t.mask; k = fls64(p);
        q = U64_MAX << k; r = q & t.mask & z; s = q & ~t.mask; v = r | s;
        u = v + (1ULL << k); w = (u & t.mask) | t.value; res = w;
    }
    return res;
}

static void __update_reg32_bounds(struct bpf_reg_state *reg) {
    struct tnum var32_off = tnum_subreg(reg->var_off);
    reg->s32_min_value = max_t(s32, reg->s32_min_value,
        var32_off.value | (var32_off.mask & S32_MIN));
    reg->s32_max_value = min_t(s32, reg->s32_max_value,
        var32_off.value | (var32_off.mask & S32_MAX));
    reg->u32_min_value = max_t(u32, reg->u32_min_value, (u32)var32_off.value);
    reg->u32_max_value = min_t(u32, reg->u32_max_value,
        (u32)(var32_off.value | var32_off.mask));
}

static void __update_reg64_bounds(struct bpf_reg_state *reg) {
    u64 tnum_next, tmax; bool umin_in_tnum;
    reg->smin_value = max_t(s64, reg->smin_value,
        reg->var_off.value | (reg->var_off.mask & S64_MIN));
    reg->smax_value = min_t(s64, reg->smax_value,
        reg->var_off.value | (reg->var_off.mask & S64_MAX));
    reg->umin_value = max_t(u64, reg->umin_value, reg->var_off.value);
    reg->umax_value = min_t(u64, reg->umax_value,
        reg->var_off.value | reg->var_off.mask);
    tnum_next = tnum_step(reg->var_off, reg->umin_value);
    umin_in_tnum = (reg->umin_value & ~reg->var_off.mask) == reg->var_off.value;
    tmax = reg->var_off.value | reg->var_off.mask;
    if (umin_in_tnum && tnum_next > reg->umax_value)
        ___mark_reg_known(reg, reg->umin_value);
    else if (!umin_in_tnum && tnum_next == tmax)
        ___mark_reg_known(reg, tmax);
    else if (!umin_in_tnum && tnum_next <= reg->umax_value &&
             tnum_step(reg->var_off, tnum_next) > reg->umax_value)
        ___mark_reg_known(reg, tnum_next);
}

static void __update_reg_bounds(struct bpf_reg_state *reg) {
    __update_reg32_bounds(reg); __update_reg64_bounds(reg);
}

/* ---- deduce_bounds variants (verbatim from original) ---- */
static void __reg32_deduce_bounds_old(struct bpf_reg_state *reg) {
    if ((reg->umin_value >> 32) == (reg->umax_value >> 32)) {
        reg->u32_min_value = max_t(u32,reg->u32_min_value,(u32)reg->umin_value);
        reg->u32_max_value = min_t(u32,reg->u32_max_value,(u32)reg->umax_value);
        if ((s32)reg->umin_value <= (s32)reg->umax_value) {
            reg->s32_min_value = max_t(s32,reg->s32_min_value,(s32)reg->umin_value);
            reg->s32_max_value = min_t(s32,reg->s32_max_value,(s32)reg->umax_value);
        }
    }
    if ((reg->smin_value >> 32) == (reg->smax_value >> 32)) {
        if ((u32)reg->smin_value <= (u32)reg->smax_value) {
            reg->u32_min_value = max_t(u32,reg->u32_min_value,(u32)reg->smin_value);
            reg->u32_max_value = min_t(u32,reg->u32_max_value,(u32)reg->smax_value);
        }
        if ((s32)reg->smin_value <= (s32)reg->smax_value) {
            reg->s32_min_value = max_t(s32,reg->s32_min_value,(s32)reg->smin_value);
            reg->s32_max_value = min_t(s32,reg->s32_max_value,(s32)reg->smax_value);
        }
    }
    if ((u32)(reg->umin_value>>32)+1==(u32)(reg->umax_value>>32) &&
        (s32)reg->umin_value < 0 && (s32)reg->umax_value >= 0) {
        reg->s32_min_value = max_t(s32,reg->s32_min_value,(s32)reg->umin_value);
        reg->s32_max_value = min_t(s32,reg->s32_max_value,(s32)reg->umax_value);
    }
    if ((u32)(reg->smin_value>>32)+1==(u32)(reg->smax_value>>32) &&
        (s32)reg->smin_value < 0 && (s32)reg->smax_value >= 0) {
        reg->s32_min_value = max_t(s32,reg->s32_min_value,(s32)reg->smin_value);
        reg->s32_max_value = min_t(s32,reg->s32_max_value,(s32)reg->smax_value);
    }
    if ((s32)reg->u32_min_value <= (s32)reg->u32_max_value) {
        reg->s32_min_value = max_t(s32,reg->s32_min_value,reg->u32_min_value);
        reg->s32_max_value = min_t(s32,reg->s32_max_value,reg->u32_max_value);
    }
    if ((u32)reg->s32_min_value <= (u32)reg->s32_max_value) {
        reg->u32_min_value = max_t(u32,reg->s32_min_value,reg->u32_min_value);
        reg->u32_max_value = min_t(u32,reg->s32_max_value,reg->u32_max_value);
    }
}

static void __reg32_deduce_bounds_new(struct bpf_reg_state *reg) {
    if ((s32)reg->u32_min_value <= (s32)reg->u32_max_value) {
        reg->s32_min_value = max_t(s32,reg->s32_min_value,reg->u32_min_value);
        reg->s32_max_value = min_t(s32,reg->s32_max_value,reg->u32_max_value);
    }
    if ((u32)reg->s32_min_value <= (u32)reg->s32_max_value) {
        reg->u32_min_value = max_t(u32,reg->s32_min_value,reg->u32_min_value);
        reg->u32_max_value = min_t(u32,reg->s32_max_value,reg->u32_max_value);
    }
}

static void __reg64_deduce_bounds(struct bpf_reg_state *reg) {
    if ((s64)reg->umin_value <= (s64)reg->umax_value) {
        reg->smin_value = max_t(s64,reg->smin_value,reg->umin_value);
        reg->smax_value = min_t(s64,reg->smax_value,reg->umax_value);
    }
    if ((u64)reg->smin_value <= (u64)reg->smax_value) {
        reg->umin_value = max_t(u64,reg->smin_value,reg->umin_value);
        reg->umax_value = min_t(u64,reg->smax_value,reg->umax_value);
    } else {
        if (reg->umax_value < (u64)reg->smin_value) {
            reg->smin_value = (s64)reg->umin_value;
            reg->umax_value = min_t(u64,reg->umax_value,reg->smax_value);
        } else if ((u64)reg->smax_value < reg->umin_value) {
            reg->smax_value = (s64)reg->umax_value;
            reg->umin_value = max_t(u64,reg->umin_value,reg->smin_value);
        }
    }
}

static void __reg_deduce_mixed_bounds_old(struct bpf_reg_state *reg) {
    u64 new_umin, new_umax; s64 new_smin, new_smax;
    new_umin = (reg->umin_value & ~0xffffffffULL) | reg->u32_min_value;
    new_umax = (reg->umax_value & ~0xffffffffULL) | reg->u32_max_value;
    reg->umin_value = max_t(u64,reg->umin_value,new_umin);
    reg->umax_value = min_t(u64,reg->umax_value,new_umax);
    new_smin = (reg->smin_value & ~0xffffffffULL) | reg->u32_min_value;
    new_smax = (reg->smax_value & ~0xffffffffULL) | reg->u32_max_value;
    reg->smin_value = max_t(s64,reg->smin_value,new_smin);
    reg->smax_value = min_t(s64,reg->smax_value,new_smax);
    if (reg->s32_min_value >= 0 && reg->smin_value >= S32_MIN &&
        reg->smax_value <= S32_MAX) {
        reg->smin_value = reg->s32_min_value;
        reg->smax_value = reg->s32_max_value;
        reg->umin_value = reg->s32_min_value;
        reg->umax_value = reg->s32_max_value;
        reg->var_off = tnum_intersect(reg->var_off,
                           tnum_range(reg->smin_value,reg->smax_value));
    }
}

static void __reg_deduce_mixed_bounds_new(struct bpf_reg_state *reg) {
    /* 64 → 32 deductions (moved from old __reg32_deduce_bounds) */
    if ((reg->umin_value >> 32) == (reg->umax_value >> 32)) {
        reg->u32_min_value = max_t(u32,reg->u32_min_value,(u32)reg->umin_value);
        reg->u32_max_value = min_t(u32,reg->u32_max_value,(u32)reg->umax_value);
        if ((s32)reg->umin_value <= (s32)reg->umax_value) {
            reg->s32_min_value = max_t(s32,reg->s32_min_value,(s32)reg->umin_value);
            reg->s32_max_value = min_t(s32,reg->s32_max_value,(s32)reg->umax_value);
        }
    }
    if ((reg->smin_value >> 32) == (reg->smax_value >> 32)) {
        if ((u32)reg->smin_value <= (u32)reg->smax_value) {
            reg->u32_min_value = max_t(u32,reg->u32_min_value,(u32)reg->smin_value);
            reg->u32_max_value = min_t(u32,reg->u32_max_value,(u32)reg->smax_value);
        }
        if ((s32)reg->smin_value <= (s32)reg->smax_value) {
            reg->s32_min_value = max_t(s32,reg->s32_min_value,(s32)reg->smin_value);
            reg->s32_max_value = min_t(s32,reg->s32_max_value,(s32)reg->smax_value);
        }
    }
    if ((u32)(reg->umin_value>>32)+1==(u32)(reg->umax_value>>32) &&
        (s32)reg->umin_value < 0 && (s32)reg->umax_value >= 0) {
        reg->s32_min_value = max_t(s32,reg->s32_min_value,(s32)reg->umin_value);
        reg->s32_max_value = min_t(s32,reg->s32_max_value,(s32)reg->umax_value);
    }
    if ((u32)(reg->smin_value>>32)+1==(u32)(reg->smax_value>>32) &&
        (s32)reg->smin_value < 0 && (s32)reg->smax_value >= 0) {
        reg->s32_min_value = max_t(s32,reg->s32_min_value,(s32)reg->smin_value);
        reg->s32_max_value = min_t(s32,reg->s32_max_value,(s32)reg->smax_value);
    }
    /* 32 → 64 tightening (same as old __reg_deduce_mixed_bounds) */
    u64 new_umin, new_umax; s64 new_smin, new_smax;
    new_umin = (reg->umin_value & ~0xffffffffULL) | reg->u32_min_value;
    new_umax = (reg->umax_value & ~0xffffffffULL) | reg->u32_max_value;
    reg->umin_value = max_t(u64,reg->umin_value,new_umin);
    reg->umax_value = min_t(u64,reg->umax_value,new_umax);
    new_smin = (reg->smin_value & ~0xffffffffULL) | reg->u32_min_value;
    new_smax = (reg->smax_value & ~0xffffffffULL) | reg->u32_max_value;
    reg->smin_value = max_t(s64,reg->smin_value,new_smin);
    reg->smax_value = min_t(s64,reg->smax_value,new_smax);
    if (reg->s32_min_value >= 0 && reg->smin_value >= S32_MIN &&
        reg->smax_value <= S32_MAX) {
        reg->smin_value = reg->s32_min_value;
        reg->smax_value = reg->s32_max_value;
        reg->umin_value = reg->s32_min_value;
        reg->umax_value = reg->s32_max_value;
        reg->var_off = tnum_intersect(reg->var_off,
                           tnum_range(reg->smin_value,reg->smax_value));
    }
}

static void __reg_deduce_bounds_old(struct bpf_reg_state *reg) {
    __reg32_deduce_bounds_old(reg);
    __reg64_deduce_bounds(reg);
    __reg_deduce_mixed_bounds_old(reg);
}
static void __reg_deduce_bounds_new(struct bpf_reg_state *reg) {
    __reg32_deduce_bounds_new(reg);
    __reg64_deduce_bounds(reg);
    __reg_deduce_mixed_bounds_new(reg);
}

static void __reg_bound_offset(struct bpf_reg_state *reg) {
    struct tnum var64_off = tnum_intersect(reg->var_off,
                               tnum_range(reg->umin_value, reg->umax_value));
    struct tnum var32_off = tnum_intersect(tnum_subreg(var64_off),
                               tnum_range(reg->u32_min_value, reg->u32_max_value));
    reg->var_off = tnum_or(tnum_clear_subreg(var64_off), var32_off);
}

static void reg_bounds_sync_old(struct bpf_reg_state *reg) {
    __update_reg_bounds(reg);
    __reg_deduce_bounds_old(reg);
    __reg_deduce_bounds_old(reg);
    __reg_deduce_bounds_old(reg);
    __reg_bound_offset(reg);
    __update_reg_bounds(reg);
}
static void reg_bounds_sync_new(struct bpf_reg_state *reg) {
    __update_reg_bounds(reg);
    __reg_deduce_bounds_new(reg);
    __reg_deduce_bounds_new(reg);
    __reg_bound_offset(reg);
    __update_reg_bounds(reg);
}

/* ================================================================
 * Concrete counter-example state from trace-compact.txt, assertion.1
 * ================================================================ */
#define CE_VAR_OFF_VALUE  1084246877UL    /* 0x40A0_4B5D */
#define CE_VAR_OFF_MASK   18446744070485517312UL /* 0xFFFF_FFFF_3FD5_2400 */
#define CE_SMIN           30L
#define CE_SMAX           1084245086L     /* 0x40A0_445E */
#define CE_UMIN           17UL
#define CE_UMAX           1218464862UL    /* 0x48A0_4C5E */
#define CE_S32MIN         7
#define CE_S32MAX         2146791261      /* 0x7FF5_6F5D */
#define CE_U32MIN         17U
#define CE_U32MAX         803694174U      /* 0x2FE7_665E */
#define CE_X              32UL

static struct bpf_reg_state make_initial_state(void) {
    struct bpf_reg_state r;
    r.var_off.value  = CE_VAR_OFF_VALUE;
    r.var_off.mask   = CE_VAR_OFF_MASK;
    r.smin_value     = CE_SMIN;
    r.smax_value     = CE_SMAX;
    r.umin_value     = CE_UMIN;
    r.umax_value     = CE_UMAX;
    r.s32_min_value  = CE_S32MIN;
    r.s32_max_value  = CE_S32MAX;
    r.u32_min_value  = CE_U32MIN;
    r.u32_max_value  = CE_U32MAX;
    return r;
}

/* ================================================================
 * CLAIM 1 — Harness flaw: val_in_reg accepts x=32 despite var_off
 *            requiring the register value to be ≥ 0x4020_4B5D.
 * ================================================================ */
static void claim1_harness_flaw(void) {
    /* known-to-be-1 bits (lower 32) = var_off.value & ~var_off.mask */
    u32 mask_lower32  = (u32)CE_VAR_OFF_MASK;          /* 0x3FD5_2400 */
    u32 value_lower32 = (u32)CE_VAR_OFF_VALUE;          /* 0x40A0_4B5D */
    u32 known_ones    = value_lower32 & ~mask_lower32;  /* 0x4020_4B5D */

    /* x=32 does not satisfy the tnum constraint */
    u32 x32 = (u32)CE_X; /* 32 = 0x20 */
    __CPROVER_assert((x32 & ~mask_lower32) != known_ones,
        "CLAIM 1a: x=32 violates var_off known-bit pattern (32 & ~mask != known_ones)");

    /* But val_in_reg would return TRUE (does not check var_off) */
    __CPROVER_assert(CE_UMIN  <= CE_X,        "CLAIM 1b: umin_value <= x");
    __CPROVER_assert(CE_X     <= CE_UMAX,     "CLAIM 1b: x <= umax_value");
    __CPROVER_assert(CE_SMIN  <= (s64)CE_X,   "CLAIM 1b: smin_value <= x");
    __CPROVER_assert((s64)CE_X <= CE_SMAX,    "CLAIM 1b: x <= smax_value");
    __CPROVER_assert(CE_U32MIN <= (u32)CE_X,  "CLAIM 1b: u32_min <= (u32)x");
    __CPROVER_assert((u32)CE_X <= CE_U32MAX,  "CLAIM 1b: (u32)x <= u32_max");
    __CPROVER_assert(CE_S32MIN <= (s32)CE_X,  "CLAIM 1b: s32_min <= (s32)x");
    __CPROVER_assert((s32)CE_X <= CE_S32MAX,  "CLAIM 1b: (s32)x <= s32_max");
    /* → all eight val_in_reg checks pass, yet the tnum check (1a) fails */
}

/* ================================================================
 * CLAIM 2 — After __update_reg_bounds the 32-bit range becomes
 *            inverted: u32_min (1 084 246 877) > u32_max (803 694 174).
 * ================================================================ */
static void claim2_inverted_u32_after_update(void) {
    struct bpf_reg_state r = make_initial_state();
    __update_reg_bounds(&r);

    __CPROVER_assert(r.u32_min_value == 1084246877U,
        "CLAIM 2a: u32_min after __update_reg_bounds == 1 084 246 877");
    __CPROVER_assert(r.u32_max_value == 803694174U,
        "CLAIM 2a: u32_max after __update_reg_bounds == 803 694 174");
    __CPROVER_assert(r.u32_min_value > r.u32_max_value,
        "CLAIM 2b: u32_min > u32_max (inverted range) after __update_reg_bounds");

    /* 64-bit bounds after update */
    __CPROVER_assert(r.umin_value == 1084246877UL,
        "CLAIM 2c: umin after __update_reg_bounds == 1 084 246 877");
    __CPROVER_assert(r.umax_value == 1218464862UL,
        "CLAIM 2c: umax after __update_reg_bounds == 1 218 464 862");
    __CPROVER_assert(r.smin_value == 30L,
        "CLAIM 2d: smin after __update_reg_bounds == 30");
    __CPROVER_assert(r.smax_value == 1084245086L,
        "CLAIM 2d: smax after __update_reg_bounds == 1 084 245 086");
}

/* ================================================================
 * CLAIM 3 — The pivotal s32_max difference.
 *
 *   OLD: __reg32_deduce_bounds_old sees smax=1 084 245 086 (pre-__reg64)
 *        and tightens s32_max to 1 084 245 086.
 *   NEW: __reg32_deduce_bounds_new + __reg64_deduce_bounds widen smax
 *        to 1 218 464 862 first; then __reg_deduce_mixed_bounds_new
 *        uses the wider value, leaving s32_max = 1 218 464 862.
 * ================================================================ */
static void claim3_pivot_s32max(void) {
    struct bpf_reg_state old_r = make_initial_state();
    struct bpf_reg_state new_r = make_initial_state();

    /* Run __update_reg_bounds on both (identical step) */
    __update_reg_bounds(&old_r);
    __update_reg_bounds(&new_r);

    /* --- Old path: first sub-step is __reg32_deduce_bounds_old --- */
    __reg32_deduce_bounds_old(&old_r);
    __CPROVER_assert(old_r.s32_max_value == 1084245086,
        "CLAIM 3a: old path — after __reg32_deduce_bounds_old, "
        "s32_max == 1 084 245 086 (tightened from original smax)");

    /* --- New path: first sub-step is __reg32_deduce_bounds_new --- */
    __reg32_deduce_bounds_new(&new_r);
    __CPROVER_assert(new_r.s32_max_value == 2146791261,
        "CLAIM 3b: new path — after __reg32_deduce_bounds_new, "
        "s32_max unchanged == 2 146 791 261 (no 64→32 deduction yet)");

    /* Then __reg64_deduce_bounds on new path widens smax_value */
    __reg64_deduce_bounds(&new_r);
    __CPROVER_assert(new_r.smax_value == 1218464862L,
        "CLAIM 3c: new path — after __reg64_deduce_bounds, "
        "smax_value widened to 1 218 464 862");

    /* Then __reg_deduce_mixed_bounds_new uses the wider smax */
    __reg_deduce_mixed_bounds_new(&new_r);
    __CPROVER_assert(new_r.s32_max_value == 1218464862,
        "CLAIM 3d: new path — after __reg_deduce_mixed_bounds_new, "
        "s32_max == 1 218 464 862 (derived from wider smax)");

    /* Compare: old has tight s32_max, new has wider s32_max */
    __CPROVER_assert(old_r.s32_max_value < new_r.s32_max_value,
        "CLAIM 3e: old s32_max (1 084 245 086) < new s32_max (1 218 464 862)");
}

/* ================================================================
 * CLAIM 4 — The special sign-extend case in __reg_deduce_mixed_bounds
 *            fires in both paths and intersects var_off with:
 *
 *   OLD: tnum_range(1 084 246 877, 1 084 245 086) → mask = 0x0FFF
 *        intersect with original mask → var_off.mask = 0x0400
 *   NEW: tnum_range(1 084 246 877, 1 218 464 862) → mask = 0x0FFF_FFFF
 *        intersect with original mask → var_off.mask = 0x0FD5_2400
 * ================================================================ */
static void claim4_tnum_intersect_difference(void) {
    u64 orig_value = CE_VAR_OFF_VALUE; /* 0x40A0_4B5D */
    u64 orig_mask  = CE_VAR_OFF_MASK;  /* 0xFFFF_FFFF_3FD5_2400 */
    struct tnum original = TNUM(orig_value, orig_mask);

    /* Old path uses tight s32_max = 1 084 245 086 as the upper bound */
    struct tnum range_old = tnum_range(1084246877UL, 1084245086UL);
    __CPROVER_assert(range_old.mask == 4095UL,         /* 0x0FFF */
        "CLAIM 4a: tnum_range(old bounds).mask == 0x0FFF (12 free bits)");

    struct tnum intersect_old = tnum_intersect(original, range_old);
    __CPROVER_assert(intersect_old.mask == 1024UL,     /* 0x0400 */
        "CLAIM 4b: var_off.mask after old-path intersect == 0x0400 (1 unknown bit)");
    __CPROVER_assert(intersect_old.value == 1084246877UL,
        "CLAIM 4c: var_off.value after old-path intersect == 0x40A0_4B5D");

    /* New path uses wide s32_max = 1 218 464 862 as the upper bound */
    struct tnum range_new = tnum_range(1084246877UL, 1218464862UL);
    __CPROVER_assert(range_new.mask == 268435455UL,    /* 0x0FFF_FFFF */
        "CLAIM 4d: tnum_range(new bounds).mask == 0x0FFF_FFFF (28 free bits)");

    struct tnum intersect_new = tnum_intersect(original, range_new);
    __CPROVER_assert(intersect_new.mask == 265626624UL, /* 0x0FD5_2400 */
        "CLAIM 4e: var_off.mask after new-path intersect == 0x0FD5_2400 (many unknown bits)");
    __CPROVER_assert(intersect_new.value == 1075858269UL, /* 0x4020_4B5D */
        "CLAIM 4f: var_off.value after new-path intersect == 0x4020_4B5D");

    /* The masks differ by several orders of magnitude */
    __CPROVER_assert(intersect_old.mask < intersect_new.mask,
        "CLAIM 4g: old var_off.mask (0x0400) << new var_off.mask (0x0FD5_2400)");
}

/* ================================================================
 * CLAIM 5 — End-to-end: old produces a constant register
 *            (var_off.mask == 0), new does not.
 * ================================================================ */
static void claim5_end_to_end(void) {
    struct bpf_reg_state old_r = make_initial_state();
    struct bpf_reg_state new_r = make_initial_state();

    reg_bounds_sync_old(&old_r);
    reg_bounds_sync_new(&new_r);

    /* Old path collapses to a constant */
    __CPROVER_assert(old_r.var_off.mask == 0UL,
        "CLAIM 5a: old path — var_off.mask == 0 (constant register)");
    __CPROVER_assert(old_r.var_off.value == 1084246877UL,
        "CLAIM 5b: old path — var_off.value == 1 084 246 877");
    __CPROVER_assert(old_r.umin_value == old_r.umax_value,
        "CLAIM 5c: old path — umin == umax (constant)");
    __CPROVER_assert(old_r.umin_value == 1084246877UL,
        "CLAIM 5d: old path — umin == 1 084 246 877");

    /* New path does NOT collapse to a constant */
    __CPROVER_assert(new_r.var_off.mask != 0UL,
        "CLAIM 5e: new path — var_off.mask != 0 (NOT a constant register)");
    __CPROVER_assert(new_r.var_off.mask == 265626624UL, /* 0x0FD5_2400 */
        "CLAIM 5f: new path — var_off.mask == 0x0FD5_2400");
    __CPROVER_assert(new_r.var_off.value == 1075858269UL, /* 0x4020_4B5D */
        "CLAIM 5g: new path — var_off.value == 0x4020_4B5D");

    /* The two final states differ on every field */
    __CPROVER_assert(old_r.var_off.value != new_r.var_off.value,
        "CLAIM 5h: var_off.value differs between old and new");
    __CPROVER_assert(old_r.var_off.mask  != new_r.var_off.mask,
        "CLAIM 5i: var_off.mask differs between old and new");
    __CPROVER_assert(old_r.umax_value    != new_r.umax_value,
        "CLAIM 5j: umax_value differs (old=1 084 246 877, new=1 218 464 862)");
    __CPROVER_assert(old_r.smax_value    != new_r.smax_value,
        "CLAIM 5k: smax_value differs");
    __CPROVER_assert(old_r.s32_max_value != new_r.s32_max_value,
        "CLAIM 5l: s32_max_value differs");
}

/* ================================================================
 * CLAIM 6 — Old path is unsound: the constant it produces (1 084 246 877)
 *            excludes the witness x=32, which the initial bounds permitted.
 * ================================================================ */
static void claim6_old_path_unsound(void) {
    struct bpf_reg_state r = make_initial_state();
    reg_bounds_sync_old(&r);

    /* After old path, umin == umax == 1 084 246 877 */
    __CPROVER_assert(r.umin_value == 1084246877UL,
        "CLAIM 6a: old-path umin_value == 1 084 246 877");
    __CPROVER_assert(r.umax_value == 1084246877UL,
        "CLAIM 6b: old-path umax_value == 1 084 246 877");

    /* x=32 was within initial bounds (umin=17 ≤ 32 ≤ umax=1 218 464 862) */
    __CPROVER_assert(CE_UMIN  <= CE_X, "CLAIM 6c: x=32 was inside initial umin");
    __CPROVER_assert(CE_X <= CE_UMAX,  "CLAIM 6d: x=32 was inside initial umax");

    /* But x=32 is NOT within the old path's final range */
    __CPROVER_assert(!(r.umin_value <= CE_X && CE_X <= r.umax_value),
        "CLAIM 6e: x=32 is OUTSIDE old path's final range [umin,umax] = [1 084 246 877, 1 084 246 877]");
}

/* ================================================================
 * main: run all claims
 * ================================================================ */
void main(void) {
    claim1_harness_flaw();
    claim2_inverted_u32_after_update();
    claim3_pivot_s32max();
    claim4_tnum_intersect_difference();
    claim5_end_to_end();
    claim6_old_path_unsound();
}
