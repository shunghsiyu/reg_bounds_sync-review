/* bpf_reg.h
 *
 * Shared definitions for all reg_bounds_sync CBMC harnesses:
 *
 *   - Linux kernel type aliases
 *   - struct tnum / struct bpf_reg_state
 *   - tnum helper functions
 *   - __update_reg_bounds, all __reg_*_deduce_bounds variants
 *   - reg_bounds_sync_old / reg_bounds_sync_new
 *   - Harness helpers: val_matches_tnum, valid_bpf_reg_state, val_in_reg,
 *     nondet declarations, __bpf_reg_state_input
 *
 * Include this header once at the top of each harness .c file.
 * Do NOT include it in multiple translation units within the same binary
 * (all functions are defined, not just declared).
 */

#ifndef BPF_REG_H
#define BPF_REG_H

#include <stdint.h>
#include <limits.h>
#include <stdbool.h>
#include <assert.h>

/* ------------------------------------------------------------------ */
/* Types and limits                                                     */
/* ------------------------------------------------------------------ */

typedef uint64_t u64;
typedef int64_t  s64;
typedef uint32_t u32;
typedef int32_t  s32;
typedef uint8_t  u8;
typedef int8_t   s8;
typedef uint16_t u16;
typedef int16_t  s16;

#define S8_MIN   INT8_MIN
#define S8_MAX   INT8_MAX
#define S16_MIN  INT16_MIN
#define S16_MAX  INT16_MAX
#define S32_MIN  INT32_MIN
#define S32_MAX  INT32_MAX
#define U32_MAX  UINT32_MAX
#define S64_MIN  INT64_MIN
#define S64_MAX  INT64_MAX
#define U64_MAX  UINT64_MAX

#define min_t(type, x, y) (((type)(x)) < ((type)(y)) ? ((type)(x)) : ((type)(y)))
#define max_t(type, x, y) (((type)(x)) > ((type)(y)) ? ((type)(x)) : ((type)(y)))

/* ------------------------------------------------------------------ */
/* fls / fls64                                                          */
/* ------------------------------------------------------------------ */

#define BITS_PER_LONG 64

/**
 * generic___fls - find last (most-significant) set bit in a long word
 * @word: the word to search
 *
 * Undefined if no set bit exists, so code should check against 0 first.
 */
static __always_inline unsigned int __fls(unsigned long word)
{
	unsigned int num = BITS_PER_LONG - 1;

	if (!(word & (~0ul << 32))) {
		num -= 32;
		word <<= 32;
	}
	if (!(word & (~0ul << (BITS_PER_LONG-16)))) {
		num -= 16;
		word <<= 16;
	}
	if (!(word & (~0ul << (BITS_PER_LONG-8)))) {
		num -= 8;
		word <<= 8;
	}
	if (!(word & (~0ul << (BITS_PER_LONG-4)))) {
		num -= 4;
		word <<= 4;
	}
	if (!(word & (~0ul << (BITS_PER_LONG-2)))) {
		num -= 2;
		word <<= 2;
	}
	if (!(word & (~0ul << (BITS_PER_LONG-1))))
		num -= 1;
	return num;
}

static __always_inline int fls64(u64 x)
{
	if (x == 0)
		return 0;
	return __fls(x) + 1;
}

/* ------------------------------------------------------------------ */
/* tnum and bpf_reg_state                                               */
/* ------------------------------------------------------------------ */

struct tnum {
	u64 value;
	u64 mask;
};

/* Simplified bpf_reg_state: only the fields touched by reg_bounds_sync */
struct bpf_reg_state {
	struct tnum var_off;
	s64 smin_value;
	s64 smax_value;
	u64 umin_value;
	u64 umax_value;
	s32 s32_min_value;
	s32 s32_max_value;
	u32 u32_min_value;
	u32 u32_max_value;
};

#define TNUM(_v, _m)	(struct tnum){.value = (_v), .mask = (_m)}

/* A completely unknown value */
const struct tnum tnum_unknown = { .value = 0, .mask = -1 };

/* ------------------------------------------------------------------ */
/* tnum operations                                                      */
/* ------------------------------------------------------------------ */

struct tnum tnum_const(u64 value)
{
	return TNUM(value, 0);
}

struct tnum tnum_range(u64 min, u64 max)
{
	u64 chi = min ^ max, delta;
	u8 bits = fls64(chi);

	/* special case, needed because 1ULL << 64 is undefined */
	if (bits > 63)
		return tnum_unknown;
	delta = (1ULL << bits) - 1;
	return TNUM(min & ~delta, delta);
}

/* Note: if a and b disagree (one has a 'known 1' where the other has a
 * 'known 0') this returns a 'known 1' for that bit.
 */
struct tnum tnum_intersect(struct tnum a, struct tnum b)
{
	u64 v = a.value | b.value;
	u64 mu = a.mask & b.mask;
	return TNUM(v & ~mu, mu);
}

struct tnum tnum_or(struct tnum a, struct tnum b)
{
	u64 v = a.value | b.value;
	u64 mu = a.mask | b.mask;
	return TNUM(v, mu & ~v);
}

struct tnum tnum_cast(struct tnum a, u8 size)
{
	a.value &= (1ULL << (size * 8)) - 1;
	a.mask  &= (1ULL << (size * 8)) - 1;
	return a;
}

struct tnum tnum_subreg(struct tnum a)       { return tnum_cast(a, 4); }
struct tnum tnum_lshift(struct tnum a, u8 s) { return TNUM(a.value << s, a.mask << s); }
struct tnum tnum_rshift(struct tnum a, u8 s) { return TNUM(a.value >> s, a.mask >> s); }
struct tnum tnum_clear_subreg(struct tnum a) { return tnum_lshift(tnum_rshift(a, 32), 32); }

/* Given tnum t and a number z such that tmin <= z < tmax, returns the
 * smallest member of t larger than z.
 */
u64 tnum_step(struct tnum t, u64 z)
{
	u64 tmax = t.value | t.mask;
	u64 j, p, q, r, s, v, u, w, res;
	u8 k;

	if (z >= tmax)
		return tmax;
	if (z < t.value)
		return t.value;

	j = t.value | (z & t.mask);
	if (j > z) {
		p = ~z & t.value & ~t.mask;
		k = fls64(p);
		q = U64_MAX << k;
		r = q & z;
		s = ~q & t.value;
		v = r | s;
		res = v;
	} else {
		p = z & ~t.value & ~t.mask;
		k = fls64(p);
		q = U64_MAX << k;
		r = q & t.mask & z;
		s = q & ~t.mask;
		v = r | s;
		u = v + (1ULL << k);
		w = (u & t.mask) | t.value;
		res = w;
	}
	return res;
}

/* ------------------------------------------------------------------ */
/* Register bound helpers                                               */
/* ------------------------------------------------------------------ */

/* This helper doesn't clear reg->id */
static void ___mark_reg_known(struct bpf_reg_state *reg, u64 imm)
{
	reg->var_off       = tnum_const(imm);
	reg->smin_value    = reg->smax_value    = (s64)imm;
	reg->umin_value    = reg->umax_value    = imm;
	reg->s32_min_value = reg->s32_max_value = (s32)imm;
	reg->u32_min_value = reg->u32_max_value = (u32)imm;
}

static void __update_reg32_bounds(struct bpf_reg_state *reg)
{
	struct tnum var32_off = tnum_subreg(reg->var_off);

	/* min signed is max(sign bit) | min(other bits) */
	reg->s32_min_value = max_t(s32, reg->s32_min_value,
			var32_off.value | (var32_off.mask & S32_MIN));
	/* max signed is min(sign bit) | max(other bits) */
	reg->s32_max_value = min_t(s32, reg->s32_max_value,
			var32_off.value | (var32_off.mask & S32_MAX));
	reg->u32_min_value = max_t(u32, reg->u32_min_value, (u32)var32_off.value);
	reg->u32_max_value = min_t(u32, reg->u32_max_value,
			(u32)(var32_off.value | var32_off.mask));
}

static void __update_reg64_bounds(struct bpf_reg_state *reg)
{
	u64 tnum_next, tmax;
	bool umin_in_tnum;

	/* min signed is max(sign bit) | min(other bits) */
	reg->smin_value = max_t(s64, reg->smin_value,
			reg->var_off.value | (reg->var_off.mask & S64_MIN));
	/* max signed is min(sign bit) | max(other bits) */
	reg->smax_value = min_t(s64, reg->smax_value,
			reg->var_off.value | (reg->var_off.mask & S64_MAX));
	reg->umin_value = max_t(u64, reg->umin_value, reg->var_off.value);
	reg->umax_value = min_t(u64, reg->umax_value,
			reg->var_off.value | reg->var_off.mask);

	/* Check if u64 and tnum overlap in a single value */
	tnum_next    = tnum_step(reg->var_off, reg->umin_value);
	umin_in_tnum = (reg->umin_value & ~reg->var_off.mask) == reg->var_off.value;
	tmax         = reg->var_off.value | reg->var_off.mask;

	if (umin_in_tnum && tnum_next > reg->umax_value)
		___mark_reg_known(reg, reg->umin_value);
	else if (!umin_in_tnum && tnum_next == tmax)
		___mark_reg_known(reg, tmax);
	else if (!umin_in_tnum && tnum_next <= reg->umax_value &&
		 tnum_step(reg->var_off, tnum_next) > reg->umax_value)
		___mark_reg_known(reg, tnum_next);
}

static void __update_reg_bounds(struct bpf_reg_state *reg)
{
	__update_reg32_bounds(reg);
	__update_reg64_bounds(reg);
}

/* ------------------------------------------------------------------ */
/* Deduce-bounds variants (old and new)                                 */
/* ------------------------------------------------------------------ */

/* Uses signed min/max values to inform unsigned, and vice-versa */
static void __reg32_deduce_bounds_old(struct bpf_reg_state *reg)
{
	if ((reg->umin_value >> 32) == (reg->umax_value >> 32)) {
		reg->u32_min_value = max_t(u32, reg->u32_min_value, (u32)reg->umin_value);
		reg->u32_max_value = min_t(u32, reg->u32_max_value, (u32)reg->umax_value);
		if ((s32)reg->umin_value <= (s32)reg->umax_value) {
			reg->s32_min_value = max_t(s32, reg->s32_min_value, (s32)reg->umin_value);
			reg->s32_max_value = min_t(s32, reg->s32_max_value, (s32)reg->umax_value);
		}
	}
	if ((reg->smin_value >> 32) == (reg->smax_value >> 32)) {
		if ((u32)reg->smin_value <= (u32)reg->smax_value) {
			reg->u32_min_value = max_t(u32, reg->u32_min_value, (u32)reg->smin_value);
			reg->u32_max_value = min_t(u32, reg->u32_max_value, (u32)reg->smax_value);
		}
		if ((s32)reg->smin_value <= (s32)reg->smax_value) {
			reg->s32_min_value = max_t(s32, reg->s32_min_value, (s32)reg->smin_value);
			reg->s32_max_value = min_t(s32, reg->s32_max_value, (s32)reg->smax_value);
		}
	}
	if ((u32)(reg->umin_value >> 32) + 1 == (u32)(reg->umax_value >> 32) &&
	    (s32)reg->umin_value < 0 && (s32)reg->umax_value >= 0) {
		reg->s32_min_value = max_t(s32, reg->s32_min_value, (s32)reg->umin_value);
		reg->s32_max_value = min_t(s32, reg->s32_max_value, (s32)reg->umax_value);
	}
	if ((u32)(reg->smin_value >> 32) + 1 == (u32)(reg->smax_value >> 32) &&
	    (s32)reg->smin_value < 0 && (s32)reg->smax_value >= 0) {
		reg->s32_min_value = max_t(s32, reg->s32_min_value, (s32)reg->smin_value);
		reg->s32_max_value = min_t(s32, reg->s32_max_value, (s32)reg->smax_value);
	}
	if ((s32)reg->u32_min_value <= (s32)reg->u32_max_value) {
		reg->s32_min_value = max_t(s32, reg->s32_min_value, reg->u32_min_value);
		reg->s32_max_value = min_t(s32, reg->s32_max_value, reg->u32_max_value);
	}
	if ((u32)reg->s32_min_value <= (u32)reg->s32_max_value) {
		reg->u32_min_value = max_t(u32, reg->s32_min_value, reg->u32_min_value);
		reg->u32_max_value = min_t(u32, reg->s32_max_value, reg->u32_max_value);
	}
}

/* Uses signed min/max values to inform unsigned, and vice-versa */
static void __reg32_deduce_bounds_new(struct bpf_reg_state *reg)
{
	if ((s32)reg->u32_min_value <= (s32)reg->u32_max_value) {
		reg->s32_min_value = max_t(s32, reg->s32_min_value, reg->u32_min_value);
		reg->s32_max_value = min_t(s32, reg->s32_max_value, reg->u32_max_value);
	}
	if ((u32)reg->s32_min_value <= (u32)reg->s32_max_value) {
		reg->u32_min_value = max_t(u32, reg->s32_min_value, reg->u32_min_value);
		reg->u32_max_value = min_t(u32, reg->s32_max_value, reg->u32_max_value);
	}
}

static void __reg64_deduce_bounds(struct bpf_reg_state *reg)
{
	if ((s64)reg->umin_value <= (s64)reg->umax_value) {
		reg->smin_value = max_t(s64, reg->smin_value, reg->umin_value);
		reg->smax_value = min_t(s64, reg->smax_value, reg->umax_value);
	}
	if ((u64)reg->smin_value <= (u64)reg->smax_value) {
		reg->umin_value = max_t(u64, reg->smin_value, reg->umin_value);
		reg->umax_value = min_t(u64, reg->smax_value, reg->umax_value);
	} else {
		if (reg->umax_value < (u64)reg->smin_value) {
			reg->smin_value = (s64)reg->umin_value;
			reg->umax_value = min_t(u64, reg->umax_value, reg->smax_value);
		} else if ((u64)reg->smax_value < reg->umin_value) {
			reg->smax_value = (s64)reg->umax_value;
			reg->umin_value = max_t(u64, reg->umin_value, reg->smin_value);
		}
	}
}

static void __reg_deduce_mixed_bounds_old(struct bpf_reg_state *reg)
{
	u64 new_umin, new_umax;
	s64 new_smin, new_smax;

	/* u32 -> u64 tightening */
	new_umin = (reg->umin_value & ~0xffffffffULL) | reg->u32_min_value;
	new_umax = (reg->umax_value & ~0xffffffffULL) | reg->u32_max_value;
	reg->umin_value = max_t(u64, reg->umin_value, new_umin);
	reg->umax_value = min_t(u64, reg->umax_value, new_umax);
	/* u32 -> s64 tightening */
	new_smin = (reg->smin_value & ~0xffffffffULL) | reg->u32_min_value;
	new_smax = (reg->smax_value & ~0xffffffffULL) | reg->u32_max_value;
	reg->smin_value = max_t(s64, reg->smin_value, new_smin);
	reg->smax_value = min_t(s64, reg->smax_value, new_smax);

	/* Sign-extend special case: s32 is non-negative and fits in s32 range */
	if (reg->s32_min_value >= 0 && reg->smin_value >= S32_MIN &&
	    reg->smax_value <= S32_MAX) {
		reg->smin_value = reg->s32_min_value;
		reg->smax_value = reg->s32_max_value;
		reg->umin_value = reg->s32_min_value;
		reg->umax_value = reg->s32_max_value;
		reg->var_off = tnum_intersect(reg->var_off,
					      tnum_range(reg->smin_value,
							 reg->smax_value));
	}
}

static void __reg_deduce_mixed_bounds_new(struct bpf_reg_state *reg)
{
	u64 new_umin, new_umax;
	s64 new_smin, new_smax;

	/* 64 → 32 deductions (moved from old __reg32_deduce_bounds) */
	if ((reg->umin_value >> 32) == (reg->umax_value >> 32)) {
		reg->u32_min_value = max_t(u32, reg->u32_min_value, (u32)reg->umin_value);
		reg->u32_max_value = min_t(u32, reg->u32_max_value, (u32)reg->umax_value);
		if ((s32)reg->umin_value <= (s32)reg->umax_value) {
			reg->s32_min_value = max_t(s32, reg->s32_min_value, (s32)reg->umin_value);
			reg->s32_max_value = min_t(s32, reg->s32_max_value, (s32)reg->umax_value);
		}
	}
	if ((reg->smin_value >> 32) == (reg->smax_value >> 32)) {
		if ((u32)reg->smin_value <= (u32)reg->smax_value) {
			reg->u32_min_value = max_t(u32, reg->u32_min_value, (u32)reg->smin_value);
			reg->u32_max_value = min_t(u32, reg->u32_max_value, (u32)reg->smax_value);
		}
		if ((s32)reg->smin_value <= (s32)reg->smax_value) {
			reg->s32_min_value = max_t(s32, reg->s32_min_value, (s32)reg->smin_value);
			reg->s32_max_value = min_t(s32, reg->s32_max_value, (s32)reg->smax_value);
		}
	}
	if ((u32)(reg->umin_value >> 32) + 1 == (u32)(reg->umax_value >> 32) &&
	    (s32)reg->umin_value < 0 && (s32)reg->umax_value >= 0) {
		reg->s32_min_value = max_t(s32, reg->s32_min_value, (s32)reg->umin_value);
		reg->s32_max_value = min_t(s32, reg->s32_max_value, (s32)reg->umax_value);
	}
	if ((u32)(reg->smin_value >> 32) + 1 == (u32)(reg->smax_value >> 32) &&
	    (s32)reg->smin_value < 0 && (s32)reg->smax_value >= 0) {
		reg->s32_min_value = max_t(s32, reg->s32_min_value, (s32)reg->smin_value);
		reg->s32_max_value = min_t(s32, reg->s32_max_value, (s32)reg->smax_value);
	}

	/* 32 → 64 tightening (same as old __reg_deduce_mixed_bounds) */
	new_umin = (reg->umin_value & ~0xffffffffULL) | reg->u32_min_value;
	new_umax = (reg->umax_value & ~0xffffffffULL) | reg->u32_max_value;
	reg->umin_value = max_t(u64, reg->umin_value, new_umin);
	reg->umax_value = min_t(u64, reg->umax_value, new_umax);
	new_smin = (reg->smin_value & ~0xffffffffULL) | reg->u32_min_value;
	new_smax = (reg->smax_value & ~0xffffffffULL) | reg->u32_max_value;
	reg->smin_value = max_t(s64, reg->smin_value, new_smin);
	reg->smax_value = min_t(s64, reg->smax_value, new_smax);

	/* Sign-extend special case (same condition, but smax already widened by
	 * __reg64_deduce_bounds before this function is called) */
	if (reg->s32_min_value >= 0 && reg->smin_value >= S32_MIN &&
	    reg->smax_value <= S32_MAX) {
		reg->smin_value = reg->s32_min_value;
		reg->smax_value = reg->s32_max_value;
		reg->umin_value = reg->s32_min_value;
		reg->umax_value = reg->s32_max_value;
		reg->var_off = tnum_intersect(reg->var_off,
					      tnum_range(reg->smin_value,
							 reg->smax_value));
	}
}

static void __reg_deduce_bounds_old(struct bpf_reg_state *reg)
{
	__reg32_deduce_bounds_old(reg);
	__reg64_deduce_bounds(reg);
	__reg_deduce_mixed_bounds_old(reg);
}

static void __reg_deduce_bounds_new(struct bpf_reg_state *reg)
{
	__reg32_deduce_bounds_new(reg);
	__reg64_deduce_bounds(reg);
	__reg_deduce_mixed_bounds_new(reg);
}

/* Attempts to improve var_off based on unsigned min/max information */
static void __reg_bound_offset(struct bpf_reg_state *reg)
{
	struct tnum var64_off = tnum_intersect(reg->var_off,
					       tnum_range(reg->umin_value,
							  reg->umax_value));
	struct tnum var32_off = tnum_intersect(tnum_subreg(var64_off),
					       tnum_range(reg->u32_min_value,
							  reg->u32_max_value));
	reg->var_off = tnum_or(tnum_clear_subreg(var64_off), var32_off);
}

static void reg_bounds_sync_old(struct bpf_reg_state *reg)
{
	__update_reg_bounds(reg);
	__reg_deduce_bounds_old(reg);
	__reg_deduce_bounds_old(reg);
	__reg_deduce_bounds_old(reg);
	__reg_bound_offset(reg);
	__update_reg_bounds(reg);
}

static void reg_bounds_sync_new(struct bpf_reg_state *reg)
{
	__update_reg_bounds(reg);
	__reg_deduce_bounds_new(reg);
	__reg_deduce_bounds_new(reg);
	__reg_bound_offset(reg);
	__update_reg_bounds(reg);
}

/* ------------------------------------------------------------------ */
/* Harness helpers                                                      */
/* ------------------------------------------------------------------ */

/* Declare nondet stubs used by CBMC harnesses.
 * CBMC treats any nondet_* as a built-in returning a fully symbolic value.
 */
long long          nondet_long_long_input(void);
unsigned long long nondet_unsigned_long_long_input(void);
int                nondet_int_input(void);
unsigned int       nondet_unsigned_int_input(void);
unsigned long      nondet_ulong(void);
long               nondet_long(void);
unsigned int       nondet_uint(void);
int                nondet_int(void);

/* Returns a fully symbolic bpf_reg_state (var_off is also symbolic) */
static struct bpf_reg_state __bpf_reg_state_input(void)
{
	struct bpf_reg_state reg;

	reg.var_off.value  = nondet_unsigned_long_long_input();
	reg.var_off.mask   = nondet_unsigned_long_long_input();
	reg.smin_value     = nondet_long_long_input();
	reg.smax_value     = nondet_long_long_input();
	reg.umin_value     = nondet_unsigned_long_long_input();
	reg.umax_value     = nondet_unsigned_long_long_input();
	reg.s32_min_value  = nondet_int_input();
	reg.s32_max_value  = nondet_int_input();
	reg.u32_min_value  = nondet_unsigned_int_input();
	reg.u32_max_value  = nondet_unsigned_int_input();
	return reg;
}

/* Returns true iff val satisfies the tnum pattern:
 * the known bits of val must match the known bits of t.
 */
static bool val_matches_tnum(struct tnum t, u64 val)
{
	return (val & ~t.mask) == (t.value & ~t.mask);
}

/* Returns true iff reg is an internally consistent bpf_reg_state.
 * Checks all range invariants AND tnum consistency.
 */
static bool valid_bpf_reg_state(struct bpf_reg_state *reg)
{
	bool ret = true;

	/* Range ordering */
	ret &= reg->umin_value    <= reg->umax_value;
	ret &= reg->smin_value    <= reg->smax_value;
	ret &= reg->u32_min_value <= reg->u32_max_value;
	ret &= reg->s32_min_value <= reg->s32_max_value;

	/* 64-bit ↔ 32-bit cross-consistency */
	ret &= reg->umin_value    <= (u64)reg->u32_max_value;
	ret &= reg->umax_value    >= (u64)reg->u32_min_value;
	ret &= (s64)reg->smin_value <= (s64)reg->s32_max_value;
	ret &= (s64)reg->smax_value >= (s64)reg->s32_min_value;

	/* tnum well-formedness: no bit is simultaneously known and unknown */
	ret &= (reg->var_off.value & reg->var_off.mask) == 0;

	/* u64 bounds must be consistent with tnum:
	 *   minimum concrete value = var_off.value (known-1 bits)
	 *   maximum concrete value = var_off.value | var_off.mask
	 */
	ret &= reg->umin_value <= (reg->var_off.value | reg->var_off.mask);
	ret &= reg->umax_value <= (reg->var_off.value | reg->var_off.mask);
	ret &= reg->umin_value >= reg->var_off.value;

	/* s64 bounds: sign bit may be 0 or 1 in unknown positions */
	ret &= reg->smin_value >= (s64)(reg->var_off.value |
				   (reg->var_off.mask & (u64)S64_MIN));
	ret &= reg->smax_value <= (s64)(reg->var_off.value |
				   (reg->var_off.mask & (u64)S64_MAX));

	/* u32 subregister bounds consistent with low-32 bits of tnum */
	ret &= reg->u32_min_value >= (u32)reg->var_off.value;
	ret &= reg->u32_max_value <= (u32)(reg->var_off.value | reg->var_off.mask);

	/* s32 subregister bounds: same sign-bit logic within 32 bits */
	ret &= reg->s32_min_value >= (s32)((u32)reg->var_off.value |
				      ((u32)reg->var_off.mask & (u32)S32_MIN));
	ret &= reg->s32_max_value <= (s32)((u32)reg->var_off.value |
				      ((u32)reg->var_off.mask & (u32)S32_MAX));
	return ret;
}

/* Returns true iff val is within all numeric ranges of reg AND satisfies
 * the tnum pattern.
 */
static bool val_in_reg(struct bpf_reg_state *reg, u64 val)
{
	bool ret = true;

	ret &= reg->umin_value    <= val;
	ret &= val                <= reg->umax_value;
	ret &= reg->smin_value    <= (s64)val;
	ret &= (s64)val           <= reg->smax_value;
	ret &= reg->u32_min_value <= (u32)val;
	ret &= (u32)val           <= reg->u32_max_value;
	ret &= reg->s32_min_value <= (s32)val;
	ret &= (s32)val           <= reg->s32_max_value;
	/* val must satisfy the tnum pattern: known bits must match var_off */
	ret &= val_matches_tnum(reg->var_off, val);
	return ret;
}

#endif /* BPF_REG_H */
