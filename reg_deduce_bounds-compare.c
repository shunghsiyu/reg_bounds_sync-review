#include <stdint.h>
#include <limits.h>
#include <stdbool.h>
#include <assert.h>

// Define Linux kernel types
typedef uint64_t u64;
typedef int64_t s64;
typedef uint32_t u32;
typedef int32_t s32;
typedef uint8_t u8;
typedef int8_t s8;
typedef uint16_t u16;
typedef int16_t s16;

// Define limits
#define S8_MIN  INT8_MIN
#define S8_MAX  INT8_MAX
#define S16_MIN INT16_MIN
#define S16_MAX INT16_MAX
#define S32_MIN INT32_MIN
#define S32_MAX INT32_MAX
#define U32_MAX UINT32_MAX
#define S64_MIN INT64_MIN
#define S64_MAX INT64_MAX
#define U64_MAX UINT64_MAX

/* Crude approximation of min_t() and max_t() */
#define min_t(type, x, y) (((type) (x)) < ((type) (y)) ? ((type) (x)) : ((type) (y)))
#define max_t(type, x, y) (((type) (x)) > ((type) (y)) ? ((type) (x)) : ((type) (y)))

/* --- fls64 --- */

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

/* ------------- */

struct tnum {
	u64 value;
	u64 mask;
};

// Simplified version of bpf_reg_state with only field needed by
// coerce_reg_to_size_sx
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

#define TNUM(_v, _m)	(struct tnum){.value = _v, .mask = _m}
/* A completely unknown value */
const struct tnum tnum_unknown = { .value = 0, .mask = -1 };

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
	/* e.g. if chi = 4, bits = 3, delta = (1<<3) - 1 = 7.
	 * if chi = 0, bits = 0, delta = (1<<0) - 1 = 0, so we return
	 *  constant min (since min == max).
	 */
	delta = (1ULL << bits) - 1;
	return TNUM(min & ~delta, delta);
}

/* Note that if a and b disagree - i.e. one has a 'known 1' where the other has
 * a 'known 0' - this will return a 'known 1' for that bit.
 */
struct tnum tnum_intersect(struct tnum a, struct tnum b)
{
	u64 v, mu;

	v = a.value | b.value;
	mu = a.mask & b.mask;
	return TNUM(v & ~mu, mu);
}


struct tnum tnum_or(struct tnum a, struct tnum b)
{
	u64 v, mu;

	v = a.value | b.value;
	mu = a.mask | b.mask;
	return TNUM(v, mu & ~v);
}

struct tnum tnum_cast(struct tnum a, u8 size)
{
	a.value &= (1ULL << (size * 8)) - 1;
	a.mask &= (1ULL << (size * 8)) - 1;
	return a;
}

struct tnum tnum_subreg(struct tnum a)
{
	return tnum_cast(a, 4);
}

struct tnum tnum_lshift(struct tnum a, u8 shift)
{
	return TNUM(a.value << shift, a.mask << shift);
}

struct tnum tnum_rshift(struct tnum a, u8 shift)
{
	return TNUM(a.value >> shift, a.mask >> shift);
}


struct tnum tnum_clear_subreg(struct tnum a)
{
	return tnum_lshift(tnum_rshift(a, 32), 32);
}

/* Given tnum t, and a number z such that tmin <= z < tmax, where tmin
 * is the smallest member of the t (= t.value) and tmax is the largest
 * member of t (= t.value | t.mask), returns the smallest member of t
 * larger than z.
 *
 * For example,
 * t      = x11100x0
 * z      = 11110001 (241)
 * result = 11110010 (242)
 *
 * Note: if this function is called with z >= tmax, it just returns
 * early with tmax; if this function is called with z < tmin, the
 * algorithm already returns tmin.
 */
u64 tnum_step(struct tnum t, u64 z)
{
	u64 tmax, j, p, q, r, s, v, u, w, res;
	u8 k;

	tmax = t.value | t.mask;

	/* if z >= largest member of t, return largest member of t */
	if (z >= tmax)
		return tmax;

	/* if z < smallest member of t, return smallest member of t */
	if (z < t.value)
		return t.value;

	/* keep t's known bits, and match all unknown bits to z */
	j = t.value | (z & t.mask);

	if (j > z) {
		p = ~z & t.value & ~t.mask;
		k = fls64(p); /* k is the most-significant 0-to-1 flip */
		q = U64_MAX << k;
		r = q & z; /* positions > k matched to z */
		s = ~q & t.value; /* positions <= k matched to t.value */
		v = r | s;
		res = v;
	} else {
		p = z & ~t.value & ~t.mask;
		k = fls64(p); /* k is the most-significant 1-to-0 flip */
		q = U64_MAX << k;
		r = q & t.mask & z; /* unknown positions > k, matched to z */
		s = q & ~t.mask; /* known positions > k, set to 1 */
		v = r | s;
		/* add 1 to unknown positions > k to make value greater than z */
		u = v + (1ULL << k);
		/* extract bits in unknown positions > k from u, rest from t.value */
		w = (u & t.mask) | t.value;
		res = w;
	}
	return res;
}

/* This helper doesn't clear reg->id */
static void ___mark_reg_known(struct bpf_reg_state *reg, u64 imm)
{
	reg->var_off = tnum_const(imm);
	reg->smin_value = (s64)imm;
	reg->smax_value = (s64)imm;
	reg->umin_value = imm;
	reg->umax_value = imm;

	reg->s32_min_value = (s32)imm;
	reg->s32_max_value = (s32)imm;
	reg->u32_min_value = (u32)imm;
	reg->u32_max_value = (u32)imm;
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
	tnum_next = tnum_step(reg->var_off, reg->umin_value);
	umin_in_tnum = (reg->umin_value & ~reg->var_off.mask) == reg->var_off.value;
	tmax = reg->var_off.value | reg->var_off.mask;
	if (umin_in_tnum && tnum_next > reg->umax_value) {
		/* The u64 range and the tnum only overlap in umin.
		 * u64:  ---[xxxxxx]-----
		 * tnum: --xx----------x-
		 */
		___mark_reg_known(reg, reg->umin_value);
	} else if (!umin_in_tnum && tnum_next == tmax) {
		/* The u64 range and the tnum only overlap in the maximum value
		 * represented by the tnum, called tmax.
		 * u64:  ---[xxxxxx]-----
		 * tnum: xx-----x--------
		 */
		___mark_reg_known(reg, tmax);
	} else if (!umin_in_tnum && tnum_next <= reg->umax_value &&
		   tnum_step(reg->var_off, tnum_next) > reg->umax_value) {
		/* The u64 range and the tnum only overlap in between umin
		 * (excluded) and umax.
		 * u64:  ---[xxxxxx]-----
		 * tnum: xx----x-------x-
		 */
		___mark_reg_known(reg, tnum_next);
	}
}

static void __update_reg_bounds(struct bpf_reg_state *reg)
{
	__update_reg32_bounds(reg);
	__update_reg64_bounds(reg);
}

/* Uses signed min/max values to inform unsigned, and vice-versa */
static void __reg32_deduce_bounds_old(struct bpf_reg_state *reg)
{
	/* If upper 32 bits of u64/s64 range don't change, we can use lower 32
	 * bits to improve our u32/s32 boundaries.
	 *
	 * E.g., the case where we have upper 32 bits as zero ([10, 20] in
	 * u64) is pretty trivial, it's obvious that in u32 we'll also have
	 * [10, 20] range. But this property holds for any 64-bit range as
	 * long as upper 32 bits in that entire range of values stay the same.
	 *
	 * E.g., u64 range [0x10000000A, 0x10000000F] ([4294967306, 4294967311]
	 * in decimal) has the same upper 32 bits throughout all the values in
	 * that range. As such, lower 32 bits form a valid [0xA, 0xF] ([10, 15])
	 * range.
	 *
	 * Note also, that [0xA, 0xF] is a valid range both in u32 and in s32,
	 * following the rules outlined below about u64/s64 correspondence
	 * (which equally applies to u32 vs s32 correspondence). In general it
	 * depends on actual hexadecimal values of 32-bit range. They can form
	 * only valid u32, or only valid s32 ranges in some cases.
	 *
	 * So we use all these insights to derive bounds for subregisters here.
	 */
	if ((reg->umin_value >> 32) == (reg->umax_value >> 32)) {
		/* u64 to u32 casting preserves validity of low 32 bits as
		 * a range, if upper 32 bits are the same
		 */
		reg->u32_min_value = max_t(u32, reg->u32_min_value, (u32)reg->umin_value);
		reg->u32_max_value = min_t(u32, reg->u32_max_value, (u32)reg->umax_value);

		if ((s32)reg->umin_value <= (s32)reg->umax_value) {
			reg->s32_min_value = max_t(s32, reg->s32_min_value, (s32)reg->umin_value);
			reg->s32_max_value = min_t(s32, reg->s32_max_value, (s32)reg->umax_value);
		}
	}
	if ((reg->smin_value >> 32) == (reg->smax_value >> 32)) {
		/* low 32 bits should form a proper u32 range */
		if ((u32)reg->smin_value <= (u32)reg->smax_value) {
			reg->u32_min_value = max_t(u32, reg->u32_min_value, (u32)reg->smin_value);
			reg->u32_max_value = min_t(u32, reg->u32_max_value, (u32)reg->smax_value);
		}
		/* low 32 bits should form a proper s32 range */
		if ((s32)reg->smin_value <= (s32)reg->smax_value) {
			reg->s32_min_value = max_t(s32, reg->s32_min_value, (s32)reg->smin_value);
			reg->s32_max_value = min_t(s32, reg->s32_max_value, (s32)reg->smax_value);
		}
	}
	/* Special case where upper bits form a small sequence of two
	 * sequential numbers (in 32-bit unsigned space, so 0xffffffff to
	 * 0x00000000 is also valid), while lower bits form a proper s32 range
	 * going from negative numbers to positive numbers. E.g., let's say we
	 * have s64 range [-1, 1] ([0xffffffffffffffff, 0x0000000000000001]).
	 * Possible s64 values are {-1, 0, 1} ({0xffffffffffffffff,
	 * 0x0000000000000000, 0x00000000000001}). Ignoring upper 32 bits,
	 * we still get a valid s32 range [-1, 1] ([0xffffffff, 0x00000001]).
	 * Note that it doesn't have to be 0xffffffff going to 0x00000000 in
	 * upper 32 bits. As a random example, s64 range
	 * [0xfffffff0fffffff0; 0xfffffff100000010], forms a valid s32 range
	 * [-16, 16] ([0xfffffff0; 0x00000010]) in its 32 bit subregister.
	 */
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
	/* if u32 range forms a valid s32 range (due to matching sign bit),
	 * try to learn from that
	 */
	if ((s32)reg->u32_min_value <= (s32)reg->u32_max_value) {
		reg->s32_min_value = max_t(s32, reg->s32_min_value, reg->u32_min_value);
		reg->s32_max_value = min_t(s32, reg->s32_max_value, reg->u32_max_value);
	}
	/* If we cannot cross the sign boundary, then signed and unsigned bounds
	 * are the same, so combine.  This works even in the negative case, e.g.
	 * -3 s<= x s<= -1 implies 0xf...fd u<= x u<= 0xf...ff.
	 */
	if ((u32)reg->s32_min_value <= (u32)reg->s32_max_value) {
		reg->u32_min_value = max_t(u32, reg->s32_min_value, reg->u32_min_value);
		reg->u32_max_value = min_t(u32, reg->s32_max_value, reg->u32_max_value);
	}
}

/* Uses signed min/max values to inform unsigned, and vice-versa */
static void __reg32_deduce_bounds_new(struct bpf_reg_state *reg)
{
	/* if u32 range forms a valid s32 range (due to matching sign bit),
	 * try to learn from that
	 */
	if ((s32)reg->u32_min_value <= (s32)reg->u32_max_value) {
		reg->s32_min_value = max_t(s32, reg->s32_min_value, reg->u32_min_value);
		reg->s32_max_value = min_t(s32, reg->s32_max_value, reg->u32_max_value);
	}
	/* If we cannot cross the sign boundary, then signed and unsigned bounds
	 * are the same, so combine.  This works even in the negative case, e.g.
	 * -3 s<= x s<= -1 implies 0xf...fd u<= x u<= 0xf...ff.
	 */
	if ((u32)reg->s32_min_value <= (u32)reg->s32_max_value) {
		reg->u32_min_value = max_t(u32, reg->s32_min_value, reg->u32_min_value);
		reg->u32_max_value = min_t(u32, reg->s32_max_value, reg->u32_max_value);
	}
}

static void __reg64_deduce_bounds(struct bpf_reg_state *reg)
{
	/* If u64 range forms a valid s64 range (due to matching sign bit),
	 * try to learn from that. Let's do a bit of ASCII art to see when
	 * this is happening. Let's take u64 range first:
	 *
	 * 0             0x7fffffffffffffff 0x8000000000000000        U64_MAX
	 * |-------------------------------|--------------------------------|
	 *
	 * Valid u64 range is formed when umin and umax are anywhere in the
	 * range [0, U64_MAX], and umin <= umax. u64 case is simple and
	 * straightforward. Let's see how s64 range maps onto the same range
	 * of values, annotated below the line for comparison:
	 *
	 * 0             0x7fffffffffffffff 0x8000000000000000        U64_MAX
	 * |-------------------------------|--------------------------------|
	 * 0                        S64_MAX S64_MIN                        -1
	 *
	 * So s64 values basically start in the middle and they are logically
	 * contiguous to the right of it, wrapping around from -1 to 0, and
	 * then finishing as S64_MAX (0x7fffffffffffffff) right before
	 * S64_MIN. We can try drawing the continuity of u64 vs s64 values
	 * more visually as mapped to sign-agnostic range of hex values.
	 *
	 *  u64 start                                               u64 end
	 *  _______________________________________________________________
	 * /                                                               \
	 * 0             0x7fffffffffffffff 0x8000000000000000        U64_MAX
	 * |-------------------------------|--------------------------------|
	 * 0                        S64_MAX S64_MIN                        -1
	 *                                / \
	 * >------------------------------   ------------------------------->
	 * s64 continues...        s64 end   s64 start          s64 "midpoint"
	 *
	 * What this means is that, in general, we can't always derive
	 * something new about u64 from any random s64 range, and vice versa.
	 *
	 * But we can do that in two particular cases. One is when entire
	 * u64/s64 range is *entirely* contained within left half of the above
	 * diagram or when it is *entirely* contained in the right half. I.e.:
	 *
	 * |-------------------------------|--------------------------------|
	 *     ^                   ^            ^                 ^
	 *     A                   B            C                 D
	 *
	 * [A, B] and [C, D] are contained entirely in their respective halves
	 * and form valid contiguous ranges as both u64 and s64 values. [A, B]
	 * will be non-negative both as u64 and s64 (and in fact it will be
	 * identical ranges no matter the signedness). [C, D] treated as s64
	 * will be a range of negative values, while in u64 it will be
	 * non-negative range of values larger than 0x8000000000000000.
	 *
	 * Now, any other range here can't be represented in both u64 and s64
	 * simultaneously. E.g., [A, C], [A, D], [B, C], [B, D] are valid
	 * contiguous u64 ranges, but they are discontinuous in s64. [B, C]
	 * in s64 would be properly presented as [S64_MIN, C] and [B, S64_MAX],
	 * for example. Similarly, valid s64 range [D, A] (going from negative
	 * to positive values), would be two separate [D, U64_MAX] and [0, A]
	 * ranges as u64. Currently reg_state can't represent two segments per
	 * numeric domain, so in such situations we can only derive maximal
	 * possible range ([0, U64_MAX] for u64, and [S64_MIN, S64_MAX] for s64).
	 *
	 * So we use these facts to derive umin/umax from smin/smax and vice
	 * versa only if they stay within the same "half". This is equivalent
	 * to checking sign bit: lower half will have sign bit as zero, upper
	 * half have sign bit 1. Below in code we simplify this by just
	 * casting umin/umax as smin/smax and checking if they form valid
	 * range, and vice versa. Those are equivalent checks.
	 */
	if ((s64)reg->umin_value <= (s64)reg->umax_value) {
		reg->smin_value = max_t(s64, reg->smin_value, reg->umin_value);
		reg->smax_value = min_t(s64, reg->smax_value, reg->umax_value);
	}
	/* If we cannot cross the sign boundary, then signed and unsigned bounds
	 * are the same, so combine.  This works even in the negative case, e.g.
	 * -3 s<= x s<= -1 implies 0xf...fd u<= x u<= 0xf...ff.
	 */
	if ((u64)reg->smin_value <= (u64)reg->smax_value) {
		reg->umin_value = max_t(u64, reg->smin_value, reg->umin_value);
		reg->umax_value = min_t(u64, reg->smax_value, reg->umax_value);
	} else {
		/* If the s64 range crosses the sign boundary, then it's split
		 * between the beginning and end of the U64 domain. In that
		 * case, we can derive new bounds if the u64 range overlaps
		 * with only one end of the s64 range.
		 *
		 * In the following example, the u64 range overlaps only with
		 * positive portion of the s64 range.
		 *
		 * 0                                                   U64_MAX
		 * |  [xxxxxxxxxxxxxx u64 range xxxxxxxxxxxxxx]              |
		 * |----------------------------|----------------------------|
		 * |xxxxx s64 range xxxxxxxxx]                       [xxxxxxx|
		 * 0                     S64_MAX S64_MIN                    -1
		 *
		 * We can thus derive the following new s64 and u64 ranges.
		 *
		 * 0                                                   U64_MAX
		 * |  [xxxxxx u64 range xxxxx]                               |
		 * |----------------------------|----------------------------|
		 * |  [xxxxxx s64 range xxxxx]                               |
		 * 0                     S64_MAX S64_MIN                    -1
		 *
		 * If they overlap in two places, we can't derive anything
		 * because reg_state can't represent two ranges per numeric
		 * domain.
		 *
		 * 0                                                   U64_MAX
		 * |  [xxxxxxxxxxxxxxxxx u64 range xxxxxxxxxxxxxxxxx]        |
		 * |----------------------------|----------------------------|
		 * |xxxxx s64 range xxxxxxxxx]                    [xxxxxxxxxx|
		 * 0                     S64_MAX S64_MIN                    -1
		 *
		 * The first condition below corresponds to the first diagram
		 * above.
		 */
		if (reg->umax_value < (u64)reg->smin_value) {
			reg->smin_value = (s64)reg->umin_value;
			reg->umax_value = min_t(u64, reg->umax_value, reg->smax_value);
		} else if ((u64)reg->smax_value < reg->umin_value) {
			/* This second condition considers the case where the u64 range
			 * overlaps with the negative portion of the s64 range:
			 *
			 * 0                                                   U64_MAX
			 * |              [xxxxxxxxxxxxxx u64 range xxxxxxxxxxxxxx]  |
			 * |----------------------------|----------------------------|
			 * |xxxxxxxxx]                       [xxxxxxxxxxxx s64 range |
			 * 0                     S64_MAX S64_MIN                    -1
			 */
			reg->smax_value = (s64)reg->umax_value;
			reg->umin_value = max_t(u64, reg->umin_value, reg->smin_value);
		}
	}
}

static void __reg_deduce_mixed_bounds_old(struct bpf_reg_state *reg)
{
	/* Try to tighten 64-bit bounds from 32-bit knowledge, using 32-bit
	 * values on both sides of 64-bit range in hope to have tighter range.
	 * E.g., if r1 is [0x1'00000000, 0x3'80000000], and we learn from
	 * 32-bit signed > 0 operation that s32 bounds are now [1; 0x7fffffff].
	 * With this, we can substitute 1 as low 32-bits of _low_ 64-bit bound
	 * (0x100000000 -> 0x100000001) and 0x7fffffff as low 32-bits of
	 * _high_ 64-bit bound (0x380000000 -> 0x37fffffff) and arrive at a
	 * better overall bounds for r1 as [0x1'000000001; 0x3'7fffffff].
	 * We just need to make sure that derived bounds we are intersecting
	 * with are well-formed ranges in respective s64 or u64 domain, just
	 * like we do with similar kinds of 32-to-64 or 64-to-32 adjustments.
	 */
	u64 new_umin, new_umax;
	s64 new_smin, new_smax;

	/* u32 -> u64 tightening, it's always well-formed */
	new_umin = (reg->umin_value & ~0xffffffffULL) | reg->u32_min_value;
	new_umax = (reg->umax_value & ~0xffffffffULL) | reg->u32_max_value;
	reg->umin_value = max_t(u64, reg->umin_value, new_umin);
	reg->umax_value = min_t(u64, reg->umax_value, new_umax);
	/* u32 -> s64 tightening, u32 range embedded into s64 preserves range validity */
	new_smin = (reg->smin_value & ~0xffffffffULL) | reg->u32_min_value;
	new_smax = (reg->smax_value & ~0xffffffffULL) | reg->u32_max_value;
	reg->smin_value = max_t(s64, reg->smin_value, new_smin);
	reg->smax_value = min_t(s64, reg->smax_value, new_smax);

	/* Here we would like to handle a special case after sign extending load,
	 * when upper bits for a 64-bit range are all 1s or all 0s.
	 *
	 * Upper bits are all 1s when register is in a range:
	 *   [0xffff_ffff_0000_0000, 0xffff_ffff_ffff_ffff]
	 * Upper bits are all 0s when register is in a range:
	 *   [0x0000_0000_0000_0000, 0x0000_0000_ffff_ffff]
	 * Together this forms are continuous range:
	 *   [0xffff_ffff_0000_0000, 0x0000_0000_ffff_ffff]
	 *
	 * Now, suppose that register range is in fact tighter:
	 *   [0xffff_ffff_8000_0000, 0x0000_0000_ffff_ffff] (R)
	 * Also suppose that it's 32-bit range is positive,
	 * meaning that lower 32-bits of the full 64-bit register
	 * are in the range:
	 *   [0x0000_0000, 0x7fff_ffff] (W)
	 *
	 * If this happens, then any value in a range:
	 *   [0xffff_ffff_0000_0000, 0xffff_ffff_7fff_ffff]
	 * is smaller than a lowest bound of the range (R):
	 *   0xffff_ffff_8000_0000
	 * which means that upper bits of the full 64-bit register
	 * can't be all 1s, when lower bits are in range (W).
	 *
	 * Note that:
	 *  - 0xffff_ffff_8000_0000 == (s64)S32_MIN
	 *  - 0x0000_0000_7fff_ffff == (s64)S32_MAX
	 * These relations are used in the conditions below.
	 */
	if (reg->s32_min_value >= 0 && reg->smin_value >= S32_MIN && reg->smax_value <= S32_MAX) {
		reg->smin_value = reg->s32_min_value;
		reg->smax_value = reg->s32_max_value;
		reg->umin_value = reg->s32_min_value;
		reg->umax_value = reg->s32_max_value;
		reg->var_off = tnum_intersect(reg->var_off,
					      tnum_range(reg->smin_value, reg->smax_value));
	}
}

static void __reg_deduce_mixed_bounds_new(struct bpf_reg_state *reg)
{
	/* If upper 32 bits of u64/s64 range don't change, we can use lower 32
	 * bits to improve our u32/s32 boundaries.
	 *
	 * E.g., the case where we have upper 32 bits as zero ([10, 20] in
	 * u64) is pretty trivial, it's obvious that in u32 we'll also have
	 * [10, 20] range. But this property holds for any 64-bit range as
	 * long as upper 32 bits in that entire range of values stay the same.
	 *
	 * E.g., u64 range [0x10000000A, 0x10000000F] ([4294967306, 4294967311]
	 * in decimal) has the same upper 32 bits throughout all the values in
	 * that range. As such, lower 32 bits form a valid [0xA, 0xF] ([10, 15])
	 * range.
	 *
	 * Note also, that [0xA, 0xF] is a valid range both in u32 and in s32,
	 * following the rules outlined below about u64/s64 correspondence
	 * (which equally applies to u32 vs s32 correspondence). In general it
	 * depends on actual hexadecimal values of 32-bit range. They can form
	 * only valid u32, or only valid s32 ranges in some cases.
	 *
	 * So we use all these insights to derive bounds for subregisters here.
	 */
	if ((reg->umin_value >> 32) == (reg->umax_value >> 32)) {
		/* u64 to u32 casting preserves validity of low 32 bits as
		 * a range, if upper 32 bits are the same
		 */
		reg->u32_min_value = max_t(u32, reg->u32_min_value, (u32)reg->umin_value);
		reg->u32_max_value = min_t(u32, reg->u32_max_value, (u32)reg->umax_value);

		if ((s32)reg->umin_value <= (s32)reg->umax_value) {
			reg->s32_min_value = max_t(s32, reg->s32_min_value, (s32)reg->umin_value);
			reg->s32_max_value = min_t(s32, reg->s32_max_value, (s32)reg->umax_value);
		}
	}
	if ((reg->smin_value >> 32) == (reg->smax_value >> 32)) {
		/* low 32 bits should form a proper u32 range */
		if ((u32)reg->smin_value <= (u32)reg->smax_value) {
			reg->u32_min_value = max_t(u32, reg->u32_min_value, (u32)reg->smin_value);
			reg->u32_max_value = min_t(u32, reg->u32_max_value, (u32)reg->smax_value);
		}
		/* low 32 bits should form a proper s32 range */
		if ((s32)reg->smin_value <= (s32)reg->smax_value) {
			reg->s32_min_value = max_t(s32, reg->s32_min_value, (s32)reg->smin_value);
			reg->s32_max_value = min_t(s32, reg->s32_max_value, (s32)reg->smax_value);
		}
	}
	/* Special case where upper bits form a small sequence of two
	 * sequential numbers (in 32-bit unsigned space, so 0xffffffff to
	 * 0x00000000 is also valid), while lower bits form a proper s32 range
	 * going from negative numbers to positive numbers. E.g., let's say we
	 * have s64 range [-1, 1] ([0xffffffffffffffff, 0x0000000000000001]).
	 * Possible s64 values are {-1, 0, 1} ({0xffffffffffffffff,
	 * 0x0000000000000000, 0x00000000000001}). Ignoring upper 32 bits,
	 * we still get a valid s32 range [-1, 1] ([0xffffffff, 0x00000001]).
	 * Note that it doesn't have to be 0xffffffff going to 0x00000000 in
	 * upper 32 bits. As a random example, s64 range
	 * [0xfffffff0fffffff0; 0xfffffff100000010], forms a valid s32 range
	 * [-16, 16] ([0xfffffff0; 0x00000010]) in its 32 bit subregister.
	 */
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

	/* Try to tighten 64-bit bounds from 32-bit knowledge, using 32-bit
	 * values on both sides of 64-bit range in hope to have tighter range.
	 * E.g., if r1 is [0x1'00000000, 0x3'80000000], and we learn from
	 * 32-bit signed > 0 operation that s32 bounds are now [1; 0x7fffffff].
	 * With this, we can substitute 1 as low 32-bits of _low_ 64-bit bound
	 * (0x100000000 -> 0x100000001) and 0x7fffffff as low 32-bits of
	 * _high_ 64-bit bound (0x380000000 -> 0x37fffffff) and arrive at a
	 * better overall bounds for r1 as [0x1'000000001; 0x3'7fffffff].
	 * We just need to make sure that derived bounds we are intersecting
	 * with are well-formed ranges in respective s64 or u64 domain, just
	 * like we do with similar kinds of 32-to-64 or 64-to-32 adjustments.
	 */
	u64 new_umin, new_umax;
	s64 new_smin, new_smax;

	/* u32 -> u64 tightening, it's always well-formed */
	new_umin = (reg->umin_value & ~0xffffffffULL) | reg->u32_min_value;
	new_umax = (reg->umax_value & ~0xffffffffULL) | reg->u32_max_value;
	reg->umin_value = max_t(u64, reg->umin_value, new_umin);
	reg->umax_value = min_t(u64, reg->umax_value, new_umax);
	/* u32 -> s64 tightening, u32 range embedded into s64 preserves range validity */
	new_smin = (reg->smin_value & ~0xffffffffULL) | reg->u32_min_value;
	new_smax = (reg->smax_value & ~0xffffffffULL) | reg->u32_max_value;
	reg->smin_value = max_t(s64, reg->smin_value, new_smin);
	reg->smax_value = min_t(s64, reg->smax_value, new_smax);

	/* Here we would like to handle a special case after sign extending load,
	 * when upper bits for a 64-bit range are all 1s or all 0s.
	 *
	 * Upper bits are all 1s when register is in a range:
	 *   [0xffff_ffff_0000_0000, 0xffff_ffff_ffff_ffff]
	 * Upper bits are all 0s when register is in a range:
	 *   [0x0000_0000_0000_0000, 0x0000_0000_ffff_ffff]
	 * Together this forms are continuous range:
	 *   [0xffff_ffff_0000_0000, 0x0000_0000_ffff_ffff]
	 *
	 * Now, suppose that register range is in fact tighter:
	 *   [0xffff_ffff_8000_0000, 0x0000_0000_ffff_ffff] (R)
	 * Also suppose that it's 32-bit range is positive,
	 * meaning that lower 32-bits of the full 64-bit register
	 * are in the range:
	 *   [0x0000_0000, 0x7fff_ffff] (W)
	 *
	 * If this happens, then any value in a range:
	 *   [0xffff_ffff_0000_0000, 0xffff_ffff_7fff_ffff]
	 * is smaller than a lowest bound of the range (R):
	 *   0xffff_ffff_8000_0000
	 * which means that upper bits of the full 64-bit register
	 * can't be all 1s, when lower bits are in range (W).
	 *
	 * Note that:
	 *  - 0xffff_ffff_8000_0000 == (s64)S32_MIN
	 *  - 0x0000_0000_7fff_ffff == (s64)S32_MAX
	 * These relations are used in the conditions below.
	 */
	if (reg->s32_min_value >= 0 && reg->smin_value >= S32_MIN && reg->smax_value <= S32_MAX) {
		reg->smin_value = reg->s32_min_value;
		reg->smax_value = reg->s32_max_value;
		reg->umin_value = reg->s32_min_value;
		reg->umax_value = reg->s32_max_value;
		reg->var_off = tnum_intersect(reg->var_off,
					      tnum_range(reg->smin_value, reg->smax_value));
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
	/* We might have learned new bounds from the var_off. */
	__update_reg_bounds(reg);
	/* We might have learned something about the sign bit. */
	__reg_deduce_bounds_old(reg);
	__reg_deduce_bounds_old(reg);
	__reg_deduce_bounds_old(reg);
	/* We might have learned some bits from the bounds. */
	__reg_bound_offset(reg);
	/* Intersecting with the old var_off might have improved our bounds
	 * slightly, e.g. if umax was 0x7f...f and var_off was (0; 0xf...fc),
	 * then new var_off is (0; 0x7f...fc) which improves our umax.
	 */
	__update_reg_bounds(reg);
}

static void reg_bounds_sync_new(struct bpf_reg_state *reg)
{
	/* We might have learned new bounds from the var_off. */
	__update_reg_bounds(reg);
	/* We might have learned something about the sign bit. */
	__reg_deduce_bounds_new(reg);
	__reg_deduce_bounds_new(reg);
	/* We might have learned some bits from the bounds. */
	__reg_bound_offset(reg);
	/* Intersecting with the old var_off might have improved our bounds
	 * slightly, e.g. if umax was 0x7f...f and var_off was (0; 0xf...fc),
	 * then new var_off is (0; 0x7f...fc) which improves our umax.
	 */
	__update_reg_bounds(reg);
}

/* helper function to initialize 'struct bpf_reg_state' */
static struct bpf_reg_state __bpf_reg_state_input(void)
{
	struct bpf_reg_state reg;
	reg.smin_value = nondet_long_long_input();
	reg.smax_value = nondet_long_long_input();
	reg.umin_value = nondet_unsigned_long_long_input();
	reg.umax_value = nondet_unsigned_long_long_input();
	reg.s32_min_value = nondet_int_input();
	reg.s32_max_value = nondet_int_input();
	reg.u32_min_value = nondet_unsigned_int_input();
	reg.u32_max_value = nondet_unsigned_int_input();
	return reg;
}

/* helper function to ensure 'struct bpf_reg_state' is in a proper state */
static bool valid_bpf_reg_state(struct bpf_reg_state *reg)
{
	bool ret = true;
	/* Ensure maximum >= minimum for all ranges */
	ret &= reg->umin_value <= reg->umax_value;
	ret &= reg->smin_value <= reg->smax_value;
	ret &= reg->u32_min_value <= reg->u32_max_value;
	ret &= reg->s32_min_value <= reg->s32_max_value;
	/* Ensure 64-bit bounds are consistent with 32-bit bounds */
	ret &= reg->umin_value <= (u64)reg->u32_max_value;
	ret &= reg->umax_value >= (u64)reg->u32_min_value;
	ret &= (s64)reg->smin_value <= (s64)reg->s32_max_value;
	ret &= (s64)reg->smax_value >= (s64)reg->s32_min_value;
	/* tnum well-formedness: no bit is simultaneously known and unknown */
	ret &= (reg->var_off.value & reg->var_off.mask) == 0;
	/* u64 bounds must be consistent with tnum:
	 *   minimum concrete value = known-1 bits = var_off.value (when well-formed)
	 *   maximum concrete value = known-1 bits | unknown bits  = value | mask
	 */
	ret &= reg->umin_value >= reg->var_off.value;
	ret &= reg->umax_value <= (reg->var_off.value | reg->var_off.mask);
	/* s64 bounds: the sign bit contributes S64_MIN, so the tnum-implied
	 * signed minimum sets the sign bit if it is unknown (worst case negative),
	 * and the tnum-implied signed maximum clears the sign bit if it is unknown
	 * (worst case positive).
	 */
	ret &= reg->smin_value >= (s64)(reg->var_off.value | (reg->var_off.mask & (u64)S64_MIN));
	ret &= reg->smax_value <= (s64)(reg->var_off.value | (reg->var_off.mask & (u64)S64_MAX));
	/* u32 subregister bounds must be consistent with the low-32 bits of tnum */
	ret &= reg->u32_min_value >= (u32)reg->var_off.value;
	ret &= reg->u32_max_value <= (u32)(reg->var_off.value | reg->var_off.mask);
	/* s32 subregister bounds: same sign-bit logic as s64 but within 32 bits */
	ret &= reg->s32_min_value >= (s32)((u32)reg->var_off.value | ((u32)reg->var_off.mask & (u32)S32_MIN));
	ret &= reg->s32_max_value <= (s32)((u32)reg->var_off.value | ((u32)reg->var_off.mask & (u32)S32_MAX));
	return ret;
}

/* helper function to check whether 'struct bpf_reg_state' contains certain value */
static bool val_in_reg(struct bpf_reg_state *reg, u64 val)
{
	bool ret = true;
	ret &= reg->umin_value <= val;
	ret &= val <= reg->umax_value;
	ret &= reg->smin_value <= (s64)val;
	ret &= (s64)val <= reg->smax_value;
	ret &= reg->u32_min_value <= (u32)val;
	ret &= (u32)val <= reg->u32_max_value;
	ret &= reg->s32_min_value <= (s32)val;
	ret &= (s32)val <= reg->s32_max_value;
	/* val must satisfy the tnum pattern: known bits of val must match var_off */
	ret &= (val & ~reg->var_off.mask) == reg->var_off.value;
	return ret;
}

void main(void)
{
	/* ------------ Assumptions and Setup ------------ */

	/* Input data structure that represents current knowledge of the possible
	 * values in a register, as well as some possible value 'x', which could be
	 * any value that is in the register right now.
	 */
	struct bpf_reg_state reg = __bpf_reg_state_input();
	u64 x = nondet_unsigned_long_long_input();
	__CPROVER_assume(valid_bpf_reg_state(&reg));
	__CPROVER_assume(x <= 32);
	__CPROVER_assume(val_in_reg(&reg, x));

	/* ------------- Operation to Check -------------- */
	/* Data structure to store the new output */
	struct bpf_reg_state new_reg;
	/* Clone the register state since __reg_deduce_bounds() modifies it */
	new_reg = reg;

	reg_bounds_sync_old(&reg);
	reg_bounds_sync_new(&new_reg);

	/* -------------- Property Checking -------------- */
	assert(new_reg.var_off.value == reg.var_off.value);
	assert(new_reg.var_off.mask == reg.var_off.mask);
	assert(new_reg.umin_value == reg.umin_value);
	assert(new_reg.umax_value == reg.umax_value);
	assert(new_reg.smin_value == reg.smin_value);
	assert(new_reg.smax_value == reg.smax_value);
	assert(new_reg.u32_min_value == reg.u32_min_value);
	assert(new_reg.u32_max_value == reg.u32_max_value);
	assert(new_reg.s32_min_value == reg.s32_min_value);
	assert(new_reg.s32_max_value == reg.s32_max_value);
}
