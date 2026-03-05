/* verify_fixed_harness.c
 *
 * Demonstrates two things:
 *
 * A) The specific counter-example from the report is REJECTED when the
 *    missing tnum consistency assumption is added.  The __CPROVER_assume
 *    for val_matches_tnum(reg.var_off, x=32) is INFEASIBLE for the
 *    concrete counter-example state, meaning CBMC cannot reach any
 *    assertion and the path is dead — confirming the fix works.
 *
 * B) On the restricted class of "fully consistent, constant registers"
 *    (var_off.mask == 0, all eight bounds equal the same value, x == that
 *    value) the two implementations produce identical results.
 *    This class trivially satisfies tnum consistency and is a good
 *    sanity-check that both implementations handle the base case identically.
 *
 * Run with:
 *   cbmc --unwind 1 verify_fixed_harness.c
 *
 * Expected: VERIFICATION SUCCESSFUL (all assertions pass).
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
#define U64_MAX  UINT64_MAX
#define U32_MAX  UINT32_MAX
#define min_t(type,x,y) (((type)(x))<((type)(y))?((type)(x)):((type)(y)))
#define max_t(type,x,y) (((type)(x))>((type)(y))?((type)(x)):((type)(y)))

struct tnum { u64 value; u64 mask; };
#define TNUM(_v,_m) (struct tnum){.value=(_v),.mask=(_m)}

struct bpf_reg_state {
    struct tnum var_off;
    s64 smin_value, smax_value;
    u64 umin_value, umax_value;
    s32 s32_min_value, s32_max_value;
    u32 u32_min_value, u32_max_value;
};

/* ---- minimal helpers ---- */
#define BITS_PER_LONG 64
static __always_inline unsigned int __fls(unsigned long word) {
    unsigned int num = BITS_PER_LONG - 1;
    if (!(word & (~0ul<<32)))          { num-=32; word<<=32; }
    if (!(word & (~0ul<<(BITS_PER_LONG-16)))) { num-=16; word<<=16; }
    if (!(word & (~0ul<<(BITS_PER_LONG-8))))  { num-=8;  word<<=8;  }
    if (!(word & (~0ul<<(BITS_PER_LONG-4))))  { num-=4;  word<<=4;  }
    if (!(word & (~0ul<<(BITS_PER_LONG-2))))  { num-=2;  word<<=2;  }
    if (!(word & (~0ul<<(BITS_PER_LONG-1))))  num-=1;
    return num;
}
static __always_inline int fls64(u64 x) { return x ? __fls(x)+1 : 0; }

struct tnum tnum_const(u64 v) { return TNUM(v,0); }
struct tnum tnum_range(u64 min, u64 max) {
    u64 chi=min^max, delta; u8 bits=fls64(chi);
    if (bits>63) return TNUM(0,U64_MAX);
    delta=(1ULL<<bits)-1; return TNUM(min&~delta,delta);
}
struct tnum tnum_intersect(struct tnum a, struct tnum b) {
    u64 v=a.value|b.value, mu=a.mask&b.mask; return TNUM(v&~mu,mu);
}
struct tnum tnum_or(struct tnum a, struct tnum b) {
    u64 v=a.value|b.value, mu=a.mask|b.mask; return TNUM(v,mu&~v);
}
struct tnum tnum_cast(struct tnum a, u8 size) {
    a.value&=(1ULL<<(size*8))-1; a.mask&=(1ULL<<(size*8))-1; return a;
}
struct tnum tnum_subreg(struct tnum a) { return tnum_cast(a,4); }
struct tnum tnum_rshift(struct tnum a, u8 s) { return TNUM(a.value>>s,a.mask>>s); }
struct tnum tnum_lshift(struct tnum a, u8 s) { return TNUM(a.value<<s,a.mask<<s); }
struct tnum tnum_clear_subreg(struct tnum a) { return tnum_lshift(tnum_rshift(a,32),32); }

static void ___mark_reg_known(struct bpf_reg_state *reg, u64 imm) {
    reg->var_off=tnum_const(imm);
    reg->smin_value=reg->smax_value=(s64)imm;
    reg->umin_value=reg->umax_value=imm;
    reg->s32_min_value=reg->s32_max_value=(s32)imm;
    reg->u32_min_value=reg->u32_max_value=(u32)imm;
}
u64 tnum_step(struct tnum t, u64 z) {
    u64 tmax,j,p,q,r,s,v,u,w,res; u8 k;
    tmax=t.value|t.mask;
    if(z>=tmax) return tmax;
    if(z<t.value) return t.value;
    j=t.value|(z&t.mask);
    if(j>z){ p=~z&t.value&~t.mask;k=fls64(p);q=U64_MAX<<k;r=q&z;s=~q&t.value;v=r|s;res=v; }
    else { p=z&~t.value&~t.mask;k=fls64(p);q=U64_MAX<<k;r=q&t.mask&z;s=q&~t.mask;v=r|s;u=v+(1ULL<<k);w=(u&t.mask)|t.value;res=w; }
    return res;
}
static void __update_reg32_bounds(struct bpf_reg_state *reg) {
    struct tnum v32=tnum_subreg(reg->var_off);
    reg->s32_min_value=max_t(s32,reg->s32_min_value,v32.value|(v32.mask&S32_MIN));
    reg->s32_max_value=min_t(s32,reg->s32_max_value,v32.value|(v32.mask&S32_MAX));
    reg->u32_min_value=max_t(u32,reg->u32_min_value,(u32)v32.value);
    reg->u32_max_value=min_t(u32,reg->u32_max_value,(u32)(v32.value|v32.mask));
}
static void __update_reg64_bounds(struct bpf_reg_state *reg) {
    u64 tn,tmax; bool ui;
    reg->smin_value=max_t(s64,reg->smin_value,reg->var_off.value|(reg->var_off.mask&S64_MIN));
    reg->smax_value=min_t(s64,reg->smax_value,reg->var_off.value|(reg->var_off.mask&S64_MAX));
    reg->umin_value=max_t(u64,reg->umin_value,reg->var_off.value);
    reg->umax_value=min_t(u64,reg->umax_value,reg->var_off.value|reg->var_off.mask);
    tn=tnum_step(reg->var_off,reg->umin_value);
    ui=(reg->umin_value&~reg->var_off.mask)==reg->var_off.value;
    tmax=reg->var_off.value|reg->var_off.mask;
    if(ui&&tn>reg->umax_value) ___mark_reg_known(reg,reg->umin_value);
    else if(!ui&&tn==tmax) ___mark_reg_known(reg,tmax);
    else if(!ui&&tn<=reg->umax_value&&tnum_step(reg->var_off,tn)>reg->umax_value) ___mark_reg_known(reg,tn);
}
static void __update_reg_bounds(struct bpf_reg_state *reg) { __update_reg32_bounds(reg); __update_reg64_bounds(reg); }

static void __reg32_deduce_bounds_old(struct bpf_reg_state *reg) {
    if((reg->umin_value>>32)==(reg->umax_value>>32)){
        reg->u32_min_value=max_t(u32,reg->u32_min_value,(u32)reg->umin_value);
        reg->u32_max_value=min_t(u32,reg->u32_max_value,(u32)reg->umax_value);
        if((s32)reg->umin_value<=(s32)reg->umax_value){
            reg->s32_min_value=max_t(s32,reg->s32_min_value,(s32)reg->umin_value);
            reg->s32_max_value=min_t(s32,reg->s32_max_value,(s32)reg->umax_value);
        }
    }
    if((reg->smin_value>>32)==(reg->smax_value>>32)){
        if((u32)reg->smin_value<=(u32)reg->smax_value){
            reg->u32_min_value=max_t(u32,reg->u32_min_value,(u32)reg->smin_value);
            reg->u32_max_value=min_t(u32,reg->u32_max_value,(u32)reg->smax_value);
        }
        if((s32)reg->smin_value<=(s32)reg->smax_value){
            reg->s32_min_value=max_t(s32,reg->s32_min_value,(s32)reg->smin_value);
            reg->s32_max_value=min_t(s32,reg->s32_max_value,(s32)reg->smax_value);
        }
    }
    if((u32)(reg->umin_value>>32)+1==(u32)(reg->umax_value>>32)&&(s32)reg->umin_value<0&&(s32)reg->umax_value>=0){
        reg->s32_min_value=max_t(s32,reg->s32_min_value,(s32)reg->umin_value);
        reg->s32_max_value=min_t(s32,reg->s32_max_value,(s32)reg->umax_value);
    }
    if((u32)(reg->smin_value>>32)+1==(u32)(reg->smax_value>>32)&&(s32)reg->smin_value<0&&(s32)reg->smax_value>=0){
        reg->s32_min_value=max_t(s32,reg->s32_min_value,(s32)reg->smin_value);
        reg->s32_max_value=min_t(s32,reg->s32_max_value,(s32)reg->smax_value);
    }
    if((s32)reg->u32_min_value<=(s32)reg->u32_max_value){
        reg->s32_min_value=max_t(s32,reg->s32_min_value,reg->u32_min_value);
        reg->s32_max_value=min_t(s32,reg->s32_max_value,reg->u32_max_value);
    }
    if((u32)reg->s32_min_value<=(u32)reg->s32_max_value){
        reg->u32_min_value=max_t(u32,reg->s32_min_value,reg->u32_min_value);
        reg->u32_max_value=min_t(u32,reg->s32_max_value,reg->u32_max_value);
    }
}
static void __reg32_deduce_bounds_new(struct bpf_reg_state *reg) {
    if((s32)reg->u32_min_value<=(s32)reg->u32_max_value){
        reg->s32_min_value=max_t(s32,reg->s32_min_value,reg->u32_min_value);
        reg->s32_max_value=min_t(s32,reg->s32_max_value,reg->u32_max_value);
    }
    if((u32)reg->s32_min_value<=(u32)reg->s32_max_value){
        reg->u32_min_value=max_t(u32,reg->s32_min_value,reg->u32_min_value);
        reg->u32_max_value=min_t(u32,reg->s32_max_value,reg->u32_max_value);
    }
}
static void __reg64_deduce_bounds(struct bpf_reg_state *reg) {
    if((s64)reg->umin_value<=(s64)reg->umax_value){
        reg->smin_value=max_t(s64,reg->smin_value,reg->umin_value);
        reg->smax_value=min_t(s64,reg->smax_value,reg->umax_value);
    }
    if((u64)reg->smin_value<=(u64)reg->smax_value){
        reg->umin_value=max_t(u64,reg->smin_value,reg->umin_value);
        reg->umax_value=min_t(u64,reg->smax_value,reg->umax_value);
    } else {
        if(reg->umax_value<(u64)reg->smin_value){
            reg->smin_value=(s64)reg->umin_value;
            reg->umax_value=min_t(u64,reg->umax_value,reg->smax_value);
        } else if((u64)reg->smax_value<reg->umin_value){
            reg->smax_value=(s64)reg->umax_value;
            reg->umin_value=max_t(u64,reg->umin_value,reg->smin_value);
        }
    }
}
static void __reg_deduce_mixed_bounds_old(struct bpf_reg_state *reg) {
    u64 nu,nU; s64 ns,nS;
    nu=(reg->umin_value&~0xffffffffULL)|reg->u32_min_value;
    nU=(reg->umax_value&~0xffffffffULL)|reg->u32_max_value;
    reg->umin_value=max_t(u64,reg->umin_value,nu);
    reg->umax_value=min_t(u64,reg->umax_value,nU);
    ns=(reg->smin_value&~0xffffffffULL)|reg->u32_min_value;
    nS=(reg->smax_value&~0xffffffffULL)|reg->u32_max_value;
    reg->smin_value=max_t(s64,reg->smin_value,ns);
    reg->smax_value=min_t(s64,reg->smax_value,nS);
    if(reg->s32_min_value>=0&&reg->smin_value>=S32_MIN&&reg->smax_value<=S32_MAX){
        reg->smin_value=reg->s32_min_value; reg->smax_value=reg->s32_max_value;
        reg->umin_value=reg->s32_min_value; reg->umax_value=reg->s32_max_value;
        reg->var_off=tnum_intersect(reg->var_off,tnum_range(reg->smin_value,reg->smax_value));
    }
}
static void __reg_deduce_mixed_bounds_new(struct bpf_reg_state *reg) {
    if((reg->umin_value>>32)==(reg->umax_value>>32)){
        reg->u32_min_value=max_t(u32,reg->u32_min_value,(u32)reg->umin_value);
        reg->u32_max_value=min_t(u32,reg->u32_max_value,(u32)reg->umax_value);
        if((s32)reg->umin_value<=(s32)reg->umax_value){
            reg->s32_min_value=max_t(s32,reg->s32_min_value,(s32)reg->umin_value);
            reg->s32_max_value=min_t(s32,reg->s32_max_value,(s32)reg->umax_value);
        }
    }
    if((reg->smin_value>>32)==(reg->smax_value>>32)){
        if((u32)reg->smin_value<=(u32)reg->smax_value){
            reg->u32_min_value=max_t(u32,reg->u32_min_value,(u32)reg->smin_value);
            reg->u32_max_value=min_t(u32,reg->u32_max_value,(u32)reg->smax_value);
        }
        if((s32)reg->smin_value<=(s32)reg->smax_value){
            reg->s32_min_value=max_t(s32,reg->s32_min_value,(s32)reg->smin_value);
            reg->s32_max_value=min_t(s32,reg->s32_max_value,(s32)reg->smax_value);
        }
    }
    if((u32)(reg->umin_value>>32)+1==(u32)(reg->umax_value>>32)&&(s32)reg->umin_value<0&&(s32)reg->umax_value>=0){
        reg->s32_min_value=max_t(s32,reg->s32_min_value,(s32)reg->umin_value);
        reg->s32_max_value=min_t(s32,reg->s32_max_value,(s32)reg->umax_value);
    }
    if((u32)(reg->smin_value>>32)+1==(u32)(reg->smax_value>>32)&&(s32)reg->smin_value<0&&(s32)reg->smax_value>=0){
        reg->s32_min_value=max_t(s32,reg->s32_min_value,(s32)reg->smin_value);
        reg->s32_max_value=min_t(s32,reg->s32_max_value,(s32)reg->smax_value);
    }
    u64 nu,nU; s64 ns,nS;
    nu=(reg->umin_value&~0xffffffffULL)|reg->u32_min_value;
    nU=(reg->umax_value&~0xffffffffULL)|reg->u32_max_value;
    reg->umin_value=max_t(u64,reg->umin_value,nu);
    reg->umax_value=min_t(u64,reg->umax_value,nU);
    ns=(reg->smin_value&~0xffffffffULL)|reg->u32_min_value;
    nS=(reg->smax_value&~0xffffffffULL)|reg->u32_max_value;
    reg->smin_value=max_t(s64,reg->smin_value,ns);
    reg->smax_value=min_t(s64,reg->smax_value,nS);
    if(reg->s32_min_value>=0&&reg->smin_value>=S32_MIN&&reg->smax_value<=S32_MAX){
        reg->smin_value=reg->s32_min_value; reg->smax_value=reg->s32_max_value;
        reg->umin_value=reg->s32_min_value; reg->umax_value=reg->s32_max_value;
        reg->var_off=tnum_intersect(reg->var_off,tnum_range(reg->smin_value,reg->smax_value));
    }
}
static void __reg_deduce_bounds_old(struct bpf_reg_state *reg) {
    __reg32_deduce_bounds_old(reg); __reg64_deduce_bounds(reg); __reg_deduce_mixed_bounds_old(reg);
}
static void __reg_deduce_bounds_new(struct bpf_reg_state *reg) {
    __reg32_deduce_bounds_new(reg); __reg64_deduce_bounds(reg); __reg_deduce_mixed_bounds_new(reg);
}
static void __reg_bound_offset(struct bpf_reg_state *reg) {
    struct tnum v64=tnum_intersect(reg->var_off,tnum_range(reg->umin_value,reg->umax_value));
    struct tnum v32=tnum_intersect(tnum_subreg(v64),tnum_range(reg->u32_min_value,reg->u32_max_value));
    reg->var_off=tnum_or(tnum_clear_subreg(v64),v32);
}
static void reg_bounds_sync_old(struct bpf_reg_state *reg) {
    __update_reg_bounds(reg);
    __reg_deduce_bounds_old(reg); __reg_deduce_bounds_old(reg); __reg_deduce_bounds_old(reg);
    __reg_bound_offset(reg); __update_reg_bounds(reg);
}
static void reg_bounds_sync_new(struct bpf_reg_state *reg) {
    __update_reg_bounds(reg);
    __reg_deduce_bounds_new(reg); __reg_deduce_bounds_new(reg);
    __reg_bound_offset(reg); __update_reg_bounds(reg);
}

/* ================================================================
 * PART A — Show the counter-example input is REJECTED by the fix.
 *
 * The original harness accepted the contradictory state because
 * val_in_reg(reg, x=32) passed.  Once we add the tnum-consistency
 * assumption, the path with x=32 and var_off.value=0x40A04B5D
 * becomes INFEASIBLE (assume evaluates to FALSE) → the bounded
 * model checker sees zero reachable assertion checks → the property
 * is trivially satisfied.
 *
 * We demonstrate this by constructing the exact concrete counter-example
 * initial state and x=32, then asserting that the fixed assumption
 * kills the path.
 *
 * EXPECTED: SUCCESS (fixed assumption is infeasible for counter-example).
 * ================================================================ */
static bool val_matches_tnum(struct tnum t, u64 val) {
    return (val & ~t.mask) == (t.value & ~t.mask);
}

void partA_counter_example_rejected_by_fix(void) {
    /* The concrete counter-example state */
    struct tnum var_off = TNUM(1084246877UL, 18446744070485517312UL);
    u64 x = 32UL;

    /* The fix: assume x matches var_off */
    /* val_matches_tnum(var_off, 32)?
     *   known_ones = 0x40A04B5D & ~0xFFFFFFFF3FD52400 (lower32: ~0x3FD52400 = 0xC02ADBFF)
     *              = 0x40A04B5D & 0xC02ADBFF = 0x40204B5D
     *   32 & 0xC02ADBFF = 0x20
     *   0x20 != 0x40204B5D  → val_matches_tnum returns FALSE */
    bool consistent = val_matches_tnum(var_off, x);

    /* CBMC-provable: the fixed assumption is FALSE for this input */
    __CPROVER_assert(!consistent,
        "PART A: val_matches_tnum(counter-example var_off, x=32) == FALSE "
        "(fixed assume kills the path)");

    /* Extra: verify the exact known-ones pattern */
    u32 mask_lo = (u32)var_off.mask;       /* 0x3FD5_2400 */
    u32 val_lo  = (u32)var_off.value;      /* 0x40A0_4B5D */
    u32 known_ones = val_lo & ~mask_lo;    /* 0x4020_4B5D */
    __CPROVER_assert(known_ones == 0x40204B5DU,
        "PART A: known-ones bits of counter-example var_off == 0x4020_4B5D");
    __CPROVER_assert((u32)(x & ~mask_lo) != known_ones,
        "PART A: (x=32) & ~mask != known_ones → inconsistency confirmed");
}

/* ================================================================
 * PART B — Equivalence on constant registers (var_off.mask == 0).
 *
 * A constant register has var_off.mask == 0 and all bounds equal to
 * the same value v.  This class trivially satisfies tnum consistency
 * (every concrete value IS v, and v & ~0 == v == var_off.value & ~0).
 *
 * Both reg_bounds_sync_old and reg_bounds_sync_new should leave a
 * constant register unchanged (or at most confirm it is still constant).
 * We verify they produce identical results on all symbolic constant regs.
 *
 * EXPECTED: SUCCESS (old == new on constant registers).
 * ================================================================ */
void partB_equivalence_on_constant_registers(void) {
    u64 v = nondet_ulong(); /* the constant value (fully symbolic) */

    /* Build a fully consistent constant register */
    struct bpf_reg_state old_r, new_r;
    old_r.var_off.value = v; old_r.var_off.mask = 0UL;
    old_r.umin_value = old_r.umax_value = v;
    old_r.smin_value = old_r.smax_value = (s64)v;
    old_r.u32_min_value = old_r.u32_max_value = (u32)v;
    old_r.s32_min_value = old_r.s32_max_value = (s32)v;
    new_r = old_r;

    /* Run both sync functions */
    reg_bounds_sync_old(&old_r);
    reg_bounds_sync_new(&new_r);

    /* Both must produce identical results */
    __CPROVER_assert(old_r.var_off.value == new_r.var_off.value,
        "PART B: constant reg — var_off.value matches");
    __CPROVER_assert(old_r.var_off.mask == new_r.var_off.mask,
        "PART B: constant reg — var_off.mask matches");
    __CPROVER_assert(old_r.umin_value == new_r.umin_value,
        "PART B: constant reg — umin matches");
    __CPROVER_assert(old_r.umax_value == new_r.umax_value,
        "PART B: constant reg — umax matches");
    __CPROVER_assert(old_r.smin_value == new_r.smin_value,
        "PART B: constant reg — smin matches");
    __CPROVER_assert(old_r.smax_value == new_r.smax_value,
        "PART B: constant reg — smax matches");
    __CPROVER_assert(old_r.u32_min_value == new_r.u32_min_value,
        "PART B: constant reg — u32_min matches");
    __CPROVER_assert(old_r.u32_max_value == new_r.u32_max_value,
        "PART B: constant reg — u32_max matches");
    __CPROVER_assert(old_r.s32_min_value == new_r.s32_min_value,
        "PART B: constant reg — s32_min matches");
    __CPROVER_assert(old_r.s32_max_value == new_r.s32_max_value,
        "PART B: constant reg — s32_max matches");

    /* And the result must still be a constant register */
    __CPROVER_assert(old_r.var_off.mask == 0UL,
        "PART B: old — result is still a constant register");
    __CPROVER_assert(new_r.var_off.mask == 0UL,
        "PART B: new — result is still a constant register");
}

void main(void) {
    partA_counter_example_rejected_by_fix();
    partB_equivalence_on_constant_registers();
}
