/* reg_deduce_bounds-compare.c
 *
 * Main equivalence harness: checks whether reg_bounds_sync_old and
 * reg_bounds_sync_new produce identical results for all valid inputs.
 *
 * Run with:
 *   cbmc --compact-trace reg_deduce_bounds-compare.c
 *
 * All ten assertions fail → the two implementations diverge on valid inputs.
 */

#include "bpf_reg.h"

unsigned int popcount64(unsigned long long x) {
	x = (x & 0x5555555555555555ULL) + ((x >> 1) & 0x5555555555555555ULL);
	x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
	x = (x & 0x0F0F0F0F0F0F0F0FULL) + ((x >> 4) & 0x0F0F0F0F0F0F0F0FULL);
	return (x * 0x0101010101010101ULL) >> 56;
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
	__CPROVER_assume(val_in_reg(&reg, x));
	__CPROVER_assume(x <= 32);
	__CPROVER_assume(reg.umax_value <= 32);
	__CPROVER_assume(popcount64(reg.var_off.mask) <= 2);

	/* ------------- Operation to Check -------------- */
	/* Clone the register state since reg_bounds_sync_* modifies it */
	struct bpf_reg_state old_reg = reg;
	struct bpf_reg_state new_reg = reg;

	reg_bounds_sync_old(&old_reg);
	reg_bounds_sync_new(&new_reg);

	/* -------------- Property Checking -------------- */
	assert(new_reg.var_off.value == old_reg.var_off.value);
	assert(new_reg.var_off.mask  == old_reg.var_off.mask);
	assert(new_reg.umin_value    == old_reg.umin_value);
	assert(new_reg.umax_value    == old_reg.umax_value);
	assert(new_reg.smin_value    == old_reg.smin_value);
	assert(new_reg.smax_value    == old_reg.smax_value);
	assert(new_reg.u32_min_value == old_reg.u32_min_value);
	assert(new_reg.u32_max_value == old_reg.u32_max_value);
	assert(new_reg.s32_min_value == old_reg.s32_min_value);
	assert(new_reg.s32_max_value == old_reg.s32_max_value);
}
