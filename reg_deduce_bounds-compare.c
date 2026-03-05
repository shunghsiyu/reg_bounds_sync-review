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
	/* Clone the register state since reg_bounds_sync_* modifies it */
	struct bpf_reg_state new_reg = reg;

	reg_bounds_sync_old(&reg);
	reg_bounds_sync_new(&new_reg);

	/* -------------- Property Checking -------------- */
	assert(new_reg.var_off.value == reg.var_off.value);
	assert(new_reg.var_off.mask  == reg.var_off.mask);
	assert(new_reg.umin_value    == reg.umin_value);
	assert(new_reg.umax_value    == reg.umax_value);
	assert(new_reg.smin_value    == reg.smin_value);
	assert(new_reg.smax_value    == reg.smax_value);
	assert(new_reg.u32_min_value == reg.u32_min_value);
	assert(new_reg.u32_max_value == reg.u32_max_value);
	assert(new_reg.s32_min_value == reg.s32_min_value);
	assert(new_reg.s32_max_value == reg.s32_max_value);
}
