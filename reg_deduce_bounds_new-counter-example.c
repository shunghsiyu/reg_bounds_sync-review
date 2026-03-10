#include "bpf_reg.h"

static void reg_bounds_sync_new_loop(struct bpf_reg_state *reg)
{
	/* make grepping easier */
	struct bpf_reg_state current, next;
	int i;

	__update_reg_bounds(reg);
	/* 2 calls are not enough */
	__reg_deduce_bounds_new(reg);
	__reg_deduce_bounds_new(reg);
	{
		current = *reg;
		next = *reg;
		__reg_deduce_bounds_new(&next);
		assert(next.var_off.value == current.var_off.value);
		assert(next.var_off.mask  == current.var_off.mask);
		assert(next.umin_value    == current.umin_value);
		assert(next.umax_value    == current.umax_value);
		assert(next.smin_value    == current.smin_value);
		assert(next.smax_value    == current.smax_value);
		assert(next.u32_min_value == current.u32_min_value);
		assert(next.u32_max_value == current.u32_max_value);
		assert(next.s32_min_value == current.s32_min_value);
		assert(next.s32_max_value == current.s32_max_value);
	}
	__reg_bound_offset(reg);
	__update_reg_bounds(reg);
}

void main(void)
{
	/* ------------ Assumptions and Setup ------------ */

	/* Input data structure that represents current knowledge of the possible
	 * values in a register, as well as some possible value 'x', which could be
	 * any value that is in the register right now.
	 */
	struct bpf_reg_state reg = __bpf_reg_state_input();
	u64 actual = nondet_unsigned_long_long_input();
	__CPROVER_assume(valid_bpf_reg_state(&reg));
	__CPROVER_assume(val_in_reg(&reg, actual));
	/* Adding additional constraint so the counter example is easier to
	 * understand */
	__CPROVER_assume(reg.smax_value <= 32);
	__CPROVER_assume(reg.smin_value >= -32);
	__CPROVER_assume(reg.s32_max_value <= 32);
	__CPROVER_assume(reg.s32_min_value >= -32);
	__CPROVER_assume(reg.var_off.value == 0);

	/* ------------- Operation to Check -------------- */
	reg_bounds_sync_new_loop(&reg);
}
