#include "bpf_reg.h"

#define REG_BOUNDS_MAX_ITERS 1000

static void reg_bounds_sync_old_loop(struct bpf_reg_state *current)
{
	struct bpf_reg_state next;
	int i;

	__update_reg_bounds(current);
	/* Taking any call away from below make verification fails */
	__reg_deduce_bounds_old(current);
	__reg_deduce_bounds_old(current);
	__reg_deduce_bounds_old(current);
	/* Try to see if an extra round of __reg_deduce_bounds_old further
	 * changes anything.
	 */
	{
		next = *current;
		__reg_deduce_bounds_old(&next);
		assert(next.var_off.value == current->var_off.value);
		assert(next.var_off.mask  == current->var_off.mask);
		assert(next.umin_value    == current->umin_value);
		assert(next.umax_value    == current->umax_value);
		assert(next.smin_value    == current->smin_value);
		assert(next.smax_value    == current->smax_value);
		assert(next.u32_min_value == current->u32_min_value);
		assert(next.u32_max_value == current->u32_max_value);
		assert(next.s32_min_value == current->s32_min_value);
		assert(next.s32_max_value == current->s32_max_value);
	}
	__reg_bound_offset(current);
	__update_reg_bounds(current);
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

	/* ------------- Operation to Check -------------- */
	reg_bounds_sync_old_loop(&reg);
}
