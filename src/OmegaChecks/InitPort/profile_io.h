#pragma once
#include <lean/lean.h>

/* Keep the caller's explicit world and complete strict EST.Out together as the
   profiler's successful payload. Returning the strict result restores either branch. */
static lean_obj_res omega_profile_action(lean_obj_arg action, lean_obj_arg world, lean_obj_arg unit) {
    lean_dec(unit);
    return lean_io_result_mk_ok(lean_apply_1(action, world));
}

static lean_obj_res omega_profile_result(lean_obj_arg io) {
    lean_object *result = lean_io_result_get_value(io);
    lean_inc(result);
    lean_dec(io);
    return result;
}
