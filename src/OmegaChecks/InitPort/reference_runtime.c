#include <lean/lean.h>
#include "est_out_elim.h"
extern uint8_t lean_st_ref_ptr_eq(b_lean_obj_arg, b_lean_obj_arg);

static lean_obj_res state_result(lean_obj_arg value, lean_obj_arg world) {
    lean_obj_res result = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result, 0, value);
    lean_ctor_set(result, 1, world);
    return result;
}

LEAN_EXPORT lean_obj_res omega_st_mk_ref(lean_obj_arg value, lean_obj_arg world) {
    return state_result(lean_st_mk_ref(value), world);
}

LEAN_EXPORT lean_obj_res omega_st_ref_swap(b_lean_obj_arg ref, lean_obj_arg value, lean_obj_arg world) {
    return state_result(lean_st_ref_swap(ref, value), world);
}

LEAN_EXPORT lean_obj_res omega_st_ref_put(b_lean_obj_arg ref, lean_obj_arg value, lean_obj_arg world) {
    return state_result(lean_st_ref_put(ref, value), world);
}

LEAN_EXPORT lean_obj_res omega_st_ref_set(lean_obj_arg ref, lean_obj_arg value, lean_obj_arg world) {
    lean_dec(lean_st_ref_swap(ref, value));
    lean_dec(ref);
    return state_result(lean_box(0), world);
}

LEAN_EXPORT lean_obj_res omega_st_ref_ptr_eq(b_lean_obj_arg a, b_lean_obj_arg b, lean_obj_arg world) {
    return state_result(lean_box(lean_st_ref_ptr_eq(a, b)), world);
}

LEAN_EXPORT lean_obj_res omega_state_ref_read_with_initial(lean_obj_arg initial, b_lean_obj_arg ref, lean_obj_arg world) {
    lean_dec(initial);
    return state_result(lean_st_ref_get(ref), world);
}

LEAN_EXPORT lean_obj_res omega_st_ref_read_for_modify(b_lean_obj_arg ref, lean_obj_arg world) {
    lean_object *value = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(value, 0, lean_st_ref_get(ref));
    return state_result(value, world);
}

LEAN_EXPORT lean_obj_res omega_st_ref_modify(lean_obj_arg ref, lean_obj_arg f, lean_obj_arg world) {
    lean_object *updated = lean_apply_1(f, lean_st_ref_take(ref));
    lean_object *unit = lean_st_ref_put(ref, updated);
    lean_dec(ref);
    return state_result(unit, world);
}
