#include <lean/lean.h>

extern lean_obj_res runtime_initialize_ReferenceModifyConsumer(uint8_t);
extern lean_obj_res omega_test_modify_unsafe(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);

static unsigned callbacks;

static lean_obj_res update(lean_obj_arg value) {
    ++callbacks;
    lean_obj_res expected = lean_mk_string("before");
    int matches = lean_string_eq(value, expected);
    lean_dec_ref(expected);
    lean_dec_ref(value);
    return lean_mk_string(matches ? "after" : "unexpected payload");
}

int main(void) {
    lean_obj_res init = runtime_initialize_ReferenceModifyConsumer(1);
    if (lean_io_result_is_error(init)) return 1;
    lean_dec_ref(init);
    lean_io_mark_end_initialization();
    lean_obj_res ref = lean_st_mk_ref(lean_mk_string("before"));
    lean_inc_ref(ref);
    lean_obj_res world = lean_box(17);
    lean_obj_res result = omega_test_modify_unsafe(lean_box(0), lean_box(0), ref,
        lean_alloc_closure((void *)update, 1, 0), world);
    lean_obj_res stored = lean_st_ref_get(ref);
    lean_obj_res expected = lean_mk_string("after");
    int valid = callbacks == 1 && lean_string_eq(stored, expected) &&
        lean_obj_tag(result) == 0 && lean_ctor_get(result, 0) == lean_box(0) && lean_ctor_get(result, 1) == world;
    lean_dec_ref(result);
    lean_dec_ref(stored);
    lean_dec_ref(expected);
    lean_dec_ref(ref);
    return valid ? 0 : 2;
}
