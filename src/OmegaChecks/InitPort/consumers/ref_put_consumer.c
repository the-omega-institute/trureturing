#include <lean/lean.h>

extern lean_obj_res runtime_initialize_ReferencePutConsumer(uint8_t);
typedef lean_obj_res (*writer)(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_primitive_ref_put(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_lifted_ref_put(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);

static int check(writer put, b_lean_obj_arg ref, b_lean_obj_arg world,
                 const char *old_text, const char *new_text) {
    lean_object *taken = lean_st_ref_take(ref);
    lean_object *expected = lean_mk_string(old_text);
    int valid = lean_string_eq(taken, expected);
    lean_dec_ref(expected);
    lean_dec_ref(taken);
    lean_inc_ref(ref);
    lean_inc_ref(world);
    lean_object *out = put(lean_box(0), lean_box(0), ref, lean_mk_string(new_text), world);
    valid = valid && lean_obj_tag(out) == 0 && lean_ctor_get(out, 0) == lean_box(0) &&
            lean_ctor_get(out, 1) == world;
    lean_dec_ref(out);
    lean_object *stored = lean_st_ref_get(ref);
    expected = lean_mk_string(new_text);
    valid = valid && lean_string_eq(stored, expected);
    lean_dec_ref(expected);
    lean_dec_ref(stored);
    return valid;
}

int main(void) {
    lean_object *init = runtime_initialize_ReferencePutConsumer(1);
    if (lean_io_result_is_error(init)) return 1;
    lean_dec_ref(init);
    lean_io_mark_end_initialization();
    lean_object *world = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(world, 0, lean_box(0));
    lean_object *ref = lean_st_mk_ref(lean_mk_string("initial"));
    int valid = check(omega_test_primitive_ref_put, ref, world, "initial", "primitive") &&
                check(omega_test_lifted_ref_put, ref, world, "primitive", "lifted");
    lean_dec_ref(ref);
    lean_dec_ref(world);
    return valid ? 0 : 2;
}
