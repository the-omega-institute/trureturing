#include <lean/lean.h>
extern int puts(const char *);
extern void exit(int);
extern lean_obj_res runtime_initialize_ReferenceConsumer(uint8_t);
extern lean_obj_res omega_ref_smoke(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_ref_swap_smoke(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_ref_set_smoke(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_ref_equal_smoke(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);

static lean_obj_res result(lean_obj_arg out, lean_obj_arg world) {
    if (lean_ctor_get(out, 1) != world) exit(2);
    lean_obj_res value = lean_ctor_get(out, 0);
    lean_inc(value);
    lean_dec(out);
    return value;
}

int main(void) {
    lean_object *status = runtime_initialize_ReferenceConsumer(1);
    if (lean_io_result_is_error(status)) return 1;
    lean_dec(status);
    lean_io_mark_end_initialization();
    lean_object *world = lean_box(12), *type = lean_box(0);
    lean_object *first = result(omega_ref_smoke(type, type, lean_mk_string("initial"), world), world);
    lean_object *second = result(omega_ref_smoke(type, type, lean_box(15), world), world);
    lean_inc(first);
    lean_inc(second);
    if (result(omega_ref_equal_smoke(type, type, first, second, world), world) != lean_box(0)) return 3;
    lean_inc(first);
    lean_inc(first);
    if (result(omega_ref_equal_smoke(type, type, first, first, world), world) != lean_box(1)) return 4;
    lean_inc(first);
    lean_object *old = result(omega_ref_swap_smoke(type, type, first, lean_box(3), world), world);
    lean_object *expected = lean_mk_string("initial");
    if (!lean_string_eq(old, expected)) return 5;
    lean_dec(old);
    lean_dec(expected);
    lean_inc(first);
    if (result(omega_ref_set_smoke(type, type, first, lean_box(11), world), world) != lean_box(0)) return 6;
    if (result(omega_ref_swap_smoke(type, type, first, lean_box(7), world), world) != lean_box(11)) return 7;
    if (result(omega_ref_swap_smoke(type, type, second, lean_box(9), world), world) != lean_box(15)) return 8;
    puts("Strict ST.Ref allocation, identity, writing, swapping and world preservation passed");
    return 0;
}
