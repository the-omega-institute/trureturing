#include <lean/lean.h>
extern int puts(const char *);
extern lean_obj_res runtime_initialize_StateRefConsumer(uint8_t);
extern lean_obj_res omega_state_ref_write(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_state_ref_swap(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_state_ref_new(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);

int main(void) {
    lean_object *status = runtime_initialize_StateRefConsumer(1);
    if (lean_io_result_is_error(status)) return 1;
    lean_dec(status);
    lean_io_mark_end_initialization();
    lean_object *type = lean_box(0), *world = lean_box(9);
    lean_object *out = omega_state_ref_new(type, type, lean_box(11), world);
    lean_object *ref = lean_ctor_get(out, 0);
    lean_inc(ref);
    lean_inc(ref);
    lean_dec(out);
    out = omega_state_ref_write(type, type, lean_mk_string("updated"), ref, world);
    if (lean_ctor_get(out, 1) != world || lean_ctor_get(out, 0) != lean_box(0)) return 2;
    lean_dec(out);
    out = omega_state_ref_swap(type, type, lean_box(13), ref, world);
    lean_object *expected = lean_mk_string("updated");
    if (lean_ctor_get(out, 1) != world || !lean_string_eq(lean_ctor_get(out, 0), expected)) return 3;
    lean_dec(expected);
    lean_dec(out);
    puts("Strict StateRefT' setter updated its underlying reference and preserved the world");
    return 0;
}
