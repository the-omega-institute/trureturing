#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_obj_res runtime_initialize_EffectRunConsumer(uint8_t);
extern lean_obj_res omega_effect_readers(lean_obj_arg);
extern lean_obj_res omega_effect_base(lean_obj_arg);
extern lean_obj_res omega_effect_eio(lean_obj_arg);
extern lean_obj_res omega_effect_io(lean_obj_arg);
extern lean_obj_res omega_effect_eio_error(lean_obj_arg);
extern lean_obj_res omega_effect_io_error(lean_obj_arg);

static int check_result(lean_obj_arg result, unsigned tag, b_lean_obj_arg value) {
    int ok = !lean_is_scalar(result) && lean_obj_tag(result) == tag && lean_ctor_get(result, 0) == value;
    lean_dec(result);
    return ok;
}

static int check_reads(b_lean_obj_arg readers, b_lean_obj_arg value) {
    lean_inc(readers);
    lean_object *base = omega_effect_base(readers);
    int ok = base == value;
    lean_dec(base);
    lean_inc(readers);
    ok &= check_result(omega_effect_eio(readers), 1, value);
    lean_inc(readers);
    return check_result(omega_effect_io(readers), 1, value) && ok;
}

int main(void) {
    lean_initialize_runtime_module();
    lean_object *init = runtime_initialize_EffectRunConsumer(1);
    if (lean_io_result_is_error(init)) return 1;
    lean_dec_ref(init);
    lean_io_mark_end_initialization();

    lean_object *cell = lean_st_mk_ref(lean_box(17));
    lean_inc_ref(cell);
    lean_object *readers = omega_effect_readers(cell);
    int ok = check_reads(readers, lean_box(17));
    lean_dec(lean_st_ref_swap(cell, lean_box(42)));
    ok &= check_reads(readers, lean_box(42));
    lean_dec_ref(readers);
    lean_dec_ref(cell);
    ok &= check_result(omega_effect_eio_error(lean_box(37)), 0, lean_box(37));
    lean_object *err = lean_mk_io_user_error(lean_mk_string("effect runner"));
    lean_inc_ref(err);
    ok &= check_result(omega_effect_io_error(err), 0, err);
    lean_dec_ref(err);
    return ok ? 0 : 2;
}
