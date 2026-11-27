extern lean_object *l_IO_stdGenRef;

LEAN_EXPORT lean_obj_res omega_std_gen_ref(lean_obj_arg unit) {
    lean_dec(unit);
    lean_inc(l_IO_stdGenRef);
    return l_IO_stdGenRef;
}

extern lean_obj_res l_IO_rand(b_lean_obj_arg lo, b_lean_obj_arg hi);

LEAN_EXPORT lean_obj_res omega_io_rand(lean_obj_arg lo, lean_obj_arg hi, lean_obj_arg world) {
    lean_object *n = l_IO_rand(lo, hi);
    lean_dec(lo);
    lean_dec(hi);
    lean_object *result = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result, 0, n);
    lean_ctor_set(result, 1, world);
    return result;
}
