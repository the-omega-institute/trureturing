#include "strict_byte_array.h"

LEAN_EXPORT lean_obj_res omega_byte_array_mk(lean_obj_arg list) {
    size_t size = 0;
    for (lean_object *xs = list; !lean_is_scalar(xs); xs = lean_ctor_get(xs, 1)) ++size;
    return omega_bytes_make(list, size, size, 0);
}

LEAN_EXPORT lean_obj_res omega_byte_array_empty(b_lean_obj_arg requested) {
    lean_object *array = lean_mk_empty_byte_array(requested);
    size_t capacity = lean_sarray_capacity(array);
    lean_dec_ref(array);
    return omega_bytes_make(lean_box(0), 0, capacity, 0);
}

LEAN_EXPORT lean_obj_res omega_byte_array_push(lean_obj_arg bytes, lean_obj_arg byte) {
    lean_object *alias;
    lean_object *native = omega_bytes_native_owner(bytes, &alias);
    uintptr_t original = (uintptr_t)native;
    native = lean_byte_array_push(native, lean_uint8_of_nat(byte));
    lean_dec(byte);
    if (alias) lean_dec_ref(alias);
    lean_object *out = omega_bytes_finish_update(bytes, original, native);
    lean_dec_ref(native);
    return out;
}
