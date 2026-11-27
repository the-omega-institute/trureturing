#include "strict_string.h"
#include "byte_seed.c"

/* Char, UInt32, BitVec and Fin erase to the checked natural representation. */
static uint32_t omega_scalar_value(b_lean_obj_arg n) {
    if (!lean_is_scalar(n)) return 0;
    size_t value = lean_unbox(n);
    if (value > 0x10ffff || (value >= 0xd800 && value <= 0xdfff)) return 0;
    return (uint32_t)value;
}

LEAN_EXPORT lean_obj_res omega_char_of_nat(lean_obj_arg n) {
    uint32_t value = omega_scalar_value(n);
    if (value != 0) return n;
    lean_dec(n);
    return lean_box(0);
}

LEAN_EXPORT lean_obj_res omega_string_of_list(lean_obj_arg chars) {
    lean_object *native = lean_mk_string_unchecked("", 0, 0);
    for (lean_object *cell = chars; !lean_is_scalar(cell); cell = lean_ctor_get(cell, 1)) {
        native = lean_string_push(native, omega_scalar_value(lean_ctor_get(cell, 0)));
    }
    lean_dec(chars);
    lean_object *bytes = omega_string_from_lean(native);
    lean_dec(native);
    return bytes;
}

LEAN_EXPORT lean_obj_res omega_string_byte_size(b_lean_obj_arg bytes) {
    return lean_usize_to_nat(omega_bytes_size(lean_ctor_get(bytes, 0)));
}

LEAN_EXPORT lean_obj_res omega_string_of_bytes(lean_obj_arg bytes) {
    lean_object *copy = omega_bytes_fresh(bytes);
    lean_dec_ref(bytes);
    return omega_string_wrap(copy, 0);
}

LEAN_EXPORT lean_obj_res omega_string_to_bytes(lean_obj_arg text) {
    lean_object *bytes = omega_bytes_fresh(lean_ctor_get(text, 0));
    lean_dec(text);
    return bytes;
}

LEAN_EXPORT uint8_t omega_string_dec_eq(b_lean_obj_arg left, b_lean_obj_arg right) {
    if (left == right) return 1;
    lean_object *a = omega_string_to_lean(left);
    lean_object *b = omega_string_to_lean(right);
    uint8_t equal = lean_string_dec_eq(a, b);
    lean_dec(a);
    lean_dec(b);
    return equal;
}

LEAN_EXPORT lean_obj_res omega_string_hash(b_lean_obj_arg bytes) {
    lean_object *native = omega_string_to_lean(bytes);
    uint64_t hash = lean_string_hash(native);
    lean_dec(native);
    return omega_nat_from_uint64(hash);
}

LEAN_EXPORT lean_obj_res omega_panic_core(b_lean_obj_arg fallback, lean_obj_arg message) {
    lean_object *native = omega_string_to_lean(message);
    lean_dec(message);
    return lean_panic_fn_borrowed(fallback, native);
}

LEAN_EXPORT lean_obj_res omega_array_get_bang(b_lean_obj_arg fallback, b_lean_obj_arg xs, b_lean_obj_arg index) {
    if (lean_is_scalar(index)) {
        size_t remaining = lean_unbox(index);
        while (!lean_is_scalar(xs)) {
            if (remaining == 0) {
                lean_object *result = lean_ctor_get(xs, 0);
                lean_inc(result);
                return result;
            }
            --remaining;
            xs = lean_ctor_get(xs, 1);
        }
    }
    lean_inc(fallback);
    return lean_array_get_panic(fallback);
}
