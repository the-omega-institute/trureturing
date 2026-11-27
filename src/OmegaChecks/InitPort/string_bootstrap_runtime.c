#include "strict_string.h"

static lean_obj_res omega_take_string(lean_obj_arg native) {
    lean_object *result = omega_string_from_lean(native);
    lean_dec(native);
    return result;
}

LEAN_EXPORT lean_obj_res omega_string_push(lean_obj_arg bytes, lean_obj_arg scalar) {
    lean_object *alias;
    lean_object *s = omega_string_take_native(bytes, &alias);
    uint32_t c = lean_uint32_of_nat(scalar);
    lean_dec(scalar);
    s = lean_string_push(s, c);
    if (alias) lean_dec_ref(alias);
    return omega_take_string(s);
}

LEAN_EXPORT lean_obj_res omega_string_length(b_lean_obj_arg bytes) {
    lean_object *s = omega_string_to_lean(bytes);
    lean_object *length = lean_string_length(s);
    lean_dec(s);
    return length;
}

LEAN_EXPORT lean_obj_res omega_string_append(lean_obj_arg left, b_lean_obj_arg right) {
    lean_object *alias;
    lean_object *a = omega_string_take_native(left, &alias);
    lean_object *b = omega_string_to_lean(right);
    lean_object *joined = lean_string_append(a, b);
    if (alias) lean_dec_ref(alias);
    lean_dec(b);
    return omega_take_string(joined);
}

LEAN_EXPORT lean_obj_res omega_string_extract(b_lean_obj_arg bytes, b_lean_obj_arg start, b_lean_obj_arg stop) {
    lean_object *s = omega_string_to_lean(bytes);
    lean_object *slice = lean_string_utf8_extract(s, start, stop);
    lean_dec(s);
    return omega_take_string(slice);
}
