#pragma once
#include "strict_nat.h"

/* The strict String data field erases to a list of unary UTF-8 bytes. */
static lean_obj_res omega_string_to_lean(b_lean_obj_arg bytes) {
    lean_object *array = lean_mk_empty_byte_array(lean_box(0));
    while (!lean_is_scalar(bytes)) {
        b_lean_obj_arg byte = lean_ctor_get(bytes, 0);
        uint8_t value = 0;
        while (!lean_is_scalar(byte)) {
            ++value;
            byte = lean_ctor_get(byte, 0);
        }
        array = lean_byte_array_push(array, value);
        bytes = lean_ctor_get(bytes, 1);
    }
    lean_object *s = lean_mk_string_from_bytes_unchecked((const char *)lean_sarray_cptr(array), lean_sarray_size(array));
    lean_dec(array);
    return s;
}

static lean_obj_res omega_string_from_lean(b_lean_obj_arg s) {
    const unsigned char *chars = (const unsigned char *)lean_string_cstr(s);
    lean_object *bytes = lean_box(0);
    for (size_t i = lean_string_size(s) - 1; i > 0; --i) {
        lean_object *cell = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(cell, 0, omega_nat_from_uint64(chars[i - 1]));
        lean_ctor_set(cell, 1, bytes);
        bytes = cell;
    }
    return bytes;
}
