#pragma once
#include "strict_nat.h"

/* The strict String data field erases to a list of Nat-valued UTF-8 bytes. */
static lean_obj_res omega_bytes_to_lean(b_lean_obj_arg bytes) {
    lean_object *array = lean_mk_empty_byte_array(lean_box(0));
    while (!lean_is_scalar(bytes)) {
        b_lean_obj_arg byte = lean_ctor_get(bytes, 0);
        uint8_t value = lean_unbox(byte);
        array = lean_byte_array_push(array, value);
        bytes = lean_ctor_get(bytes, 1);
    }
    return array;
}

static lean_obj_res omega_string_to_lean(b_lean_obj_arg bytes) {
    lean_object *array = omega_bytes_to_lean(bytes);
    lean_object *s = lean_mk_string_from_bytes_unchecked((const char *)lean_sarray_cptr(array), lean_sarray_size(array));
    lean_dec(array);
    return s;
}

static lean_obj_res omega_bytes_from_data(const unsigned char *chars, size_t length) {
    lean_object *bytes = lean_box(0);
    for (size_t i = length; i > 0; --i) {
        lean_object *cell = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(cell, 0, omega_nat_from_uint64(chars[i - 1]));
        lean_ctor_set(cell, 1, bytes);
        bytes = cell;
    }
    return bytes;
}

static lean_obj_res omega_string_from_lean(b_lean_obj_arg s) {
    return omega_bytes_from_data((const unsigned char *)lean_string_cstr(s), lean_string_size(s) - 1);
}

/* The three physical fields of Slice are the backing string and two byte offsets. */
static inline lean_obj_res omega_slice_to_lean(b_lean_obj_arg slice) {
    lean_object *converted = lean_alloc_ctor(0, 3, 0);
    lean_ctor_set(converted, 0, omega_string_to_lean(lean_ctor_get(slice, 0)));
    for (unsigned field = 1; field <= 2; ++field) {
        lean_object *offset = lean_ctor_get(slice, field);
        lean_inc(offset);
        lean_ctor_set(converted, field, offset);
    }
    return converted;
}
