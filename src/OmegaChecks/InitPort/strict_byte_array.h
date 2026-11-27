#pragma once
#include "strict_nat.h"

/* Strict ByteArray.data erases to a list of UInt8 represented by bounded Nat values. */
static inline size_t omega_bytes_size(b_lean_obj_arg bytes) {
    size_t length = 0;
    for (; !lean_is_scalar(bytes); bytes = lean_ctor_get(bytes, 1)) ++length;
    return length;
}

static lean_obj_res omega_bytes_to_lean(b_lean_obj_arg bytes) {
    size_t length = omega_bytes_size(bytes);
    lean_object *array = lean_alloc_sarray(1, length, length);
    uint8_t *data = lean_sarray_cptr(array);
    for (size_t i = 0; i < length; ++i, bytes = lean_ctor_get(bytes, 1))
        data[i] = lean_unbox(lean_ctor_get(bytes, 0));
    return array;
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
