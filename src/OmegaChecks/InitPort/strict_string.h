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

/* Convert the string field while preserving both byte offsets. The caller owns the new record. */
static lean_obj_res omega_convert_substring(b_lean_obj_arg slice, lean_obj_res (*convert)(b_lean_obj_arg)) {
    lean_object *result = lean_alloc_ctor(0, 3, 0);
    lean_ctor_set(result, 0, convert(lean_ctor_get(slice, 0)));
    for (unsigned i = 1; i < 3; ++i) {
        lean_object *offset = lean_ctor_get(slice, i);
        lean_inc(offset);
        lean_ctor_set(result, i, offset);
    }
    return result;
}

static lean_obj_res omega_string_list_to_lean(b_lean_obj_arg strings) {
    lean_object *head = lean_box(0), *last = NULL;
    while (!lean_is_scalar(strings)) {
        lean_object *cell = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(cell, 0, omega_string_to_lean(lean_ctor_get(strings, 0)));
        lean_ctor_set(cell, 1, lean_box(0));
        if (last) lean_ctor_set(last, 1, cell);
        else head = cell;
        last = cell;
        strings = lean_ctor_get(strings, 1);
    }
    return head;
}

static lean_obj_res omega_string_predicate(lean_obj_arg f, lean_obj_arg c) {
    uint32_t scalar = lean_unbox_uint32(c);
    lean_dec(c);
    return lean_apply_1(f, lean_uint32_to_nat(scalar));
}

static lean_obj_res omega_string_fold_step(lean_obj_arg f, lean_obj_arg s, lean_obj_arg c) {
    lean_object *bytes = omega_string_from_lean(s);
    uint32_t scalar = lean_unbox_uint32(c);
    lean_dec(s);
    lean_dec(c);
    lean_object *updated = lean_apply_2(f, bytes, lean_uint32_to_nat(scalar));
    lean_object *result = omega_string_to_lean(updated);
    lean_dec(updated);
    return result;
}

static inline lean_obj_res omega_slice_to_lean(b_lean_obj_arg slice) {
    return omega_convert_substring(slice, omega_string_to_lean);
}
