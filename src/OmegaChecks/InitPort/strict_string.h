#pragma once
#include "strict_byte_array.h"

/* Field zero is the public UTF-8 byte projection. The extra byte records linearity. */
static lean_obj_res omega_string_wrap(lean_obj_arg bytes, uint8_t marked) {
    lean_object *text = lean_alloc_ctor(0, 1, 1);
    lean_ctor_set(text, 0, bytes);
    lean_ctor_set_uint8(text, sizeof(void *), marked);
    return text;
}

static lean_obj_res omega_string_to_lean(b_lean_obj_arg text) {
    lean_object *array = omega_bytes_to_lean(lean_ctor_get(text, 0));
    lean_object *s = lean_mk_string_from_bytes_unchecked((const char *)lean_sarray_cptr(array), lean_sarray_size(array));
    lean_dec(array);
    if (lean_ctor_get_uint8(text, sizeof(void *))) s = lean_string_mark_linear(s);
    return s;
}

static lean_obj_res omega_string_from_lean(b_lean_obj_arg s) {
    lean_object *bytes = omega_bytes_from_data((const unsigned char *)lean_string_cstr(s), lean_string_size(s) - 1);
    return omega_string_wrap(bytes, lean_string_is_marked_linear(s));
}

/* Native operations receiving an owned argument must observe the strict reference's exclusivity. */
static lean_obj_res omega_string_take_native(lean_obj_arg text, lean_object **alias) {
    lean_object *native = omega_string_to_lean(text);
    *alias = NULL;
    if (!lean_is_exclusive(text)) {
        lean_inc(native);
        *alias = native;
    }
    lean_dec(text);
    return native;
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

static lean_obj_res omega_char_from_lean(b_lean_obj_arg value) {
    return lean_uint32_to_nat(lean_unbox_uint32(value));
}

static lean_obj_res omega_char_to_lean(b_lean_obj_arg value) {
    return lean_box_uint32(lean_uint32_of_nat(value));
}

static lean_obj_res omega_map_list(b_lean_obj_arg values, lean_obj_res (*convert)(b_lean_obj_arg)) {
    lean_object *head = lean_box(0), *last = NULL;
    while (!lean_is_scalar(values)) {
        lean_object *cell = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(cell, 0, convert(lean_ctor_get(values, 0)));
        lean_ctor_set(cell, 1, lean_box(0));
        if (last) lean_ctor_set(last, 1, cell);
        else head = cell;
        last = cell;
        values = lean_ctor_get(values, 1);
    }
    return head;
}

static lean_obj_res omega_string_list_to_lean(b_lean_obj_arg strings) {
    return omega_map_list(strings, omega_string_to_lean);
}

static lean_obj_res omega_char_array_to_lean(b_lean_obj_arg chars) {
    lean_object *array = lean_mk_empty_array();
    for (; !lean_is_scalar(chars); chars = lean_ctor_get(chars, 1))
        array = lean_array_push(array, omega_char_to_lean(lean_ctor_get(chars, 0)));
    return array;
}

static lean_obj_res omega_char_array_from_lean(b_lean_obj_arg array) {
    lean_object *out = lean_box(0);
    for (size_t i = lean_array_size(array); i > 0; --i) {
        lean_object *cell = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(cell, 0, omega_char_from_lean(lean_array_get_core(array, i - 1)));
        lean_ctor_set(cell, 1, out);
        out = cell;
    }
    return out;
}

/* The pinned Name printer applies its strict token predicate to assembled native text. */
static lean_obj_res omega_name_token(lean_obj_arg predicate, lean_obj_arg native) {
    lean_object *s = omega_string_from_lean(native);
    lean_dec(native);
    return lean_apply_1(predicate, s);
}

static lean_obj_res omega_optional_from_lean(lean_obj_arg value, lean_obj_res (*convert)(b_lean_obj_arg)) {
    if (lean_is_scalar(value)) return value;
    lean_object *result = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(result, 0, convert(lean_ctor_get(value, 0)));
    lean_dec(value);
    return result;
}

static lean_obj_res omega_string_map_char(lean_obj_arg fn, lean_obj_arg c) {
    lean_object *arg = omega_char_from_lean(c);
    lean_dec(c);
    lean_object *mapped = lean_apply_1(fn, arg);
    lean_object *result = omega_char_to_lean(mapped);
    lean_dec(mapped);
    return result;
}

static lean_obj_res omega_string_predicate(lean_obj_arg f, lean_obj_arg c) {
    uint32_t scalar = lean_unbox_uint32(c);
    lean_dec(c);
    return lean_apply_1(f, lean_uint32_to_nat(scalar));
}

static lean_obj_res omega_raw_fold_left(lean_obj_arg f, lean_obj_arg acc, lean_obj_arg c) {
    lean_object *scalar = omega_char_from_lean(c);
    lean_dec(c);
    return lean_apply_2(f, acc, scalar);
}

static lean_obj_res omega_raw_fold_right(lean_obj_arg f, lean_obj_arg c, lean_obj_arg acc) {
    lean_object *scalar = omega_char_from_lean(c);
    lean_dec(c);
    return lean_apply_2(f, scalar, acc);
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

static inline lean_obj_res omega_substring_from_lean(b_lean_obj_arg slice) {
    return omega_convert_substring(slice, omega_string_from_lean);
}

static inline lean_obj_res omega_slice_to_lean(b_lean_obj_arg slice) {
    return omega_convert_substring(slice, omega_string_to_lean);
}

/* Pinned Char boxes UInt32, while strict Char carries a physical Nat. */
static inline lean_obj_res omega_convert_char_list(b_lean_obj_arg chars, bool to_native) {
    lean_object *head = lean_box(0);
    lean_object *last = NULL;
    for (; !lean_is_scalar(chars); chars = lean_ctor_get(chars, 1)) {
        lean_object *ch = lean_ctor_get(chars, 0);
        lean_object *next = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(next, 0, to_native ? lean_box_uint32(lean_uint32_of_nat(ch))
                                        : lean_uint32_to_nat(lean_unbox_uint32(ch)));
        lean_ctor_set(next, 1, lean_box(0));
        if (last == NULL) head = next;
        else lean_ctor_set(last, 1, next);
        last = next;
    }
    return head;
}
