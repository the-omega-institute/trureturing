#pragma once
#include "strict_nat.h"

/* Field zero carries the public strict Array UInt8. The scalar fields carry the
   packed buffer's length, capacity and linearity. */
static inline size_t omega_bytes_size(b_lean_obj_arg bytes) {
    return lean_ctor_get_usize(bytes, 1);
}

static inline lean_obj_res omega_bytes_make(lean_obj_arg list, size_t size, size_t capacity, uint8_t marked) {
    lean_object *bytes = lean_alloc_ctor(0, 1, 2 * sizeof(size_t) + 1);
    lean_ctor_set(bytes, 0, list);
    lean_ctor_set_usize(bytes, 1, size);
    lean_ctor_set_usize(bytes, 2, capacity);
    lean_ctor_set_uint8(bytes, 3 * sizeof(void *), marked);
    return bytes;
}

static lean_obj_res omega_bytes_to_lean(b_lean_obj_arg bytes) {
    size_t length = omega_bytes_size(bytes);
    lean_object *array = lean_alloc_sarray(1, length, lean_ctor_get_usize(bytes, 2));
    uint8_t *data = lean_sarray_cptr(array);
    lean_object *xs = lean_ctor_get(bytes, 0);
    for (size_t i = 0; i < length; ++i, xs = lean_ctor_get(xs, 1)) data[i] = lean_unbox(lean_ctor_get(xs, 0));
    if (lean_ctor_get_uint8(bytes, 3 * sizeof(void *))) lean_sarray_mark_linear_core(array);
    return array;
}

static lean_obj_res omega_bytes_native_owner(b_lean_obj_arg bytes, lean_object **alias) {
    lean_object *array = omega_bytes_to_lean(bytes);
    *alias = NULL;
    if (!lean_is_exclusive(bytes)) {
        lean_inc_ref(array);
        *alias = array;
    }
    return array;
}

static lean_obj_res omega_bytes_take_native(lean_obj_arg bytes, lean_object **alias) {
    lean_object *array = omega_bytes_native_owner(bytes, alias);
    lean_dec_ref(bytes);
    return array;
}

static lean_obj_res omega_bytes_list(const unsigned char *data, size_t length) {
    lean_object *xs = lean_box(0);
    for (size_t i = length; i > 0; --i) {
        lean_object *cell = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(cell, 0, lean_box(data[i - 1]));
        lean_ctor_set(cell, 1, xs);
        xs = cell;
    }
    return xs;
}

static lean_obj_res omega_bytes_from_data(const unsigned char *data, size_t length) {
    return omega_bytes_make(omega_bytes_list(data, length), length, length, 0);
}

static lean_obj_res omega_bytes_from_lean(b_lean_obj_arg array) {
    size_t length = lean_sarray_size(array);
    return omega_bytes_make(omega_bytes_list(lean_sarray_cptr(array), length), length,
                            lean_sarray_capacity(array), lean_sarray_is_marked_linear(array));
}

/* Preserve observable identity when the packed primitive returns its input. A shared
   input returned unchanged needs no field updates. A unique input can be updated in place. */
static lean_obj_res omega_bytes_finish_update(lean_obj_arg bytes, uintptr_t original, b_lean_obj_arg native) {
    if ((uintptr_t)native != original) {
        lean_object *out = omega_bytes_from_lean(native);
        lean_dec_ref(bytes);
        return out;
    }
    if (lean_is_exclusive(bytes)) {
        size_t size = lean_sarray_size(native);
        lean_dec(lean_ctor_get(bytes, 0));
        lean_ctor_set(bytes, 0, omega_bytes_list(lean_sarray_cptr(native), size));
        lean_ctor_set_usize(bytes, 1, size);
        lean_ctor_set_usize(bytes, 2, lean_sarray_capacity(native));
        lean_ctor_set_uint8(bytes, 3 * sizeof(void *), lean_sarray_is_marked_linear(native));
    }
    return bytes;
}

/* The pinned string conversions produce an unmarked byte buffer with exact capacity. */
static lean_obj_res omega_bytes_fresh(b_lean_obj_arg bytes) {
    lean_object *data = lean_ctor_get(bytes, 0);
    lean_inc(data);
    size_t size = omega_bytes_size(bytes);
    return omega_bytes_make(data, size, size, 0);
}

static lean_obj_res omega_bytes_mark(lean_obj_arg bytes) {
    if (lean_is_exclusive(bytes)) {
        lean_ctor_set_uint8(bytes, 3 * sizeof(void *), 1);
        return bytes;
    }
    lean_object *alias;
    lean_object *native = omega_bytes_take_native(bytes, &alias);
    native = lean_sarray_mark_linear(native);
    lean_dec_ref(alias);
    lean_object *result = omega_bytes_from_lean(native);
    lean_dec_ref(native);
    return result;
}
