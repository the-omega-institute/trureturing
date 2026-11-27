#pragma once
#include "strict_array_set.h"

/* A strict FloatArray erases to List Float. Each Float erases to its IEEE bits as a Nat. */
static lean_obj_res omega_float_list_get(b_lean_obj_arg xs, b_lean_obj_arg index) {
    b_lean_obj_arg cell = omega_array_list_at(xs, index);
    if (lean_is_scalar(cell)) return lean_box(0);
    lean_obj_res value = lean_ctor_get(cell, 0);
    lean_inc(value);
    return value;
}

static lean_obj_res omega_float_list_set(lean_obj_arg xs, b_lean_obj_arg index, lean_obj_arg value) {
    /* The pinned scalar-array primitive returns the very same array for out-of-bounds indices. */
    if (lean_is_scalar(omega_array_list_at(xs, index))) {
        lean_dec(value);
        return xs;
    }
    return omega_array_list_set_at(xs, lean_unbox(index), value);
}

/* The public FloatArray.data projection reads slot zero. New boxed owners reserve the
   remaining two words and byte for length, capacity, and the linearity marker. */
#ifndef LEAN_EMSCRIPTEN
extern char *getenv(const char *name);
#endif
static inline size_t omega_float_array_length(b_lean_obj_arg xs) {
    return lean_ctor_get_usize(xs, 1);
}
static inline size_t omega_float_array_capacity(b_lean_obj_arg xs) {
    return lean_ctor_get_usize(xs, 2);
}
static inline uint8_t omega_float_array_marked(b_lean_obj_arg xs) {
    return lean_ctor_get_uint8(xs, sizeof(void *) * 3);
}
static lean_obj_res omega_float_array_make(lean_obj_arg data, size_t len, size_t capacity, uint8_t marked) {
    lean_object *xs = lean_alloc_ctor(0, 1, 2 * sizeof(size_t) + 1);
    lean_ctor_set(xs, 0, data);
    lean_ctor_set_usize(xs, 1, len);
    lean_ctor_set_usize(xs, 2, capacity);
    lean_ctor_set_uint8(xs, sizeof(void *) * 3, marked);
    return xs;
}
static lean_obj_res omega_float_array_wrap_list(lean_obj_arg data) {
    size_t len = 0;
    for (lean_object *xs = data; !lean_is_scalar(xs); xs = lean_ctor_get(xs, 1)) ++len;
    return omega_float_array_make(data, len, len, 0);
}
static lean_obj_res omega_float_array_empty(b_lean_obj_arg cap) {
    if (!lean_is_scalar(cap) || lean_alloc_sarray_would_overflow(sizeof(double), lean_unbox(cap)))
        lean_internal_panic_out_of_memory();
    return omega_float_array_make(lean_box(0), 0, lean_unbox(cap), 0);
}
static lean_obj_res omega_float_array_unique(lean_obj_arg xs, size_t capacity) {
    const bool unique = lean_is_exclusive(xs);
    if (unique && capacity == omega_float_array_capacity(xs)) return xs;
    uint8_t marked = omega_float_array_marked(xs);
#ifndef LEAN_EMSCRIPTEN
    if (!unique && marked && getenv("LEAN_ABORT_ON_NONLINEAR"))
        lean_internal_panic("scalar array marked by `markLinear` was used non-linearly");
#endif
    lean_object *data = lean_ctor_get(xs, 0);
    lean_inc(data);
    lean_obj_res dst = omega_float_array_make(data, omega_float_array_length(xs), capacity, marked);
    lean_dec_ref(xs);
    return dst;
}
static lean_obj_res omega_float_array_mark(lean_obj_arg xs) {
    xs = omega_float_array_unique(xs, omega_float_array_capacity(xs));
    lean_ctor_set_uint8(xs, sizeof(void *) * 3, 1);
    return xs;
}
static lean_obj_res omega_float_array_propagate(b_lean_obj_arg src, lean_obj_arg dst) {
    return omega_float_array_marked(src) ? omega_float_array_mark(dst) : dst;
}
static lean_obj_res omega_float_array_set(lean_obj_arg xs, b_lean_obj_arg i, lean_obj_arg value) {
    if (!lean_is_scalar(i) || lean_unbox(i) >= omega_float_array_length(xs)) {
        lean_dec(value);
        return xs;
    }
    xs = omega_float_array_unique(xs, omega_float_array_capacity(xs));
    lean_ctor_set(xs, 0, omega_float_list_set(lean_ctor_get(xs, 0), i, value));
    return xs;
}
static lean_obj_res omega_float_array_uset(lean_obj_arg xs, lean_obj_arg i, lean_obj_arg value) {
    lean_obj_res result = omega_float_array_set(xs, i, value);
    lean_dec(i);
    return result;
}
static lean_obj_res omega_float_array_push(lean_obj_arg xs, lean_obj_arg value) {
    const size_t len = omega_float_array_length(xs) + 1;
    size_t cap = omega_float_array_capacity(xs);
    if (len > cap) cap = lean_usize_mul_checked(len, 2);
    xs = omega_float_array_unique(xs, cap);
    lean_object *tail = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(tail, 0, value);
    lean_ctor_set(tail, 1, lean_box(0));
    lean_object *old = lean_ctor_get(xs, 0), *prev = xs;
    unsigned field = 0;
    while (!lean_is_scalar(old)) {
        lean_object *cell = old, *next = lean_ctor_get(old, 1);
        if (!lean_is_exclusive(old)) {
            cell = lean_alloc_ctor(1, 2, 0);
            lean_object *head = lean_ctor_get(old, 0);
            lean_inc(head);
            lean_inc(next);
            lean_ctor_set(cell, 0, head);
            lean_dec_ref(old);
        }
        lean_ctor_set(prev, field, cell);
        prev = cell;
        field = 1;
        old = next;
    }
    lean_ctor_set(prev, field, tail);
    lean_ctor_set_usize(xs, 1, len);
    return xs;
}
