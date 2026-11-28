#pragma once
#include "sep_array.h"

/* The result of the native loop is converted before it reaches the original pure. */
static lean_obj_res omega_array_map_pure(lean_obj_arg pure, lean_obj_arg slots,
        lean_obj_arg original, lean_obj_arg type, lean_obj_arg values) {
    size_t size = lean_array_size(values);
    bool reuse = (uintptr_t)values == lean_unbox_usize(original) && lean_is_exclusive(slots);
    lean_dec(original);
    lean_object *tail = lean_box(0);
    for (size_t i = size; i > 0; --i) {
        lean_object *value = lean_array_get_core(values, i - 1);
        lean_inc(value);
        lean_object *cell = reuse ? lean_array_get_core(slots, i - 1) : lean_box(0);
        if (lean_is_scalar(cell)) cell = lean_alloc_ctor(1, 2, 0);
        else lean_array_set_core(slots, i - 1, lean_box(0));
        lean_ctor_set(cell, 0, value);
        lean_ctor_set(cell, 1, tail);
        tail = cell;
    }
    lean_dec(slots);
    lean_dec(values);
    return lean_apply_2(pure, type, tail);
}

/* Transfer input elements to the pinned array loop. Empty unique cells can be
   reused upon return whenever the pinned loop retains its input array. */
static lean_obj_res omega_array_map_prepare(lean_obj_arg monad, lean_obj_arg input,
        lean_object **converted) {
    size_t size = 0;
    for (lean_object *xs = input; !lean_is_scalar(xs); xs = lean_ctor_get(xs, 1)) ++size;
    lean_object *values = lean_alloc_array(size, size);
    lean_object *slots = lean_alloc_array(size, size);
    for (size_t i = 0; i < size; ++i) {
        lean_object *value = lean_ctor_get(input, 0);
        lean_object *tail = lean_ctor_get(input, 1);
        if (lean_is_exclusive(input)) {
            lean_ctor_set(input, 0, lean_box(0));
            lean_ctor_set(input, 1, lean_box(0));
            lean_array_set_core(slots, i, input);
        } else {
            lean_inc(value);
            lean_inc(tail);
            lean_dec(input);
            lean_array_set_core(slots, i, lean_box(0));
        }
        lean_array_set_core(values, i, value);
        input = tail;
    }
    lean_object *pure = lean_alloc_closure((void *)omega_array_map_pure, 5, 3);
    lean_object *original_pure = lean_ctor_get(lean_ctor_get(monad, 0), 1);
    lean_inc(original_pure);
    lean_closure_set(pure, 0, original_pure);
    lean_closure_set(pure, 1, slots);
    lean_closure_set(pure, 2, lean_box_usize((uintptr_t)values));
    lean_object *out = omega_array_with_pure(monad, pure);
    lean_dec(monad);
    *converted = values;
    return out;
}
