#pragma once
#include <lean/lean.h>

/* A strict FloatArray erases to List Float. Each Float erases to its IEEE bits as a Nat. */
static b_lean_obj_arg omega_float_list_at(b_lean_obj_arg xs, b_lean_obj_arg index) {
    if (!lean_is_scalar(index)) return lean_box(0);
    size_t i = lean_unbox(index);
    while (i && !lean_is_scalar(xs)) {
        xs = lean_ctor_get(xs, 1);
        --i;
    }
    return xs;
}

static lean_obj_res omega_float_list_get(b_lean_obj_arg xs, b_lean_obj_arg index) {
    b_lean_obj_arg cell = omega_float_list_at(xs, index);
    if (lean_is_scalar(cell)) return lean_box(0);
    lean_obj_res value = lean_ctor_get(cell, 0);
    lean_inc(value);
    return value;
}

static lean_obj_res omega_float_list_set(lean_obj_arg xs, b_lean_obj_arg index, lean_obj_arg value) {
    /* The pinned scalar-array primitive returns the very same array for out-of-bounds indices. */
    if (lean_is_scalar(omega_float_list_at(xs, index))) {
        lean_dec(value);
        return xs;
    }
    size_t i = lean_unbox(index);
    lean_obj_res result = NULL, last = NULL;
    for (;;) {
        lean_object *next = lean_ctor_get(xs, 1);
        lean_object *cell = xs;
        if (!lean_is_exclusive(xs)) {
            lean_inc(next);
            cell = lean_alloc_ctor(1, 2, 0);
            if (i) {
                lean_object *head = lean_ctor_get(xs, 0);
                lean_inc(head);
                lean_ctor_set(cell, 0, head);
            }
            lean_dec_ref(xs);
        } else if (!i) {
            lean_dec(lean_ctor_get(cell, 0));
        }
        if (last) lean_ctor_set(last, 1, cell);
        else result = cell;
        if (!i) {
            lean_ctor_set(cell, 0, value);
            lean_ctor_set(cell, 1, next);
            return result;
        }
        last = cell;
        xs = next;
        --i;
    }
}
