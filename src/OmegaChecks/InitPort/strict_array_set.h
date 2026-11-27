#pragma once
#include <lean/lean.h>

static b_lean_obj_arg omega_array_list_at(b_lean_obj_arg xs, b_lean_obj_arg index) {
    if (!lean_is_scalar(index)) return lean_box(0);
    size_t i = lean_unbox(index);
    while (i && !lean_is_scalar(xs)) {
        xs = lean_ctor_get(xs, 1);
        --i;
    }
    return xs;
}

/* Update a known in-bounds element in the list representation of a strict array. */
static lean_obj_res omega_array_list_set_at(lean_obj_arg xs, size_t i, lean_obj_arg value) {
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

static lean_obj_res omega_array_list_set_bang(lean_obj_arg xs, b_lean_obj_arg index, lean_obj_arg value) {
    if (lean_is_scalar(omega_array_list_at(xs, index))) {
        /* Let the pinned runtime report the bounds error and consume the rejected value. */
        lean_dec(lean_array_set_panic(lean_mk_empty_array(), value));
        return xs;
    }
    return omega_array_list_set_at(xs, lean_unbox(index), value);
}

/* Apply the callback in index order. Keep the untouched suffix and copy a shared
   prefix only when an element changes its pointer. */
static lean_obj_res omega_array_list_map_mono(lean_obj_arg xs, lean_obj_arg f) {
    lean_object *result = xs, *pending = xs, *last = NULL;
    lean_object *scan = xs;
    while (!lean_is_scalar(scan)) {
        lean_object *old = lean_ctor_get(scan, 0);
        lean_object *following = lean_ctor_get(scan, 1);
        lean_inc(old);
        lean_inc(f);
        lean_object *mapped = lean_apply_1(f, old);
        if (mapped == old) {
            lean_dec(mapped);
        } else {
            for (;;) {
                bool changed = pending == scan;
                lean_object *cell = pending, *next = lean_ctor_get(pending, 1);
                if (!lean_is_exclusive(pending)) {
                    cell = lean_alloc_ctor(1, 2, 0);
                    lean_inc(next);
                    lean_ctor_set(cell, 1, next);
                    if (!changed) {
                        lean_object *head = lean_ctor_get(pending, 0);
                        lean_inc(head);
                        lean_ctor_set(cell, 0, head);
                    }
                    lean_dec_ref(pending);
                } else if (changed) {
                    lean_dec(lean_ctor_get(cell, 0));
                }
                if (last) lean_ctor_set(last, 1, cell);
                else result = cell;
                last = cell;
                pending = next;
                if (changed) {
                    lean_ctor_set(cell, 0, mapped);
                    break;
                }
            }
        }
        scan = following;
    }
    lean_dec(f);
    return result;
}
