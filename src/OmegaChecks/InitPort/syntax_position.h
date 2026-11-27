#pragma once
#include <lean/lean.h>

typedef lean_obj_res (*omega_syntax_info_fn)(b_lean_obj_arg);
typedef lean_obj_res (*omega_tail_position_fn)(b_lean_obj_arg, uint8_t);

static lean_obj_res omega_position_pop(lean_object **stack) {
    lean_object *value = lean_array_get_core(*stack, lean_array_size(*stack) - 1);
    lean_inc(value);
    *stack = lean_array_pop(*stack);
    return value;
}

/* The pinned queries inspect source information and traverse the children in source order
   or in reverse order. Query each node using an empty native array, then traverse its
   strict list of children if the pinned query did not find a position at that node. */
static lean_obj_res omega_syntax_position(b_lean_obj_arg syntax, bool reverse, uint8_t canonical,
                                          omega_syntax_info_fn info_query, omega_tail_position_fn tail) {
    lean_inc(syntax);
    lean_object *pending = lean_array_push(lean_mk_empty_array(), syntax);
    while (lean_array_size(pending) != 0) {
        lean_object *current = omega_position_pop(&pending);
        int node = lean_obj_tag(current) == 1;
        lean_object *view = current;
        if (node) {
            lean_object *info = lean_ctor_get(current, 0);
            lean_inc(info);
            view = lean_alloc_ctor(1, 3, 0);
            lean_ctor_set(view, 0, info);
            lean_ctor_set(view, 1, lean_box(0));
            lean_ctor_set(view, 2, lean_mk_empty_array());
        }
        lean_object *found = info_query != NULL ? info_query(view) : tail(view, canonical);
        if (node) lean_dec(view);
        if (!lean_is_scalar(found)) {
            lean_dec(current);
            lean_dec(pending);
            return found;
        }
        if (node) {
            lean_object *children = lean_ctor_get(current, 2);
            lean_object *forward = reverse ? NULL : lean_mk_empty_array();
            while (!lean_is_scalar(children)) {
                lean_object *child = lean_ctor_get(children, 0);
                lean_inc(child);
                if (forward != NULL) forward = lean_array_push(forward, child);
                else pending = lean_array_push(pending, child);
                children = lean_ctor_get(children, 1);
            }
            if (forward != NULL) {
                while (lean_array_size(forward) != 0) pending = lean_array_push(pending, omega_position_pop(&forward));
                lean_dec(forward);
            }
        }
        lean_dec(current);
    }
    lean_dec(pending);
    return lean_box(0);
}
