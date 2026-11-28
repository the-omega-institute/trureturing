#pragma once
#include <lean/lean.h>

/* The pinned separator loops pass individual syntax values straight through to the callback.
   Their terminal pure receives an array, the single place where its container must change. */
static lean_obj_res omega_sep_array_pure(lean_obj_arg pure, lean_obj_arg type, lean_obj_arg array) {
    return lean_apply_2(pure, type, lean_array_to_list(array));
}

static lean_obj_res omega_sep_replace_field(b_lean_obj_arg original, unsigned index, lean_obj_arg replacement) {
    unsigned size = lean_ctor_num_objs(original);
    lean_object *out = lean_alloc_ctor(0, size, 0);
    for (unsigned i = 0; i < size; ++i) {
        lean_object *field = replacement;
        if (i != index) {
            field = lean_ctor_get(original, i);
            lean_inc(field);
        }
        lean_ctor_set(out, i, field);
    }
    return out;
}

static lean_obj_res omega_array_with_pure(b_lean_obj_arg monad, lean_obj_arg replacement) {
    return omega_sep_replace_field(monad, 0, omega_sep_replace_field(lean_ctor_get(monad, 0), 1, replacement));
}

static lean_obj_res omega_sep_array_monad(b_lean_obj_arg monad) {
    lean_object *applicative = lean_ctor_get(monad, 0);
    lean_object *pure = lean_ctor_get(applicative, 1);
    lean_inc(pure);
    lean_object *adapted = lean_alloc_closure((void *)omega_sep_array_pure, 3, 1);
    lean_closure_set(adapted, 0, pure);
    return omega_array_with_pure(monad, adapted);
}
