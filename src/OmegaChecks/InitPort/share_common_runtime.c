#include <lean/lean.h>

extern lean_obj_res l_ShareCommon_StateFactory_mkImpl(lean_obj_arg);

#include "share_common_word.h"

extern uint64_t lean_sharecommon_hash(b_lean_obj_arg);

LEAN_EXPORT lean_obj_res omega_share_common_object_hash(b_lean_obj_arg key) {
    return lean_uint64_to_nat(lean_sharecommon_hash(key));
}

static lean_object *capture(void *entry, unsigned arity, lean_obj_arg value) {
    lean_object *closure = lean_alloc_closure(entry, arity, 1);
    lean_closure_set(closure, 0, value);
    return closure;
}

/* BEq is a single boxed closure with the same Boolean result on both sides.
   The type parameters are erased. Retain the builder's remaining arguments
   through ordinary Lean partial application. */
static lean_obj_res map_op(lean_obj_arg fn, lean_obj_arg alpha, lean_obj_arg beta,
                           lean_obj_arg eq, lean_obj_arg hash) {
    return lean_apply_4(fn, alpha, beta, eq, capture((void *)strict_hash, 2, hash));
}
static lean_obj_res set_op(lean_obj_arg fn, lean_obj_arg alpha, lean_obj_arg eq, lean_obj_arg hash) {
    return lean_apply_3(fn, alpha, eq, capture((void *)strict_hash, 2, hash));
}
static lean_obj_res mk_map(lean_obj_arg fn, lean_obj_arg alpha, lean_obj_arg beta,
                           lean_obj_arg eq, lean_obj_arg hash, lean_obj_arg capacity) {
    return lean_apply_1(map_op(fn, alpha, beta, eq, hash), capacity);
}
static lean_obj_res mk_set(lean_obj_arg fn, lean_obj_arg alpha, lean_obj_arg eq,
                           lean_obj_arg hash, lean_obj_arg capacity) {
    return lean_apply_1(set_op(fn, alpha, eq, hash), capacity);
}

LEAN_EXPORT lean_obj_res omega_share_common_factory_mk(lean_obj_arg builder) {
    static const struct { void *entry; unsigned arity; } callbacks[] = {
        {(void *)mk_map, 6}, {(void *)map_op, 5}, {(void *)map_op, 5},
        {(void *)mk_set, 5}, {(void *)set_op, 4}, {(void *)set_op, 4}
    };
    lean_object *wrapped = lean_alloc_ctor(0, 6, 0);
    for (unsigned i = 0; i < 6; ++i) {
        lean_object *fn = lean_ctor_get(builder, i);
        lean_inc(fn);
        lean_ctor_set(wrapped, i, capture(callbacks[i].entry, callbacks[i].arity, fn));
    }
    lean_dec(builder);
    return l_ShareCommon_StateFactory_mkImpl(wrapped);
}
