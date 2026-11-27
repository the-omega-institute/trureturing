#pragma once
#include <lean/lean.h>

/* In the strict library UInt64, BitVec and Fin each erase to their sole data
   field, ending in a unary Omega.Nat. Build it only when a callback asks for
   a hash. The two capacities supplied by the pinned mkImpl are both 1024. */
static lean_obj_res share_unary(uint64_t n) {
    lean_object *value = lean_box(0);
    for (uint64_t i = 0; i < n; ++i) {
        lean_object *next = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(next, 0, value);
        value = next;
    }
    return value;
}

static lean_obj_res strict_hash(lean_obj_arg hash, lean_obj_arg key) {
    lean_object *word = lean_apply_1(hash, key);
    uint64_t value = lean_unbox_uint64(word);
    lean_dec(word);
    return share_unary(value);
}
