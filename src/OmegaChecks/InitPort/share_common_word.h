#pragma once
#include "strict_nat.h"

/* In the strict library UInt64, BitVec and Fin each erase to their sole data
   field, ending in a unary Omega.Nat. Build it only when a callback asks for
   a hash. The two capacities supplied by the pinned mkImpl are both 1024. */
static lean_obj_res strict_hash(lean_obj_arg hash, lean_obj_arg key) {
    lean_object *word = lean_apply_1(hash, key);
    uint64_t value = lean_unbox_uint64(word);
    lean_dec(word);
    return omega_nat_from_uint64(value);
}
