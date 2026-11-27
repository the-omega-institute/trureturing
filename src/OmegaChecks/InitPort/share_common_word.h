#pragma once
#include "strict_nat.h"

/* The strict UInt64 structure erases to its Nat field. */
static lean_obj_res strict_hash(lean_obj_arg hash, lean_obj_arg key) {
    lean_object *word = lean_apply_1(hash, key);
    uint64_t value = lean_unbox_uint64(word);
    lean_dec(word);
    return lean_uint64_to_nat(value);
}
