#pragma once
#include <lean/lean.h>

static lean_obj_res omega_nat_from_uint64(uint64_t n) {
    return lean_uint64_to_nat(n);
}

static lean_obj_res omega_int_from_lean(b_lean_obj_arg integer) {
    uint8_t negative = lean_int_lt(integer, lean_box(0));
    lean_object *magnitude = lean_nat_abs(integer);
    if (negative) {
        lean_object *predecessor = lean_nat_pred(magnitude);
        lean_dec(magnitude);
        magnitude = predecessor;
    }
    lean_object *value = lean_alloc_ctor(negative, 1, 0);
    lean_ctor_set(value, 0, magnitude);
    return value;
}
