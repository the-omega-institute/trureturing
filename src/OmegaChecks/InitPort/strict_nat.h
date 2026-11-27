#pragma once
#include <lean/lean.h>

static lean_obj_res omega_nat_from_uint64(uint64_t n) {
    lean_object *value = lean_box(0);
    for (uint64_t i = 0; i < n; ++i) {
        lean_object *next = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(next, 0, value);
        value = next;
    }
    return value;
}
