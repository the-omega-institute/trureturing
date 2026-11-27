#pragma once
#include <lean/lean.h>

static lean_obj_res omega_nat_from_uint64(uint64_t n) {
    return lean_uint64_to_nat(n);
}
