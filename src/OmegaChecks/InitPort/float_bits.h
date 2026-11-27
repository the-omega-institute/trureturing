#pragma once
#include <lean/lean.h>

static inline double omega_float_from_nat_bits(b_lean_obj_arg value) {
    uint64_t bits = lean_uint64_of_nat(value);
    double result;
    __builtin_memcpy(&result, &bits, sizeof(result));
    return result;
}

static inline lean_obj_res omega_float_to_nat_bits(double value) {
    uint64_t bits;
    __builtin_memcpy(&bits, &value, sizeof(bits));
    return lean_uint64_to_nat(bits);
}

static inline float omega_float32_from_nat_bits(b_lean_obj_arg value) {
    uint32_t bits = lean_uint32_of_nat(value);
    float result;
    __builtin_memcpy(&result, &bits, sizeof(result));
    return result;
}

static inline lean_obj_res omega_float32_to_nat_bits(float value) {
    uint32_t bits;
    __builtin_memcpy(&bits, &value, sizeof(bits));
    return lean_uint32_to_nat(bits);
}
