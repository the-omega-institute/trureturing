#include "strict_string.h"

LEAN_EXPORT lean_obj_res omega_string_to_list(lean_obj_arg bytes) {
    lean_object *native = omega_string_to_lean(bytes);
    lean_dec(bytes);
    lean_object *decoded = lean_string_data(native);
    lean_object *result = lean_box(0);
    lean_object *previous = NULL;
    for (lean_object *cell = decoded; !lean_is_scalar(cell); cell = lean_ctor_get(cell, 1)) {
        uint32_t scalar = lean_unbox_uint32(lean_ctor_get(cell, 0));
        lean_object *next = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(next, 0, omega_nat_from_uint64(scalar));
        lean_ctor_set(next, 1, lean_box(0));
        if (previous) lean_ctor_set(previous, 1, next);
        else result = next;
        previous = next;
    }
    lean_dec(decoded);
    return result;
}

LEAN_EXPORT lean_obj_res omega_string_data(lean_obj_arg bytes) {
    return omega_string_to_list(bytes);
}

LEAN_EXPORT uint8_t omega_string_dec_lt(b_lean_obj_arg left, b_lean_obj_arg right) {
    lean_object *a = omega_string_to_lean(left);
    lean_object *b = omega_string_to_lean(right);
    uint8_t less = lean_string_dec_lt(a, b);
    lean_dec(a);
    lean_dec(b);
    return less;
}
