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
