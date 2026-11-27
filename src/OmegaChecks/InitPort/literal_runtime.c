#include "strict_string.h"

/* Char, UInt32, BitVec and Fin erase to the checked natural representation. */
static uint32_t omega_scalar_value(b_lean_obj_arg n) {
    uint32_t value = 0;
    while (!lean_is_scalar(n)) {
        if (value == 0x10ffff) return 0;
        ++value;
        n = lean_ctor_get(n, 0);
    }
    return value >= 0xd800 && value <= 0xdfff ? 0 : value;
}

LEAN_EXPORT lean_obj_res omega_char_of_nat(lean_obj_arg n) {
    uint32_t value = omega_scalar_value(n);
    if (value != 0) return n;
    lean_dec(n);
    return lean_box(0);
}

LEAN_EXPORT lean_obj_res omega_string_of_list(lean_obj_arg chars) {
    lean_object *native = lean_mk_string_unchecked("", 0, 0);
    for (lean_object *cell = chars; !lean_is_scalar(cell); cell = lean_ctor_get(cell, 1)) {
        native = lean_string_push(native, omega_scalar_value(lean_ctor_get(cell, 0)));
    }
    lean_dec(chars);
    lean_object *bytes = omega_string_from_lean(native);
    lean_dec(native);
    return bytes;
}
