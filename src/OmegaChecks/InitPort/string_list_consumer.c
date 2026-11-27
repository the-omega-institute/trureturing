#include "strict_string.h"

extern lean_obj_res runtime_initialize_StringListConsumer(uint8_t);
extern lean_obj_res omega_string_roundtrip(lean_obj_arg);
extern lean_obj_res omega_string_scalars(lean_obj_arg);
extern lean_obj_res omega_string_bytes(lean_obj_arg);

static int represents(b_lean_obj_arg n, uint32_t expected) {
    if (lean_is_scalar(n)) return lean_unbox(n) == expected;
    while (expected && !lean_is_scalar(n) && lean_is_ctor(n)) {
        n = lean_ctor_get(n, 0);
        --expected;
    }
    return !expected && n == lean_box(0);
}

int main(void) {
    lean_object *status = runtime_initialize_StringListConsumer(1);
    if (lean_io_result_is_error(status)) return 1;
    lean_dec(status);
    lean_io_mark_end_initialization();
    static const char text[] = "\x00\xc3\xa9\xe4\xb8\xad\xf0\x9f\x99\x82";
    static const uint32_t scalars[] = {0, 0xe9, 0x4e2d, 0x1f642};
    lean_object *native = lean_mk_string_from_bytes_unchecked(text, sizeof text - 1);
    lean_object *s = omega_string_from_lean(native);
    lean_inc(s);
    lean_object *len = omega_string_bytes(s);
    if (!represents(len, sizeof text - 1)) return 2;
    lean_dec(len);
    lean_inc(s);
    lean_object *decoded = omega_string_scalars(s);
    lean_object *cell = decoded;
    for (size_t i = 0; i < sizeof scalars / sizeof scalars[0]; ++i) {
        if (lean_is_scalar(cell) || !represents(lean_ctor_get(cell, 0), scalars[i])) return 3;
        cell = lean_ctor_get(cell, 1);
    }
    if (!lean_is_scalar(cell)) return 4;
    lean_dec(decoded);
    lean_object *encoded = omega_string_roundtrip(s);
    lean_object *again = omega_string_to_lean(encoded);
    int same = lean_string_dec_eq(native, again);
    lean_dec(encoded);
    lean_dec(native);
    lean_dec(again);
    if (!same) return 5;
    lean_object *empty = omega_string_scalars(lean_box(0));
    if (empty != lean_box(0)) return 6;
    lean_dec(empty);
    return 0;
}
