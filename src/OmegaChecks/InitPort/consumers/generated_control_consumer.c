#include <lean/lean.h>
#include <stdint.h>
extern lean_obj_res runtime_initialize_GeneratedControlConsumer(uint8_t);
extern uint8_t omega_generated_except(uint8_t, uint8_t);
extern uint8_t omega_generated_option(uint8_t, uint8_t);
extern uint8_t omega_generated_state(uint8_t, uint8_t);
#ifdef OMEGA_TEST_NAMES
#include "strict_name.h"
extern lean_obj_res omega_test_scoped_name(lean_obj_arg, lean_obj_arg, lean_obj_arg, uint8_t);
extern lean_obj_res l_Lean_addMacroScope(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res l_Lean_Name_append(lean_obj_arg, lean_obj_arg);

static int check_scoped_name(b_lean_obj_arg left, b_lean_obj_arg right, unsigned scope, uint8_t on_left) {
    lean_inc(left);
    lean_inc(left);
    lean_inc(right);
    lean_inc(right);
    lean_object *scoped = l_Lean_addMacroScope(left, left, lean_unsigned_to_nat(scope));
    scoped = l_Lean_addMacroScope(right, scoped, lean_usize_to_nat((size_t)scope + 1));
    lean_object *expected = on_left ? l_Lean_Name_append(scoped, right) : l_Lean_Name_append(right, scoped);
    lean_object *strict = omega_test_scoped_name(omega_name_from_lean(left), omega_name_from_lean(right),
                                                 lean_unsigned_to_nat(scope), on_left);
    lean_object *actual = omega_name_to_lean(strict);
    int equal = lean_name_eq(actual, expected);
    lean_dec(actual);
    lean_dec(strict);
    lean_dec(expected);
    return equal;
}
#endif
#ifdef OMEGA_TEST_MIXED
extern lean_obj_res runtime_initialize_GeneratedMixedConsumer(uint8_t);
extern uint8_t omega_mixed_or(uint8_t, uint8_t);
extern uint8_t omega_mixed_and(uint8_t, uint8_t);
extern lean_obj_res omega_mixed_quotation(uint8_t);
extern uint8_t omega_mixed_depth(uint8_t);
extern uint8_t omega_mixed_empty_syntax(uint8_t);
#endif
#ifdef OMEGA_TEST_LITERALS
#include "strict_string.h"
extern lean_obj_res omega_mixed_empty_string(uint8_t);
extern lean_obj_res omega_mixed_scalars(lean_obj_arg, lean_obj_arg);

static int check_scalars(unsigned a, unsigned b, const unsigned char *expected, size_t count) {
    lean_object *strict = omega_mixed_scalars(omega_nat_from_uint64(a), omega_nat_from_uint64(b));
    lean_object *encoded = omega_string_to_lean(strict);
    int equal = lean_string_size(encoded) == count + 1;
    for (size_t i = 0; equal && i < count; ++i)
        equal = (unsigned char)lean_string_cstr(encoded)[i] == expected[i];
    lean_dec(encoded);
    lean_dec(strict);
    return equal;
}

#endif
int main(void) {
    lean_object *status = runtime_initialize_GeneratedControlConsumer(1);
    if (lean_io_result_is_error(status)) return 1;
    lean_dec(status);
#ifdef OMEGA_TEST_MIXED
    status = runtime_initialize_GeneratedMixedConsumer(1);
    if (lean_io_result_is_error(status)) return 5;
    lean_dec(status);
    lean_object *quotation = omega_mixed_quotation(1);
    if (!quotation) return 6;
    lean_dec(quotation);
    if (!omega_mixed_depth(0)) return 9;
    if (!omega_mixed_empty_syntax(0)) return 10;
#endif
#ifdef OMEGA_TEST_LITERALS
    lean_object *empty = omega_mixed_empty_string(0);
    if (lean_is_scalar(empty) || omega_bytes_size(lean_ctor_get(empty, 0)) != 0 || lean_ctor_get_uint8(empty, sizeof(void *))) return 11;
    lean_dec(empty);
    const unsigned char nul_latin[] = {0x00, 0xc3, 0xa9};
    const unsigned char cjk_emoji[] = {0xe4, 0xb8, 0xad, 0xf0, 0x9f, 0x99, 0x82};
    const unsigned char boundaries[] = {0xef, 0xbf, 0xbf, 0xf4, 0x8f, 0xbf, 0xbf};
    const unsigned char invalid[] = {0x00, 0x00};
    if (!check_scalars(0, 0xe9, nul_latin, sizeof nul_latin)) return 12;
    if (!check_scalars(0x4e2d, 0x1f642, cjk_emoji, sizeof cjk_emoji)) return 13;
    if (!check_scalars(0xffff, 0x10ffff, boundaries, sizeof boundaries)) return 14;
    if (!check_scalars(0xd800, 0x110000, invalid, sizeof invalid)) return 15;
#endif
    lean_io_mark_end_initialization();
#ifdef OMEGA_TEST_NAMES
    lean_object *left = lean_name_mk_numeral(lean_name_mk_string(lean_box(0), lean_mk_string("左")), lean_box(13));
    lean_object *right = lean_name_mk_string(lean_box(0), lean_mk_string("module"));
    for (uint8_t side = 0; side <= 1; ++side) {
        if (!check_scoped_name(left, right, 0, side) || !check_scoped_name(right, left, 4096, side) ||
            !check_scoped_name(right, right, 37, side)) return 16;
    }
    lean_dec(left);
    lean_dec(right);
#endif
    for (uint8_t x = 0; x <= 1; x++) {
        for (uint8_t y = 0; y <= 1; y++) {
            if (omega_generated_except(x, y) != (x || y)) return 2;
            if (omega_generated_option(x, y) != (x && y)) return 3;
            if (omega_generated_state(x, y) != (x && y)) return 4;
        }
    }
    return 0;
}
