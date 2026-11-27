#include <lean/lean.h>
#include <stdint.h>
extern lean_obj_res runtime_initialize_GeneratedControlConsumer(uint8_t);
extern uint8_t omega_generated_except(uint8_t, uint8_t);
extern uint8_t omega_generated_option(uint8_t, uint8_t);
extern uint8_t omega_generated_state(uint8_t, uint8_t);
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
    if (empty != lean_box(0)) return 11;
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
    for (uint8_t x = 0; x <= 1; x++) {
        for (uint8_t y = 0; y <= 1; y++) {
            if (omega_generated_except(x, y) != (x || y)) return 2;
            if (omega_generated_option(x, y) != (x && y)) return 3;
            if (omega_generated_state(x, y) != (x && y)) return 4;
        }
    }
    return 0;
}
