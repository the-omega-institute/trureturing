#include "strict_string.h"

extern lean_obj_res runtime_initialize_StringListConsumer(uint8_t);
extern lean_obj_res omega_string_roundtrip(lean_obj_arg);
extern lean_obj_res omega_string_scalars(lean_obj_arg);
extern lean_obj_res omega_string_bytes(lean_obj_arg);

extern lean_obj_res omega_test_string_raw(lean_obj_arg);
extern uint8_t omega_test_string_equal(lean_obj_arg, lean_obj_arg);
extern uint8_t omega_test_string_less(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_string_hash(lean_obj_arg);
extern lean_obj_res omega_test_string_data(lean_obj_arg);

extern uint8_t omega_test_string_valid_bytes(lean_obj_arg);
extern lean_obj_res omega_test_string_get(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_string_next(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_string_prev(lean_obj_arg, lean_obj_arg);
extern uint8_t omega_test_string_end(lean_obj_arg, lean_obj_arg);
extern uint8_t omega_test_string_valid_pos(lean_obj_arg, lean_obj_arg);
extern uint8_t lean_string_is_valid_pos(b_lean_obj_arg, b_lean_obj_arg);

extern lean_obj_res omega_test_string_push(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_string_append(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_string_length(lean_obj_arg);
extern lean_obj_res omega_test_string_extract(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_string_utf8(lean_obj_arg);

static int same_text(lean_obj_arg strict, lean_obj_arg expected) {
    lean_object *actual = omega_string_to_lean(strict);
    uint8_t equal = lean_string_dec_eq(actual, expected);
    lean_dec(actual);
    lean_dec(strict);
    lean_dec(expected);
    return equal;
}

static int check_text(b_lean_obj_arg a, b_lean_obj_arg b) {
    if (omega_test_string_length(omega_string_from_lean(a)) != lean_string_length(a)) return 0;
    lean_inc(a);
    if (!same_text(omega_test_string_append(omega_string_from_lean(a), omega_string_from_lean(b)),
                   lean_string_append(a, b))) return 0;
    lean_inc(a);
    if (!same_text(omega_test_string_push(omega_string_from_lean(a), lean_box(0x1f642)),
                   lean_string_push(a, 0x1f642))) return 0;
    lean_inc(a);
    if (!same_text(omega_string_wrap(omega_test_string_utf8(omega_string_from_lean(a)), 0), a)) return 0;
    lean_object *start = lean_box(1), *stop = lean_box(3);
    return same_text(omega_test_string_extract(omega_string_from_lean(a), start, stop),
                     lean_string_utf8_extract(a, start, stop));
}

static int check_positions(b_lean_obj_arg s) {
    for (size_t i = 0; i <= lean_string_size(s) + 1; ++i) {
        lean_object *p = lean_box(i);
        lean_object *c = omega_test_string_get(omega_string_from_lean(s), p);
        lean_object *next = omega_test_string_next(omega_string_from_lean(s), p);
        lean_object *prev = omega_test_string_prev(omega_string_from_lean(s), p);
        int good = c == lean_box(lean_string_utf8_get(s, p)) && next == lean_string_utf8_next(s, p)
            && prev == lean_string_utf8_prev(s, p)
            && omega_test_string_end(omega_string_from_lean(s), p) == lean_string_utf8_at_end(s, p)
            && omega_test_string_valid_pos(omega_string_from_lean(s), p) == lean_string_is_valid_pos(s, p);
        lean_dec(c);
        lean_dec(next);
        lean_dec(prev);
        if (!good) return 0;
    }
    return 1;
}

static int check_operations(b_lean_obj_arg a, b_lean_obj_arg b) {
    uint8_t equal = omega_test_string_equal(omega_string_from_lean(a), omega_string_from_lean(b));
    uint8_t less = omega_test_string_less(omega_string_from_lean(a), omega_string_from_lean(b));
    if (equal != lean_string_dec_eq(a, b) || less != lean_string_dec_lt(a, b)) return 0;
    lean_object *hash = omega_test_string_hash(omega_string_from_lean(a));
    lean_object *expected = lean_uint64_to_nat(lean_string_hash(a));
    int valid = lean_nat_dec_eq(hash, expected);
    lean_dec(hash);
    lean_dec(expected);
    lean_object *raw = omega_test_string_raw(omega_string_from_lean(a));
    lean_object *bytes = omega_bytes_to_lean(raw);
    valid = valid && lean_sarray_size(bytes) == lean_string_size(a) - 1;
    for (size_t i = 0; valid && i < lean_sarray_size(bytes); ++i) {
        valid = lean_sarray_cptr(bytes)[i] == (unsigned char)lean_string_cstr(a)[i];
    }
    lean_dec(bytes);
    lean_dec(raw);
    return valid;
}

static int has_scalars(b_lean_obj_arg chars, const uint32_t *values, size_t count) {
    for (size_t i = 0; i < count; ++i) {
        if (lean_is_scalar(chars) || lean_ctor_get(chars, 0) != lean_box(values[i])) return 0;
        chars = lean_ctor_get(chars, 1);
    }
    return chars == lean_box(0);
}

int main(void) {
    lean_object *status = runtime_initialize_StringListConsumer(1);
    if (lean_io_result_is_error(status)) return 1;
    lean_dec(status);
    lean_io_mark_end_initialization();
    static const char text[] = "\x00\xc3\xa9\xe4\xb8\xad\xf0\x9f\x99\x82";
    static const uint32_t scalars[] = {0, 0xe9, 0x4e2d, 0x1f642};
    lean_object *native = lean_mk_string_from_bytes_unchecked(text, sizeof text - 1);
    lean_object *empty_string = lean_mk_string("");
    if (!check_text(native, native) || !check_text(empty_string, native)) return 11;
    if (!check_operations(native, empty_string) || !check_operations(empty_string, native) ||
        !check_operations(native, native) || !check_operations(empty_string, empty_string)) return 7;
    lean_dec(empty_string);
    static const unsigned char overlong[] = {0xc0, 0xaf};
    if (!check_positions(native) || !omega_test_string_valid_bytes(omega_bytes_from_data((const unsigned char *)text, sizeof text - 1)) ||
        omega_test_string_valid_bytes(omega_bytes_from_data(overlong, sizeof overlong))) return 10;
    lean_object *s = omega_string_from_lean(native);
    lean_inc(s);
    lean_object *len = omega_string_bytes(s);
    if (len != lean_box(sizeof text - 1)) return 2;
    lean_dec(len);
    lean_inc(s);
    lean_object *decoded = omega_string_scalars(s);
    if (!has_scalars(decoded, scalars, sizeof scalars / sizeof scalars[0])) return 3;
    lean_dec(decoded);
    lean_inc(s);
    decoded = omega_test_string_data(s);
    if (!has_scalars(decoded, scalars, sizeof scalars / sizeof scalars[0])) return 8;
    lean_dec(decoded);
    lean_object *encoded = omega_string_roundtrip(s);
    lean_object *again = omega_string_to_lean(encoded);
    int same = lean_string_dec_eq(native, again);
    lean_dec(encoded);
    lean_dec(native);
    lean_dec(again);
    if (!same) return 5;
    lean_object *empty = omega_string_scalars(omega_string_wrap(omega_bytes_from_data(NULL, 0), 0));
    if (empty != lean_box(0)) return 6;
    lean_dec(empty);
    return 0;
}
