#include "strict_string.h"

extern void lean_initialize_runtime_module(void);
extern lean_obj_res runtime_initialize_RatFormatConsumer(uint8_t);
extern lean_obj_res omega_test_rat_format(uint8_t, uint8_t, lean_obj_arg, lean_obj_arg);

static bool matches(uint8_t negative, uint8_t repr_output, const char *num, const char *den,
                    const char *expected) {
    lean_object *bytes = omega_test_rat_format(negative, repr_output, lean_cstr_to_nat(num), lean_cstr_to_nat(den));
    lean_object *actual = omega_string_to_lean(bytes);
    lean_dec(bytes);
    lean_object *reference = lean_mk_string(expected);
    bool same = lean_string_eq(actual, reference);
    lean_dec(actual);
    lean_dec(reference);
    return same;
}

int main(void) {
    static const struct {
        uint8_t negative;
        const char *num, *den, *text, *repr;
    } cases[] = {
        {0, "23", "0", "0", "0"},
        {1, "8", "0", "0", "0"},
        {1, "8", "3", "-3", "-3"},
        {0, "45", "35", "9/7", "(9 : Rat)/7"},
        {1, "44", "35", "-9/7", "(-9 : Rat)/7"},
        {0, "1267650600228229401496703205376", "3", "1267650600228229401496703205376/3",
         "(1267650600228229401496703205376 : Rat)/3"},
    };
    lean_initialize_runtime_module();
    lean_object *initialized = runtime_initialize_RatFormatConsumer(1);
    if (lean_io_result_is_error(initialized)) return 1;
    lean_dec(initialized);
    for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); ++i) {
        if (!matches(cases[i].negative, 0, cases[i].num, cases[i].den, cases[i].text) ||
            !matches(cases[i].negative, 1, cases[i].num, cases[i].den, cases[i].repr))
            return 2;
    }
    return 0;
}
