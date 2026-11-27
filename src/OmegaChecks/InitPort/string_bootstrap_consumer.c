#include "strict_string.h"

extern void lean_initialize_runtime_module(void);
extern lean_obj_res runtime_initialize_StringBootstrapConsumer(uint8_t);
extern lean_obj_res omega_test_bootstrap_text(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);

static lean_obj_res strict_text(const char *s) {
    lean_object *text = lean_mk_string(s);
    lean_object *bytes = omega_string_from_lean(text);
    lean_dec(text);
    return bytes;
}

static bool matches(const char *s, const char *sep, uint32_t mark, size_t start, const char *want) {
    lean_object *bytes = omega_test_bootstrap_text(strict_text(s), strict_text(sep),
                                                  lean_uint32_to_nat(mark), lean_usize_to_nat(start));
    lean_object *text = omega_string_to_lean(bytes);
    lean_object *expected = lean_mk_string(want);
    bool ok = lean_string_eq(text, expected);
    lean_dec(expected);
    lean_dec(text);
    lean_dec(bytes);
    return ok;
}

int main(void) {
    lean_initialize_runtime_module();
    lean_object *initialized = runtime_initialize_StringBootstrapConsumer(1);
    if (lean_io_result_is_error(initialized)) return 1;
    lean_dec(initialized);
    lean_io_mark_end_initialization();
    return matches("aλλ🙂b", "-", 0x3bb, 1, "-λλ-aλλ🙂b") &&
           matches("aλλ🙂b", "中", 0x1f642, 5, "中🙂中aλλ🙂b") &&
           matches("λ", ":", 0x3bb, 2, "::λ") &&
           matches("", "", 0, 0, "") ? 0 : 2;
}
