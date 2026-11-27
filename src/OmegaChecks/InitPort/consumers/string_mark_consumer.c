#include "strict_string.h"
extern int printf(const char *, ...);
extern int strcmp(const char *, const char *);
extern int strncmp(const char *, const char *, size_t);

extern void lean_initialize_runtime_module(void);
extern lean_obj_res runtime_initialize_StringMarkConsumer(uint8_t);
extern lean_obj_res omega_test_mark(lean_obj_arg);
extern lean_obj_res omega_test_propagate(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_push_marked(lean_obj_arg, lean_obj_arg);

static lean_obj_res text(bool strict, const char *s) {
    lean_object *native = lean_mk_string(s);
    if (!strict) return native;
    lean_object *out = omega_string_from_lean(native);
    lean_dec(native);
    return out;
}

static bool is_marked(bool strict, b_lean_obj_arg s) {
    return strict ? lean_ctor_get_uint8(s, sizeof(void *)) : lean_string_is_marked_linear(s);
}

int main(int argc, char **argv) {
    if (argc != 4) return 1;
    lean_initialize_runtime_module();
    lean_object *init = runtime_initialize_StringMarkConsumer(1);
    if (lean_io_result_is_error(init)) return 2;
    lean_dec(init);
    lean_io_mark_end_initialization();
    bool strict = !strcmp(argv[1], "strict");
    bool shared = !strncmp(argv[2], "shared-", 7);
    const char *op = argv[2] + (shared ? 7 : 0);
    lean_object *source = text(strict, "source");
    lean_object *value = text(strict, argv[3]);
    lean_object *(*mark)(lean_obj_arg) = strict ? omega_test_mark : lean_string_mark_linear;
    if (strcmp(op, "mark") && strcmp(op, "propagate-fresh")) value = mark(value);
    if (!strcmp(op, "propagate") || !strcmp(op, "propagate-fresh")) source = mark(source);
    if (shared) lean_inc(value);
    lean_object *result;
    if (!strncmp(op, "propagate", 9)) {
        if (strict) lean_inc(source);
        result = strict ? omega_test_propagate(source, value) : lean_string_propagate_mark(source, value);
    }
    else if (!strcmp(op, "push"))
        result = strict ? omega_test_push_marked(value, lean_uint32_to_nat(0x1f642))
                        : lean_string_push(value, 0x1f642);
    else
        result = mark(value);
    lean_object *view = strict ? omega_string_to_lean(result) : result;
    printf("%u %u %u %s\n", is_marked(strict, result), shared && is_marked(strict, value),
           shared && value == result, lean_string_cstr(view));
    if (strict) lean_dec(view);
    lean_dec(result);
    if (shared) lean_dec(value);
    lean_dec(source);
    return 0;
}
