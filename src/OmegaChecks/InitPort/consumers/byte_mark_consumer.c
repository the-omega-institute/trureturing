#include "strict_string.h"
extern int printf(const char *, ...);
extern int strcmp(const char *, const char *);
extern int strncmp(const char *, const char *, size_t);
extern void lean_initialize_runtime_module(void);
extern lean_obj_res runtime_initialize_ByteMarkConsumer(uint8_t);
extern lean_obj_res omega_test_byte_mark(lean_obj_arg);
extern lean_obj_res omega_test_byte_propagate(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_byte_push(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_byte_set(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_byte_copy(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_bytes_of_string(lean_obj_arg);
extern lean_obj_res omega_string_of_bytes(lean_obj_arg);
extern lean_obj_res lean_byte_array_copy_slice(b_lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, uint8_t);
extern lean_obj_res lean_string_from_utf8_unchecked(lean_obj_arg);
extern lean_obj_res lean_string_to_utf8(b_lean_obj_arg);

static lean_obj_res buffer(bool strict, const char *s) {
    lean_object *a = lean_mk_empty_byte_array(lean_box(8));
    for (; *s; ++s) a = lean_byte_array_push(a, (uint8_t)*s);
    if (!strict) return a;
    lean_object *out = omega_bytes_from_lean(a);
    lean_dec_ref(a);
    return out;
}

static bool marked(bool strict, b_lean_obj_arg a) {
    return strict ? lean_ctor_get_uint8(a, 3 * sizeof(void *)) : lean_sarray_is_marked_linear(a);
}

int main(int argc, char **argv) {
    if (argc != 4) return 1;
    lean_initialize_runtime_module();
    lean_object *init = runtime_initialize_ByteMarkConsumer(1);
    if (lean_io_result_is_error(init)) return 2;
    lean_dec_ref(init);
    lean_io_mark_end_initialization();
    bool strict = !strcmp(argv[1], "strict");
    bool shared = !strncmp(argv[2], "shared-", 7);
    const char *op = argv[2] + (shared ? 7 : 0);
    lean_object *value = buffer(strict, argv[3]), *source = buffer(strict, "source");
    lean_object *(*mark)(lean_obj_arg) = strict ? omega_test_byte_mark : lean_sarray_mark_linear;
    if (strcmp(op, "mark") && strcmp(op, "propagate-fresh")) value = mark(value);
    if (!strcmp(op, "propagate") || !strcmp(op, "propagate-fresh")) source = mark(source);
    if (shared) lean_inc_ref(value);
    uintptr_t original = (uintptr_t)value;
    lean_object *result;
    if (!strncmp(op, "propagate", 9)) {
        if (strict) lean_inc_ref(source);
        result = strict ? omega_test_byte_propagate(source, value) : lean_sarray_propagate_mark(source, value);
    } else if (!strcmp(op, "push")) {
        result = strict ? omega_test_byte_push(value, lean_box(255)) : lean_byte_array_push(value, 255);
    } else if (!strncmp(op, "set", 3)) {
        lean_object *idx = lean_box(!strcmp(op, "set") ? 0 : 1024);
        result = strict ? omega_test_byte_set(value, idx, lean_box(128)) : lean_byte_array_set(value, idx, 128);
    } else if (!strcmp(op, "copy")) {
        if (strict) lean_inc_ref(source);
        result = strict ? omega_test_byte_copy(source, value, lean_box(3))
                        : lean_byte_array_copy_slice(source, lean_box(0), value, lean_box(0), lean_box(3), 1);
    } else if (!strcmp(op, "text")) {
        lean_object *text = strict ? omega_string_of_bytes(value) : lean_string_from_utf8_unchecked(value);
        printf("text %u ", strict ? lean_ctor_get_uint8(text, sizeof(void *)) : lean_string_is_marked_linear(text));
        if (strict) result = omega_test_bytes_of_string(text);
        else {
            result = lean_string_to_utf8(text);
            lean_dec_ref(text);
        }
    } else {
        result = mark(value);
    }
    lean_object *view = strict ? omega_bytes_to_lean(result) : result;
    printf("%u %u %u %lu %lu", marked(strict, result), shared && marked(strict, value),
           !strcmp(op, "text") ? 0 : (uintptr_t)result == original,
           (unsigned long)lean_sarray_size(view), (unsigned long)lean_sarray_capacity(view));
    for (size_t i = 0; i < lean_sarray_size(view); ++i) printf(" %02x", lean_sarray_cptr(view)[i]);
    printf("\n");
    if (strict) lean_dec_ref(view);
    lean_dec_ref(result);
    if (shared) lean_dec_ref(value);
    lean_dec_ref(source);
    return 0;
}
