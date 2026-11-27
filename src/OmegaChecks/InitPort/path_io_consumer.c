#include <lean/lean.h>
#include "strict_nat.h"
extern lean_obj_res runtime_initialize_PathIOConsumer(uint8_t);
extern lean_obj_res omega_test_path_env(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_path_create(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_path_rmdir(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_path_unlink(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_path_rename(lean_obj_arg, lean_obj_arg, lean_obj_arg);

static lean_object *encode(const char *s) {
    const char *end = s;
    while (*end) ++end;
    lean_object *xs = lean_box(0);
    while (end > s) {
        lean_object *node = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(node, 0, omega_nat_from_uint64((unsigned char)*--end));
        lean_ctor_set(node, 1, xs);
        xs = node;
    }
    return xs;
}

static int text_equals(b_lean_obj_arg bytes, const char *text) {
    while (!lean_is_scalar(bytes) && *text) {
        b_lean_obj_arg n = lean_ctor_get(bytes, 0);
        unsigned value = lean_unbox(n);
        if (value != (unsigned char)*text++) return 0;
        bytes = lean_ctor_get(bytes, 1);
    }
    return lean_is_scalar(bytes) && !*text;
}

static int path_result(lean_obj_arg out, unsigned tag, const char *path) {
    lean_object *s = lean_ctor_get(out, 0);
    int ok = lean_ctor_get(out, 1) == lean_box(0) && lean_obj_tag(s) == tag;
    if (ok && path) {
        lean_object *file = lean_ctor_get(s, 0);
        if (tag == 1 && !lean_is_scalar(file)) file = lean_ctor_get(file, 0);
        ok = text_equals(file, path) && !lean_is_scalar(lean_ctor_get(s, 1));
    }
    lean_dec(out);
    return ok;
}

int main(int argc, char **argv) {
    if (argc != 4) return 1;
    lean_object *init = runtime_initialize_PathIOConsumer(1);
    if (lean_io_result_is_error(init)) return 1;
    lean_dec(init);
    lean_io_mark_end_initialization();
    lean_object *world = lean_box(0);
    lean_object *env = omega_test_path_env(encode("OMEGA_PATH_TEST_VALUE"), world);
    lean_object *some = lean_ctor_get(env, 0);
    if (lean_ctor_get(env, 1) != world || lean_is_scalar(some) || !text_equals(lean_ctor_get(some, 0), "héλ界")) return 2;
    lean_dec(env);
    env = omega_test_path_env(encode("OMEGA_PATH_TEST_ABSENT"), world);
    if (lean_ctor_get(env, 0) != lean_box(0) || lean_ctor_get(env, 1) != world) return 3;
    lean_dec(env);
    if (!path_result(omega_test_path_create(encode(argv[1]), world), 0, 0)) return 4;
    if (!path_result(omega_test_path_create(encode(argv[1]), world), 1, argv[1])) return 5;
    if (!path_result(omega_test_path_rename(encode(argv[1]), encode(argv[2]), world), 0, 0)) return 6;
    if (!path_result(omega_test_path_rmdir(encode(argv[2]), world), 0, 0)) return 7;
    if (!path_result(omega_test_path_unlink(encode(argv[3]), world), 0, 0)) return 8;
    if (!path_result(omega_test_path_unlink(encode(argv[3]), world), 2, argv[3])) return 9;
    return 0;
}
