#include <lean/lean.h>
#include "strict_nat.h"
extern lean_obj_res runtime_initialize_PathIOConsumer(uint8_t);
extern lean_obj_res omega_test_path_env(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_path_create(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_path_rmdir(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_path_unlink(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_path_rename(lean_obj_arg, lean_obj_arg, lean_obj_arg);

extern lean_obj_res omega_test_path_hard_link(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_path_set_cwd(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_path_cwd(lean_obj_arg);
extern lean_obj_res omega_test_path_process_cwd(lean_obj_arg);
extern lean_obj_res omega_test_path_real(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_path_temp_dir(lean_obj_arg);
extern lean_obj_res omega_test_path_app(lean_obj_arg);
extern lean_obj_res omega_test_path_list(lean_obj_arg, lean_obj_arg);
extern lean_obj_res lean_io_current_dir(void);
extern lean_obj_res lean_io_app_path(void);

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
        unsigned value = 0;
        while (!lean_is_scalar(n)) { ++value; n = lean_ctor_get(n, 0); }
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
    if (argc != 6) return 1;
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
    lean_object *cwd = lean_io_current_dir();
    if (!lean_io_result_is_ok(cwd)) return 10;
    if (!path_result(omega_test_path_set_cwd(encode(argv[5]), world), 0, 0)) return 11;
    lean_object *strict_cwd = omega_test_path_cwd(world);
    lean_object *process_cwd = omega_test_path_process_cwd(world);
    lean_object *real = omega_test_path_real(encode("."), world);
    if (lean_obj_tag(strict_cwd) || lean_obj_tag(process_cwd) || lean_obj_tag(real) ||
        !text_equals(lean_ctor_get(strict_cwd, 0), argv[5]) || !text_equals(lean_ctor_get(process_cwd, 0), argv[5]) ||
        !text_equals(lean_ctor_get(real, 0), argv[5])) return 12;
    lean_dec(strict_cwd); lean_dec(process_cwd); lean_dec(real);
    if (!path_result(omega_test_path_set_cwd(encode(lean_string_cstr(lean_io_result_get_value(cwd))), world), 0, 0)) return 13;
    lean_dec(cwd);
    lean_object *app = lean_io_app_path();
    lean_object *strict_app = omega_test_path_app(world);
    if (!lean_io_result_is_ok(app) || lean_obj_tag(strict_app) || !text_equals(lean_ctor_get(strict_app, 0),
        lean_string_cstr(lean_io_result_get_value(app)))) return 14;
    lean_dec(app); lean_dec(strict_app);
    lean_object *temp = omega_test_path_temp_dir(world);
    if (lean_obj_tag(temp)) return 15;
    lean_object *temp_path = lean_ctor_get(temp, 0);
    lean_inc(temp_path); lean_dec(temp);
    if (!path_result(omega_test_path_rmdir(temp_path, world), 0, 0)) return 16;
    if (!path_result(omega_test_path_hard_link(encode(argv[3]), encode(argv[4]), world), 0, 0)) return 17;
    lean_object *entries = omega_test_path_list(encode(argv[5]), world);
    if (lean_obj_tag(entries)) return 18;
    lean_object *xs = lean_ctor_get(entries, 0);
    unsigned seen = 0;
    for (; !lean_is_scalar(xs); xs = lean_ctor_get(xs, 1)) {
        lean_object *e = lean_ctor_get(xs, 0);
        if (!text_equals(lean_ctor_get(e, 0), argv[5])) return 19;
        lean_object *name = lean_ctor_get(e, 1);
        if (text_equals(name, "文件")) seen |= 1;
        else if (text_equals(name, "链接")) seen |= 2;
        else return 20;
    }
    lean_dec(entries);
    if (seen != 3) return 20;
    if (!path_result(omega_test_path_unlink(encode(argv[4]), world), 0, 0)) return 21;
    if (!path_result(omega_test_path_unlink(encode(argv[3]), world), 0, 0)) return 8;
    if (!path_result(omega_test_path_unlink(encode(argv[3]), world), 2, argv[3])) return 9;
    return 0;
}
