#include <lean/lean.h>
#include "strict_string.h"
extern size_t strlen(const char *);
extern int memcmp(const void *, const void *, size_t);
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

extern lean_obj_res omega_test_open(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_tty(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_flush(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_rewind(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_truncate(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_unlock(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_lock(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_try_lock(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_read(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_write(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_line(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_test_put(lean_obj_arg, lean_obj_arg, lean_obj_arg);

static lean_object *encode(const char *s) {
    return omega_string_wrap(omega_bytes_from_data((const unsigned char *)s, strlen(s)), 0);
}

static int text_equals(b_lean_obj_arg strict, const char *text) {
    lean_object *native = omega_string_to_lean(strict);
    int same = lean_string_size(native) == strlen(text) + 1 &&
               memcmp(lean_string_cstr(native), text, strlen(text)) == 0;
    lean_dec(native);
    return same;
}

static int path_result(lean_obj_arg out, unsigned tag, const char *path) {
    lean_object *s = lean_ctor_get(out, 0);
    int ok = lean_ctor_get(out, 1) == lean_box(0) && lean_obj_tag(s) == tag;
    if (ok && path) {
        lean_object *file = lean_ctor_get(s, 0);
        if (tag == 1 && !lean_is_scalar(file)) file = lean_ctor_get(file, 0);
        ok = text_equals(file, path) && lean_ctor_get(s, 1) != lean_box(0);
    }
    lean_dec(out);
    return ok;
}

static int file_ok(lean_obj_res (*action)(lean_obj_arg, lean_obj_arg), b_lean_obj_arg h) {
    lean_inc(h);
    return path_result(action(h, lean_box(0)), 0, 0);
}

#ifdef OMEGA_TEST_READ_INTO
extern lean_obj_res omega_io_handle_read_bin_into(lean_obj_arg, lean_obj_arg, lean_obj_arg);

static int check_eof_buffer(lean_obj_arg handle, lean_obj_arg world) {
    lean_object *bytes = omega_bytes_mark(omega_bytes_from_data((const unsigned char *)"x", 1));
    lean_inc_ref(bytes);
    lean_object *result = omega_io_handle_read_bin_into(handle, bytes, world);
    int ok = lean_obj_tag(result) == 0 && lean_ctor_get(result, 0) == bytes &&
             lean_ctor_get(result, 1) == world;
    lean_dec_ref(result);
    lean_dec_ref(bytes);
    return ok;
}
#endif

static int handle_io(const char *path) {
    lean_object *w = lean_box(0);
    lean_object *out = omega_test_open(encode(path), w);
    if (lean_obj_tag(out) || lean_ctor_get(out, 1) != w) return 0;
    lean_object *h = lean_ctor_get(out, 0);
    lean_inc(h);
    lean_dec(out);
    lean_inc(h);
    out = omega_test_tty(h, w);
    if (lean_ctor_get(out, 0) != lean_box(0)) return 0;
    lean_dec(out);
    if (!file_ok(omega_test_lock, h) || !file_ok(omega_test_unlock, h)) return 0;
    lean_inc(h);
    out = omega_test_try_lock(h, w);
    if (lean_obj_tag(out) || lean_ctor_get(out, 0) != lean_box(1)) return 0;
    lean_dec(out);
    if (!file_ok(omega_test_unlock, h) || !file_ok(omega_test_truncate, h)) return 0;
    lean_inc(h);
    if (!path_result(omega_test_put(h, encode("héλ界\n"), w), 0, 0)) return 0;
    const unsigned char sample[] = {0, 255};
    lean_object *bytes = omega_bytes_from_data(sample, sizeof(sample));
    lean_inc(h);
    if (!path_result(omega_test_write(h, bytes, w), 0, 0) ||
        !file_ok(omega_test_flush, h) || !file_ok(omega_test_rewind, h)) return 0;
    lean_inc(h);
    out = omega_test_line(h, w);
    if (lean_obj_tag(out) || !text_equals(lean_ctor_get(out, 0), "héλ界\n")) return 0;
    lean_dec(out);
#ifdef OMEGA_TEST_READ_INTO
    lean_inc(h);
#endif
    out = omega_test_read(h, omega_nat_from_uint64(9), w);
    if (lean_obj_tag(out)) return 0;
    bytes = lean_ctor_get(out, 0);
    lean_object *packed = omega_bytes_to_lean(bytes);
    int ok = lean_sarray_size(packed) == sizeof(sample) && !memcmp(lean_sarray_cptr(packed), sample, sizeof(sample));
    lean_dec_ref(packed);
    lean_dec(out);
#ifdef OMEGA_TEST_READ_INTO
    ok = check_eof_buffer(h, w) && ok;
#endif
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
    if (!handle_io(argv[3])) return 22;
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
