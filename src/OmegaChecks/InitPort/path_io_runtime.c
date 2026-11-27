#include <lean/lean.h>
#include "strict_string.h"

extern lean_obj_res lean_io_getenv(b_lean_obj_arg);
extern lean_obj_res lean_io_create_dir(b_lean_obj_arg);
extern lean_obj_res lean_io_remove_dir(b_lean_obj_arg);
extern lean_obj_res lean_io_remove_file(b_lean_obj_arg);
extern lean_obj_res lean_io_rename(b_lean_obj_arg, b_lean_obj_arg);

static lean_obj_res strict_option_string(b_lean_obj_arg option) {
    if (lean_is_scalar(option)) return lean_box(0);
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, omega_string_from_lean(lean_ctor_get(option, 0)));
    return some;
}

static lean_obj_res world_result(unsigned tag, lean_obj_arg value, lean_obj_arg world) {
    lean_object *out = lean_alloc_ctor(tag, 2, 0);
    lean_ctor_set(out, 0, value);
    lean_ctor_set(out, 1, world);
    return out;
}

LEAN_EXPORT lean_obj_res omega_io_get_env(b_lean_obj_arg name, lean_obj_arg world) {
    lean_object *var = omega_string_to_lean(name);
    lean_object *result = lean_io_getenv(var);
    lean_dec(var);
    lean_object *value = strict_option_string(result);
    lean_dec(result);
    return world_result(0, value, world);
}

#ifdef OMEGA_PATH_IO_FS
/* Emitted from the official and strict IO.Error constructor types and layouts. */
static lean_obj_res strict_io_error(b_lean_obj_arg error);

typedef lean_obj_res (*decoder)(b_lean_obj_arg);

static lean_obj_res strict_unit(b_lean_obj_arg value) {
    return lean_box(0);
}

static lean_obj_res strict_result(lean_obj_arg result, lean_obj_arg world, decoder success) {
    unsigned tag = lean_obj_tag(result);
    lean_object *value = lean_ctor_get(result, 0);
    lean_object *converted = tag == 0 ? success(value) : strict_io_error(value);
    lean_dec(result);
    return world_result(tag, converted, world);
}

static lean_obj_res unary_path(lean_obj_res (*fn)(b_lean_obj_arg), b_lean_obj_arg path, lean_obj_arg world, decoder success) {
    lean_object *native = omega_string_to_lean(path);
    lean_object *result = fn(native);
    lean_dec(native);
    return strict_result(result, world, success);
}

LEAN_EXPORT lean_obj_res omega_io_create_dir(b_lean_obj_arg p, lean_obj_arg world) {
    return unary_path(lean_io_create_dir, p, world, strict_unit);
}
LEAN_EXPORT lean_obj_res omega_io_remove_dir(b_lean_obj_arg p, lean_obj_arg world) {
    return unary_path(lean_io_remove_dir, p, world, strict_unit);
}
LEAN_EXPORT lean_obj_res omega_io_remove_file(b_lean_obj_arg p, lean_obj_arg world) {
    return unary_path(lean_io_remove_file, p, world, strict_unit);
}
static lean_obj_res binary_path(lean_obj_res (*fn)(b_lean_obj_arg, b_lean_obj_arg),
                                b_lean_obj_arg from, b_lean_obj_arg to, lean_obj_arg world) {
    lean_object *old_name = omega_string_to_lean(from);
    lean_object *new_name = omega_string_to_lean(to);
    lean_object *result = fn(old_name, new_name);
    lean_dec(old_name);
    lean_dec(new_name);
    return strict_result(result, world, strict_unit);
}
extern lean_obj_res lean_io_hard_link(b_lean_obj_arg, b_lean_obj_arg);
extern lean_obj_res lean_io_realpath(lean_obj_arg);
extern lean_obj_res lean_io_create_tempdir(void);
extern lean_obj_res lean_io_app_path(void);
extern lean_obj_res lean_io_current_dir(void);
extern lean_obj_res lean_io_process_get_current_dir(void);
extern lean_obj_res lean_io_process_set_current_dir(b_lean_obj_arg);
extern lean_obj_res lean_io_read_dir(b_lean_obj_arg);

LEAN_EXPORT lean_obj_res omega_io_rename(b_lean_obj_arg from, b_lean_obj_arg to, lean_obj_arg world) {
    return binary_path(lean_io_rename, from, to, world);
}
LEAN_EXPORT lean_obj_res omega_io_hard_link(b_lean_obj_arg from, b_lean_obj_arg to, lean_obj_arg world) {
    return binary_path(lean_io_hard_link, from, to, world);
}
LEAN_EXPORT lean_obj_res omega_io_real_path(lean_obj_arg path, lean_obj_arg world) {
    lean_object *p = omega_string_to_lean(path);
    lean_dec(path);
    return strict_result(lean_io_realpath(p), world, omega_string_from_lean);
}
LEAN_EXPORT lean_obj_res omega_io_create_temp_dir(lean_obj_arg world) {
    return strict_result(lean_io_create_tempdir(), world, omega_string_from_lean);
}
LEAN_EXPORT lean_obj_res omega_io_app_path(lean_obj_arg world) {
    return strict_result(lean_io_app_path(), world, omega_string_from_lean);
}
LEAN_EXPORT lean_obj_res omega_io_current_dir(lean_obj_arg world) {
    return strict_result(lean_io_current_dir(), world, omega_string_from_lean);
}
LEAN_EXPORT lean_obj_res omega_io_process_get_current_dir(lean_obj_arg world) {
    return strict_result(lean_io_process_get_current_dir(), world, omega_string_from_lean);
}
LEAN_EXPORT lean_obj_res omega_io_process_set_current_dir(b_lean_obj_arg path, lean_obj_arg world) {
    return unary_path(lean_io_process_set_current_dir, path, world, strict_unit);
}
static lean_obj_res strict_entries(b_lean_obj_arg array) {
    lean_object *entries = lean_box(0);
    for (size_t i = lean_array_size(array); i > 0; --i) {
        lean_object *entry = lean_array_get_core(array, i - 1);
        lean_object *pair = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(pair, 0, omega_string_from_lean(lean_ctor_get(entry, 0)));
        lean_ctor_set(pair, 1, omega_string_from_lean(lean_ctor_get(entry, 1)));
        lean_object *cons = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(cons, 0, pair);
        lean_ctor_set(cons, 1, entries);
        entries = cons;
    }
    return entries;
}
LEAN_EXPORT lean_obj_res omega_io_read_dir(b_lean_obj_arg path, lean_obj_arg world) {
    return unary_path(lean_io_read_dir, path, world, strict_entries);
}
extern lean_obj_res lean_io_prim_handle_mk(b_lean_obj_arg, uint8_t);
extern uint8_t lean_io_prim_handle_is_tty(b_lean_obj_arg);
extern lean_obj_res lean_io_prim_handle_flush(b_lean_obj_arg);
extern lean_obj_res lean_io_prim_handle_rewind(b_lean_obj_arg);
extern lean_obj_res lean_io_prim_handle_truncate(b_lean_obj_arg);
extern lean_obj_res lean_io_prim_handle_unlock(b_lean_obj_arg);
extern lean_obj_res lean_io_prim_handle_lock(b_lean_obj_arg, uint8_t);
extern lean_obj_res lean_io_prim_handle_try_lock(b_lean_obj_arg, uint8_t);
extern lean_obj_res lean_io_prim_handle_write(b_lean_obj_arg, b_lean_obj_arg);
extern lean_obj_res lean_io_prim_handle_read(b_lean_obj_arg, size_t);
extern lean_obj_res lean_io_prim_handle_get_line(b_lean_obj_arg);
extern lean_obj_res lean_io_prim_handle_put_str(b_lean_obj_arg, b_lean_obj_arg);

static lean_obj_res retain_value(b_lean_obj_arg value) {
    lean_inc(value);
    return value;
}

LEAN_EXPORT lean_obj_res omega_io_handle_mk(b_lean_obj_arg path, uint8_t mode, lean_obj_arg world) {
    lean_object *p = omega_string_to_lean(path);
    lean_object *r = lean_io_prim_handle_mk(p, mode);
    lean_dec(p);
    return strict_result(r, world, retain_value);
}
LEAN_EXPORT lean_obj_res omega_io_handle_is_tty(b_lean_obj_arg handle, lean_obj_arg world) {
    return world_result(0, lean_box(lean_io_prim_handle_is_tty(handle)), world);
}
LEAN_EXPORT lean_obj_res omega_io_handle_flush(b_lean_obj_arg handle, lean_obj_arg world) {
    return strict_result(lean_io_prim_handle_flush(handle), world, strict_unit);
}
LEAN_EXPORT lean_obj_res omega_io_handle_rewind(b_lean_obj_arg handle, lean_obj_arg world) {
    return strict_result(lean_io_prim_handle_rewind(handle), world, strict_unit);
}
LEAN_EXPORT lean_obj_res omega_io_handle_truncate(b_lean_obj_arg handle, lean_obj_arg world) {
    return strict_result(lean_io_prim_handle_truncate(handle), world, strict_unit);
}
LEAN_EXPORT lean_obj_res omega_io_handle_unlock(b_lean_obj_arg handle, lean_obj_arg world) {
    return strict_result(lean_io_prim_handle_unlock(handle), world, strict_unit);
}
LEAN_EXPORT lean_obj_res omega_io_handle_get_line(b_lean_obj_arg handle, lean_obj_arg world) {
    return strict_result(lean_io_prim_handle_get_line(handle), world, omega_string_from_lean);
}
LEAN_EXPORT lean_obj_res omega_io_handle_lock(b_lean_obj_arg handle, uint8_t exclusive, lean_obj_arg world) {
    return strict_result(lean_io_prim_handle_lock(handle, exclusive), world, strict_unit);
}
LEAN_EXPORT lean_obj_res omega_io_handle_try_lock(b_lean_obj_arg handle, uint8_t exclusive, lean_obj_arg world) {
    return strict_result(lean_io_prim_handle_try_lock(handle, exclusive), world, retain_value);
}
LEAN_EXPORT lean_obj_res omega_io_handle_put_str(b_lean_obj_arg handle, b_lean_obj_arg string, lean_obj_arg world) {
    lean_object *s = omega_string_to_lean(string);
    lean_object *r = lean_io_prim_handle_put_str(handle, s);
    lean_dec(s);
    return strict_result(r, world, strict_unit);
}
LEAN_EXPORT lean_obj_res omega_io_handle_write(b_lean_obj_arg handle, b_lean_obj_arg bytes, lean_obj_arg world) {
    lean_object *buffer = omega_bytes_to_lean(bytes);
    lean_object *r = lean_io_prim_handle_write(handle, buffer);
    lean_dec(buffer);
    return strict_result(r, world, strict_unit);
}
static lean_obj_res from_byte_array(b_lean_obj_arg buffer) {
    return omega_bytes_from_data(lean_sarray_cptr(buffer), lean_sarray_size(buffer));
}
LEAN_EXPORT lean_obj_res omega_io_handle_read(b_lean_obj_arg handle, lean_obj_arg count, lean_obj_arg world) {
    size_t size = lean_usize_of_nat_mk(count);
    return strict_result(lean_io_prim_handle_read(handle, size), world, from_byte_array);
}
#endif
