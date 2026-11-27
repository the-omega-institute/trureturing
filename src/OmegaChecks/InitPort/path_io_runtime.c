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

extern lean_obj_res lean_io_create_tempfile(void);

static lean_obj_res strict_temp_file(b_lean_obj_arg pair) {
    lean_object *out = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(out, 0, retain_value(lean_ctor_get(pair, 0)));
    lean_ctor_set(out, 1, omega_string_from_lean(lean_ctor_get(pair, 1)));
    return out;
}

LEAN_EXPORT lean_obj_res omega_io_create_temp_file(lean_obj_arg world) {
    return strict_result(lean_io_create_tempfile(), world, strict_temp_file);
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
    return omega_bytes_from_lean(buffer);
}

static lean_obj_res strict_byte_update_result(lean_obj_arg result, lean_obj_arg world, lean_obj_arg bytes, uintptr_t original) {
    if (lean_io_result_is_error(result)) {
        lean_dec_ref(bytes);
        return strict_result(result, world, from_byte_array);
    }
    lean_object *out = omega_bytes_finish_update(bytes, original, lean_io_result_get_value(result));
    lean_dec_ref(result);
    return world_result(0, out, world);
}

static lean_obj_res strict_string_array(b_lean_obj_arg values) {
    lean_object *list = lean_box(0);
    for (size_t i = lean_array_size(values); i > 0; --i) {
        lean_object *cons = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(cons, 0, omega_string_from_lean(lean_array_get_core(values, i - 1)));
        lean_ctor_set(cons, 1, list);
        list = cons;
    }
    return list;
}
LEAN_EXPORT lean_obj_res omega_io_handle_read(b_lean_obj_arg handle, lean_obj_arg count, lean_obj_arg world) {
    size_t size = lean_usize_of_nat_mk(count);
    return strict_result(lean_io_prim_handle_read(handle, size), world, from_byte_array);
}
extern lean_obj_res lean_io_get_random_bytes(size_t);
extern lean_obj_res lean_chmod(b_lean_obj_arg, uint32_t);

LEAN_EXPORT lean_obj_res omega_io_random_bytes(lean_obj_arg count, lean_obj_arg world) {
    return strict_result(lean_io_get_random_bytes(lean_usize_of_nat_mk(count)), world, from_byte_array);
}

LEAN_EXPORT lean_obj_res omega_io_set_access_rights(b_lean_obj_arg path, lean_obj_arg mode, lean_obj_arg world) {
    lean_object *native = omega_string_to_lean(path);
    lean_object *result = lean_chmod(native, lean_uint32_of_nat(mode));
    lean_dec(mode);
    lean_dec(native);
    return strict_result(result, world, strict_unit);
}

/* A strict IO.Ref stores its payload unchanged. The two modifiers preserve
   the pinned take/put critical section across the supplied callback. */
LEAN_EXPORT lean_obj_res omega_buffer_get(b_lean_obj_arg ref, lean_obj_arg world) {
    return world_result(0, lean_st_ref_get(ref), world);
}

LEAN_EXPORT lean_obj_res omega_buffer_modify(lean_obj_arg ref, lean_obj_arg f, lean_obj_arg world) {
    lean_object *updated = lean_apply_1(f, lean_st_ref_take(ref));
    lean_object *unit = lean_st_ref_put(ref, updated);
    lean_dec(ref);
    return world_result(0, unit, world);
}

LEAN_EXPORT lean_obj_res omega_buffer_modifyGet(lean_obj_arg ref, lean_obj_arg f, lean_obj_arg world) {
    lean_object *pair = lean_apply_1(f, lean_st_ref_take(ref));
    lean_object *out = retain_value(lean_ctor_get(pair, 0));
    lean_object *updated = retain_value(lean_ctor_get(pair, 1));
    lean_dec(pair);
    lean_dec(lean_st_ref_put(ref, updated));
    lean_dec(ref);
    return world_result(0, out, world);
}

#include "stream_io.h"

extern lean_obj_res lean_io_metadata(b_lean_obj_arg);
extern lean_obj_res lean_io_symlink_metadata(b_lean_obj_arg);

static lean_obj_res strict_file_time(b_lean_obj_arg time) {
    lean_object *out = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(out, 0, omega_int_from_lean(lean_ctor_get(time, 0)));
    lean_ctor_set(out, 1, lean_uint32_to_nat(lean_ctor_get_uint32(time, sizeof(void*))));
    return out;
}

static lean_obj_res strict_metadata(b_lean_obj_arg record) {
    size_t offset = 2 * sizeof(void*);
    lean_object *out = lean_alloc_ctor(0, 4, 1);
    lean_ctor_set(out, 0, strict_file_time(lean_ctor_get(record, 0)));
    lean_ctor_set(out, 1, strict_file_time(lean_ctor_get(record, 1)));
    lean_ctor_set(out, 2, lean_uint64_to_nat(lean_ctor_get_uint64(record, offset)));
    lean_ctor_set_uint8(out, 4 * sizeof(void*), lean_ctor_get_uint8(record, offset + 16));
    lean_ctor_set(out, 3, lean_uint64_to_nat(lean_ctor_get_uint64(record, offset + 8)));
    return out;
}

LEAN_EXPORT lean_obj_res omega_io_metadata(b_lean_obj_arg path, lean_obj_arg world) {
    return unary_path(lean_io_metadata, path, world, strict_metadata);
}

LEAN_EXPORT lean_obj_res omega_io_symlink_metadata(b_lean_obj_arg path, lean_obj_arg world) {
    return unary_path(lean_io_symlink_metadata, path, world, strict_metadata);
}

extern lean_obj_res lean_io_process_spawn(lean_obj_arg);
extern lean_obj_res lean_io_process_child_wait(b_lean_obj_arg, b_lean_obj_arg);
extern lean_obj_res lean_io_process_child_try_wait(b_lean_obj_arg, b_lean_obj_arg);
extern lean_obj_res lean_io_process_child_kill(b_lean_obj_arg, b_lean_obj_arg);
extern lean_obj_res lean_io_process_child_take_stdin(b_lean_obj_arg, lean_obj_arg);
extern uint32_t lean_io_process_child_pid(b_lean_obj_arg, lean_obj_arg);

static lean_obj_res process_option(b_lean_obj_arg value, decoder convert) {
    if (lean_is_scalar(value)) return lean_box(0);
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, convert(lean_ctor_get(value, 0)));
    return some;
}

static lean_obj_res native_env_pair(b_lean_obj_arg pair) {
    lean_object *out = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(out, 0, omega_string_to_lean(lean_ctor_get(pair, 0)));
    lean_ctor_set(out, 1, process_option(lean_ctor_get(pair, 1), omega_string_to_lean));
    return out;
}

static lean_obj_res native_process_array(b_lean_obj_arg list, decoder convert) {
    lean_object *out = lean_mk_empty_array();
    for (; !lean_is_scalar(list); list = lean_ctor_get(list, 1))
        out = lean_array_push(out, convert(lean_ctor_get(list, 0)));
    return out;
}

LEAN_EXPORT lean_obj_res omega_io_process_spawn(lean_obj_arg args, lean_obj_arg world) {
    lean_object *native = lean_alloc_ctor(0, 5, 2);
    lean_ctor_set(native, 0, retain_value(lean_ctor_get(args, 0)));
    lean_ctor_set(native, 1, omega_string_to_lean(lean_ctor_get(args, 1)));
    lean_ctor_set(native, 2, native_process_array(lean_ctor_get(args, 2), omega_string_to_lean));
    lean_ctor_set(native, 3, process_option(lean_ctor_get(args, 3), omega_string_to_lean));
    lean_ctor_set(native, 4, native_process_array(lean_ctor_get(args, 4), native_env_pair));
    size_t offset = 5 * sizeof(void*);
    lean_ctor_set_uint8(native, offset, lean_ctor_get_uint8(args, offset));
    lean_ctor_set_uint8(native, offset + 1, lean_ctor_get_uint8(args, offset + 1));
    lean_dec(args);
    return strict_result(lean_io_process_spawn(native), world, retain_value);
}

static lean_obj_res strict_u32(b_lean_obj_arg value) {
    return lean_uint32_to_nat(lean_unbox_uint32(value));
}

static lean_obj_res strict_optional_u32(b_lean_obj_arg value) {
    return process_option(value, strict_u32);
}

LEAN_EXPORT lean_obj_res omega_io_process_child_wait(b_lean_obj_arg cfg, b_lean_obj_arg child, lean_obj_arg world) {
    return strict_result(lean_io_process_child_wait(cfg, child), world, strict_u32);
}

LEAN_EXPORT lean_obj_res omega_io_process_child_try_wait(b_lean_obj_arg cfg, b_lean_obj_arg child, lean_obj_arg world) {
    return strict_result(lean_io_process_child_try_wait(cfg, child), world, strict_optional_u32);
}

LEAN_EXPORT lean_obj_res omega_io_process_child_kill(b_lean_obj_arg cfg, b_lean_obj_arg child, lean_obj_arg world) {
    return strict_result(lean_io_process_child_kill(cfg, child), world, strict_unit);
}

LEAN_EXPORT lean_obj_res omega_io_process_child_take_stdin(b_lean_obj_arg cfg, lean_obj_arg child, lean_obj_arg world) {
    return strict_result(lean_io_process_child_take_stdin(cfg, child), world, retain_value);
}

LEAN_EXPORT lean_obj_res omega_io_process_child_pid(b_lean_obj_arg cfg, lean_obj_arg child) {
    return lean_uint32_to_nat(lean_io_process_child_pid(cfg, child));
}

extern lean_obj_res lean_io_exit(uint8_t);
extern lean_obj_res lean_io_force_exit(uint8_t);

LEAN_EXPORT lean_obj_res omega_io_exit(lean_obj_arg code, lean_obj_arg world) {
    return strict_result(lean_io_exit(lean_uint8_of_nat(code)), world, retain_value);
}

LEAN_EXPORT lean_obj_res omega_io_force_exit(lean_obj_arg code, lean_obj_arg world) {
    return strict_result(lean_io_force_exit(lean_uint8_of_nat(code)), world, retain_value);
}
#endif
