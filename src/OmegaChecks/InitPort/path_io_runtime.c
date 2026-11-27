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

static lean_obj_res strict_unit_result(lean_obj_arg result, lean_obj_arg world) {
    unsigned tag = lean_obj_tag(result);
    lean_object *value = tag == 0 ? lean_box(0) : strict_io_error(lean_ctor_get(result, 0));
    lean_dec(result);
    return world_result(tag, value, world);
}

static lean_obj_res unary_path(lean_obj_res (*fn)(b_lean_obj_arg), b_lean_obj_arg path, lean_obj_arg world) {
    lean_object *native = omega_string_to_lean(path);
    lean_object *result = fn(native);
    lean_dec(native);
    return strict_unit_result(result, world);
}

LEAN_EXPORT lean_obj_res omega_io_create_dir(b_lean_obj_arg p, lean_obj_arg world) {
    return unary_path(lean_io_create_dir, p, world);
}
LEAN_EXPORT lean_obj_res omega_io_remove_dir(b_lean_obj_arg p, lean_obj_arg world) {
    return unary_path(lean_io_remove_dir, p, world);
}
LEAN_EXPORT lean_obj_res omega_io_remove_file(b_lean_obj_arg p, lean_obj_arg world) {
    return unary_path(lean_io_remove_file, p, world);
}
LEAN_EXPORT lean_obj_res omega_io_rename(b_lean_obj_arg from, b_lean_obj_arg to, lean_obj_arg world) {
    lean_object *old_name = omega_string_to_lean(from);
    lean_object *new_name = omega_string_to_lean(to);
    lean_object *result = lean_io_rename(old_name, new_name);
    lean_dec(old_name);
    lean_dec(new_name);
    return strict_unit_result(result, world);
}
#endif
