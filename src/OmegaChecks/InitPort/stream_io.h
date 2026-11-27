#pragma once

/* A native IO callback consumes an erased world. Its strict counterpart
   returns the caller's explicit world alongside the converted result. */
static lean_obj_res stream_flush(lean_obj_arg action, lean_obj_arg world) {
    return strict_result(lean_apply_1(action, lean_box(0)), world, strict_unit);
}

static lean_obj_res stream_read(lean_obj_arg action, lean_obj_arg count, lean_obj_arg world) {
    lean_object *size = lean_box_usize(lean_usize_of_nat_mk(count));
    return strict_result(lean_apply_2(action, size, lean_box(0)), world, from_byte_array);
}

static lean_obj_res stream_write(lean_obj_arg action, lean_obj_arg bytes, lean_obj_arg world) {
    lean_object *native = omega_bytes_to_lean(bytes);
    lean_dec(bytes);
    return strict_result(lean_apply_2(action, native, lean_box(0)), world, strict_unit);
}

static lean_obj_res stream_get_line(lean_obj_arg action, lean_obj_arg world) {
    return strict_result(lean_apply_1(action, lean_box(0)), world, omega_string_from_lean);
}

static lean_obj_res stream_put_str(lean_obj_arg action, lean_obj_arg string, lean_obj_arg world) {
    lean_object *native = omega_string_to_lean(string);
    lean_dec(string);
    return strict_result(lean_apply_2(action, native, lean_box(0)), world, strict_unit);
}

static lean_obj_res stream_is_tty(lean_obj_arg action, lean_obj_arg world) {
    return world_result(0, lean_apply_1(action, lean_box(0)), world);
}

static lean_obj_res strict_stream(lean_obj_arg stream) {
    static void *const callbacks[] = {
        (void *)stream_flush, (void *)stream_read, (void *)stream_write,
        (void *)stream_get_line, (void *)stream_put_str, (void *)stream_is_tty
    };
    static unsigned const arities[] = {2, 3, 3, 2, 3, 2};
    lean_object *out = lean_alloc_ctor(0, 6, 0);
    for (unsigned i = 0; i < 6; ++i) {
        lean_object *wrapper = lean_alloc_closure(callbacks[i], arities[i], 1);
        lean_closure_set(wrapper, 0, retain_value(lean_ctor_get(stream, i)));
        lean_ctor_set(out, i, wrapper);
    }
    lean_dec(stream);
    return out;
}

extern lean_obj_res lean_get_stdin(void);
extern lean_obj_res lean_get_stdout(void);
extern lean_obj_res lean_get_stderr(void);

LEAN_EXPORT lean_obj_res omega_io_get_stdin(lean_obj_arg world) {
    return world_result(0, strict_stream(lean_get_stdin()), world);
}

LEAN_EXPORT lean_obj_res omega_io_get_stdout(lean_obj_arg world) {
    return world_result(0, strict_stream(lean_get_stdout()), world);
}

LEAN_EXPORT lean_obj_res omega_io_get_stderr(lean_obj_arg world) {
    return world_result(0, strict_stream(lean_get_stderr()), world);
}
