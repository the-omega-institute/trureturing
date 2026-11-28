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

static lean_obj_res native_io_error(b_lean_obj_arg error);

static lean_obj_res native_option_string(b_lean_obj_arg value) {
    if (lean_is_scalar(value)) return lean_box(0);
    lean_object *out = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(out, 0, omega_string_to_lean(lean_ctor_get(value, 0)));
    return out;
}

static lean_obj_res native_stream_result(lean_obj_arg r, decoder convert) {
    lean_object *value = lean_ctor_get(r, 0);
    lean_object *out = lean_obj_tag(r) == 0 ? lean_io_result_mk_ok(convert(value))
                                            : lean_io_result_mk_error(native_io_error(value));
    lean_dec(r);
    return out;
}

static lean_obj_res native_flush(lean_obj_arg action, lean_obj_arg world) {
    return native_stream_result(lean_apply_1(action, world), strict_unit);
}

static lean_obj_res native_read(lean_obj_arg action, lean_obj_arg count, lean_obj_arg world) {
    lean_object *n = lean_usize_to_nat(lean_unbox_usize(count));
    lean_dec(count);
    return native_stream_result(lean_apply_2(action, n, world), omega_bytes_to_lean);
}

static lean_obj_res native_write(lean_obj_arg action, lean_obj_arg bytes, lean_obj_arg world) {
    lean_object *data = from_byte_array(bytes);
    lean_dec(bytes);
    return native_stream_result(lean_apply_2(action, data, world), strict_unit);
}

static lean_obj_res native_get_line(lean_obj_arg action, lean_obj_arg world) {
    return native_stream_result(lean_apply_1(action, world), omega_string_to_lean);
}

static lean_obj_res native_put_str(lean_obj_arg action, lean_obj_arg string, lean_obj_arg world) {
    lean_object *s = omega_string_from_lean(string);
    lean_dec(string);
    return native_stream_result(lean_apply_2(action, s, world), strict_unit);
}

static lean_obj_res native_is_tty(lean_obj_arg action, lean_obj_arg world) {
    lean_object *r = lean_apply_1(action, world);
    lean_object *value = retain_value(lean_ctor_get(r, 0));
    lean_dec(r);
    return value;
}

static lean_obj_res convert_stream(lean_obj_arg stream, bool to_native) {
    static void *const strict_callbacks[] = {
        (void *)stream_flush, (void *)stream_read, (void *)stream_write,
        (void *)stream_get_line, (void *)stream_put_str, (void *)stream_is_tty
    };
    static void *const native_callbacks[] = {
        (void *)native_flush, (void *)native_read, (void *)native_write,
        (void *)native_get_line, (void *)native_put_str, (void *)native_is_tty
    };
    static unsigned const arities[] = {2, 3, 3, 2, 3, 2};
    void *const *callbacks = to_native ? native_callbacks : strict_callbacks;
    void *const *reverse = to_native ? strict_callbacks : native_callbacks;
    lean_object *out = lean_alloc_ctor(0, 6, 0);
    for (unsigned i = 0; i < 6; ++i) {
        lean_object *field = lean_ctor_get(stream, i);
        /* Unwrap a returning callback so its caller's world remains observable
           and repeated restoration never accumulates a chain of wrappers. */
        if (lean_closure_fun(field) == reverse[i]) {
            lean_ctor_set(out, i, retain_value(lean_closure_get(field, 0)));
            continue;
        }
        lean_object *wrapper = lean_alloc_closure(callbacks[i], arities[i], 1);
        lean_closure_set(wrapper, 0, retain_value(field));
        lean_ctor_set(out, i, wrapper);
    }
    lean_dec(stream);
    return out;
}

extern lean_obj_res lean_get_stdin(void);
extern lean_obj_res lean_get_stdout(void);
extern lean_obj_res lean_get_stderr(void);

LEAN_EXPORT lean_obj_res omega_io_get_stdin(lean_obj_arg world) {
    return world_result(0, convert_stream(lean_get_stdin(), false), world);
}

LEAN_EXPORT lean_obj_res omega_io_get_stdout(lean_obj_arg world) {
    return world_result(0, convert_stream(lean_get_stdout(), false), world);
}

LEAN_EXPORT lean_obj_res omega_io_get_stderr(lean_obj_arg world) {
    return world_result(0, convert_stream(lean_get_stderr(), false), world);
}

extern lean_obj_res lean_get_set_stdin(lean_obj_arg);

LEAN_EXPORT lean_obj_res omega_io_set_stdin(lean_obj_arg stream, lean_obj_arg world) {
    lean_object *previous = lean_get_set_stdin(convert_stream(stream, true));
    return world_result(0, convert_stream(previous, false), world);
}

extern lean_obj_res lean_get_set_stdout(lean_obj_arg);

LEAN_EXPORT lean_obj_res omega_io_set_stdout(lean_obj_arg stream, lean_obj_arg world) {
    lean_object *previous = lean_get_set_stdout(convert_stream(stream, true));
    return world_result(0, convert_stream(previous, false), world);
}

extern lean_obj_res lean_get_set_stderr(lean_obj_arg);

LEAN_EXPORT lean_obj_res omega_io_set_stderr(lean_obj_arg stream, lean_obj_arg world) {
    lean_object *previous = lean_get_set_stderr(convert_stream(stream, true));
    return world_result(0, convert_stream(previous, false), world);
}
