#pragma once
#include "strict_name.h"

/* Both SourceInfo representations share the synthetic and none constructors. */
static lean_obj_res omega_convert_source_info(b_lean_obj_arg info, bool to_native) {
    if (lean_obj_tag(info) != 0) {
        lean_inc(info);
        return info;
    }
    lean_object *out = lean_alloc_ctor(0, 4, 0);
    for (unsigned i = 0; i < 4; ++i) {
        lean_object *field = lean_ctor_get(info, i);
        if (i == 0 || i == 2) {
            field = omega_convert_substring(field, to_native ? omega_string_to_lean : omega_string_from_lean);
        } else lean_inc(field);
        lean_ctor_set(out, i, field);
    }
    return out;
}

static lean_obj_res omega_convert_preresolved(b_lean_obj_arg pre, bool to_native) {
    unsigned tag = lean_obj_tag(pre);
    lean_object *out = lean_alloc_ctor(tag, tag + 1, 0);
    lean_object *name = lean_ctor_get(pre, 0);
    lean_ctor_set(out, 0, to_native ? omega_name_to_lean(name) : omega_name_from_lean(name));
    if (tag == 1) lean_ctor_set(out, 1, omega_map_list(lean_ctor_get(pre, 1),
                                    to_native ? omega_string_to_lean : omega_string_from_lean));
    return out;
}

static lean_obj_res omega_preresolved_to_lean(b_lean_obj_arg p) { return omega_convert_preresolved(p, true); }
static lean_obj_res omega_preresolved_from_lean(b_lean_obj_arg p) { return omega_convert_preresolved(p, false); }

static lean_obj_res omega_convert_syntax_ctor(b_lean_obj_arg src, lean_obj_arg children, bool to_native) {
    unsigned tag = lean_obj_tag(src);
    if (tag == 0) return lean_box(0);
    unsigned fields = tag == 1 ? 3 : tag == 2 ? 2 : 4;
    lean_object *out = lean_alloc_ctor(tag, fields, 0);
    lean_ctor_set(out, 0, omega_convert_source_info(lean_ctor_get(src, 0), to_native));
    lean_object *field = lean_ctor_get(src, 1);
    if (tag == 1) {
        lean_ctor_set(out, 1, to_native ? omega_name_to_lean(field) : omega_name_from_lean(field));
        lean_ctor_set(out, 2, children);
    } else if (tag == 2) {
        lean_ctor_set(out, 1, to_native ? omega_string_to_lean(field) : omega_string_from_lean(field));
    } else {
        lean_ctor_set(out, 1, omega_convert_substring(field, to_native ? omega_string_to_lean : omega_string_from_lean));
        lean_object *name = lean_ctor_get(src, 2);
        lean_ctor_set(out, 2, to_native ? omega_name_to_lean(name) : omega_name_from_lean(name));
        lean_ctor_set(out, 3, omega_map_list(lean_ctor_get(src, 3),
                                     to_native ? omega_preresolved_to_lean : omega_preresolved_from_lean));
    }
    return out;
}

/* Input cursors borrow from the root. Each frame owns the output children until its node is built. */
typedef struct {
    lean_object *node, *input, *output, *last;
    size_t index;
} omega_syntax_frame;

static lean_obj_res omega_convert_syntax(b_lean_obj_arg root, bool to_native) {
    if (lean_obj_tag(root) != 1) return omega_convert_syntax_ctor(root, NULL, to_native);
    size_t depth = 0;
    lean_object *storage = lean_alloc_sarray(sizeof(omega_syntax_frame), 0, 16);
    omega_syntax_frame *frames = (omega_syntax_frame *)lean_sarray_cptr(storage);
    lean_object *current = root;
    for (;;) {
        lean_object *converted = NULL;
        if (lean_obj_tag(current) == 1) {
            if (depth == lean_sarray_capacity(storage)) {
                lean_sarray_set_size(storage, depth);
                storage = lean_copy_sarray(storage, lean_usize_mul_checked(depth, 2));
                frames = (omega_syntax_frame *)lean_sarray_cptr(storage);
            }
            frames[depth++] = (omega_syntax_frame){ current, lean_ctor_get(current, 2),
                               to_native ? lean_mk_empty_array() : lean_box(0), NULL, 0 };
        } else converted = omega_convert_syntax_ctor(current, NULL, to_native);
        while (depth) {
            omega_syntax_frame *frame = &frames[depth - 1];
            if (converted) {
                if (to_native) frame->output = lean_array_push(frame->output, converted);
                else {
                    lean_object *cell = lean_alloc_ctor(1, 2, 0);
                    lean_ctor_set(cell, 0, converted);
                    lean_ctor_set(cell, 1, lean_box(0));
                    if (frame->last) lean_ctor_set(frame->last, 1, cell);
                    else frame->output = cell;
                    frame->last = cell;
                }
            }
            if (to_native && !lean_is_scalar(frame->input)) {
                current = lean_ctor_get(frame->input, 0);
                frame->input = lean_ctor_get(frame->input, 1);
                break;
            }
            if (!to_native && frame->index < lean_array_size(frame->input)) {
                current = lean_array_get_core(frame->input, frame->index++);
                break;
            }
            converted = omega_convert_syntax_ctor(frame->node, frame->output, to_native);
            --depth;
        }
        if (!depth) {
            lean_dec(storage);
            return converted;
        }
    }
}

static lean_obj_res omega_syntax_from_lean(b_lean_obj_arg stx) { return omega_convert_syntax(stx, false); }

static lean_obj_res omega_syntax_predicate(lean_obj_arg f, lean_obj_arg stx) {
    lean_object *input = omega_syntax_from_lean(stx);
    lean_dec(stx);
    return lean_apply_1(f, input);
}

static lean_obj_res omega_syntax_array_to_lean(b_lean_obj_arg values) {
    lean_object *out = lean_mk_empty_array();
    for (; !lean_is_scalar(values); values = lean_ctor_get(values, 1))
        out = lean_array_push(out, omega_convert_syntax(lean_ctor_get(values, 0), true));
    return out;
}

static lean_obj_res omega_syntax_array_from_lean(b_lean_obj_arg values) {
    lean_object *out = lean_box(0);
    for (size_t i = lean_array_size(values); i > 0; --i) {
        lean_object *cell = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(cell, 0, omega_syntax_from_lean(lean_array_get_core(values, i - 1)));
        lean_ctor_set(cell, 1, out);
        out = cell;
    }
    return out;
}

static lean_obj_res omega_syntax_map(lean_obj_arg f, lean_obj_arg stx) {
    lean_object *mapped = omega_syntax_predicate(f, stx);
    lean_object *out = omega_convert_syntax(mapped, true);
    lean_dec(mapped);
    return out;
}

static lean_obj_res omega_syntax_array_coe(lean_obj_arg coerce, lean_obj_arg values) {
    lean_object *native = omega_syntax_array_to_lean(values);
    lean_dec(values);
    lean_object *converted = lean_apply_1(coerce, native);
    lean_object *out = omega_syntax_array_from_lean(converted);
    lean_dec(converted);
    return out;
}
