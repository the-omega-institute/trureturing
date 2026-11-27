#pragma once
#include "strict_string.h"

extern lean_obj_res lean_name_mk_string(lean_obj_arg prefix, lean_obj_arg string);
extern lean_obj_res lean_name_mk_numeral(lean_obj_arg prefix, lean_obj_arg number);

/* Both versions store the prefix in field zero and the component in field one. */
static lean_obj_res omega_name_components(b_lean_obj_arg name) {
    lean_object *components = lean_mk_empty_array();
    for (lean_object *n = name; !lean_is_scalar(n); n = lean_ctor_get(n, 0)) {
        lean_inc(n);
        components = lean_array_push(components, n);
    }
    return components;
}

/* Rebuild the prefix chain with the official constructors, which populate its hash fields. */
static lean_obj_res omega_name_to_lean(b_lean_obj_arg name) {
    lean_object *components = omega_name_components(name);
    lean_object *prefix = lean_box(0);
    for (size_t i = lean_array_size(components); i > 0; --i) {
        lean_object *node = lean_array_get_core(components, i - 1);
        lean_object *value = lean_ctor_get(node, 1);
        if (lean_obj_tag(node) == 1) {
            prefix = lean_name_mk_string(prefix, omega_string_to_lean(value));
        } else {
            lean_inc(value);
            prefix = lean_name_mk_numeral(prefix, value);
        }
    }
    lean_dec(components);
    return prefix;
}

static lean_obj_res omega_name_from_lean(b_lean_obj_arg name) {
    lean_object *components = omega_name_components(name);
    lean_object *prefix = lean_box(0);
    for (size_t i = lean_array_size(components); i > 0; --i) {
        lean_object *node = lean_array_get_core(components, i - 1);
        uint8_t tag = lean_obj_tag(node);
        lean_object *value = lean_ctor_get(node, 1);
        if (tag == 1) value = omega_string_from_lean(value);
        else lean_inc(value);
        lean_object *next = lean_alloc_ctor(tag, 2, 0);
        lean_ctor_set(next, 0, prefix);
        lean_ctor_set(next, 1, value);
        prefix = next;
    }
    lean_dec(components);
    return prefix;
}
