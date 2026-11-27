#include "strict_string.h"

LEAN_EXPORT lean_obj_res omega_string_utf8(b_lean_obj_arg text) {
    return omega_bytes_fresh(lean_ctor_get(text, 0));
}

LEAN_EXPORT lean_obj_res omega_string_mark(lean_obj_arg text) {
    if (lean_is_exclusive(text)) {
        lean_ctor_set_uint8(text, sizeof(void *), 1);
        return text;
    }
    lean_object *alias;
    lean_object *native = omega_string_take_native(text, &alias);
    native = lean_string_mark_linear(native);
    lean_dec_ref(alias);
    lean_object *result = omega_string_from_lean(native);
    lean_dec_ref(native);
    return result;
}

LEAN_EXPORT lean_obj_res omega_string_propagate(b_lean_obj_arg source, lean_obj_arg target) {
    return lean_ctor_get_uint8(source, sizeof(void *)) ? omega_string_mark(target) : target;
}
