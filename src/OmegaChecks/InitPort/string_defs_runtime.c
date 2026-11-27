#include <lean/lean.h>

LEAN_EXPORT lean_obj_res omega_string_utf8(b_lean_obj_arg bytes) {
    lean_inc(bytes);
    return bytes;
}
