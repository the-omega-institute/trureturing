#include <lean/lean.h>
LEAN_EXPORT lean_obj_res omega_st_mk_ref(lean_obj_arg value, lean_obj_arg world) {
    lean_obj_res ref = lean_st_mk_ref(value);
    lean_obj_res result = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result, 0, ref);
    lean_ctor_set(result, 1, world);
    return result;
}
