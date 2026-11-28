#include <lean/lean.h>

extern lean_obj_res omega_type_name_round_trip(lean_obj_arg);
extern lean_obj_res omega_type_name_nested(lean_obj_arg);
extern lean_obj_res l_Omega_TypeName_mk(lean_obj_arg, b_lean_obj_arg);
extern lean_obj_res l___private_OmegaInit_Dynamic_0__Omega_TypeName_typeNameImpl(lean_obj_arg, b_lean_obj_arg);
extern lean_obj_res runtime_initialize_TypeNameConsumer(uint8_t builtin);

int main(void) {
    lean_object *init = runtime_initialize_TypeNameConsumer(1);
    if (lean_io_result_is_error(init)) return 1;
    lean_dec(init);
    lean_io_mark_end_initialization();
    lean_object *name = lean_box(0);
    for (unsigned i = 0; i < 4; ++i) {
        lean_inc(name);
        lean_object *result = omega_type_name_round_trip(name);
        if (result != name) return 2;
        lean_dec(result);
        lean_object *instance = l_Omega_TypeName_mk(lean_box(0), name);
        result = l___private_OmegaInit_Dynamic_0__Omega_TypeName_typeNameImpl(lean_box(0), instance);
        if (result != name) return 3;
        lean_dec(result);
        lean_dec(instance);
        name = omega_type_name_nested(name);
    }
    lean_dec(name);
    return 0;
}
