#include <lean/lean.h>

extern lean_obj_res runtime_initialize_MacroMethodsConsumer(uint8_t builtin);
extern lean_obj_res omega_macro_methods_query(lean_obj_arg, lean_obj_arg, lean_obj_arg);

static lean_obj_res has_decl(lean_obj_arg answer, lean_obj_arg name, lean_obj_arg context, lean_obj_arg state) {
    lean_dec(name);
    lean_dec(context);
    lean_object *result = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result, 0, answer);
    lean_ctor_set(result, 1, state);
    return result;
}

int main(void) {
    lean_object *init = runtime_initialize_MacroMethodsConsumer(1);
    if (lean_io_result_is_error(init)) return 1;
    lean_dec(init);
    lean_io_mark_end_initialization();
    for (size_t answer = 0; answer <= 1; ++answer) {
        lean_object *callback = lean_alloc_closure((void *)has_decl, 4, 1);
        lean_closure_set(callback, 0, lean_box(answer));
        lean_object *methods = lean_alloc_ctor(0, 5, 0);
        for (unsigned i = 0; i < 5; ++i) lean_ctor_set(methods, i, i == 2 ? callback : lean_box(0));
        lean_object *context = lean_alloc_ctor(0, 6, 0);
        for (unsigned i = 0; i < 6; ++i) lean_ctor_set(context, i, lean_box(0));
        lean_object *state = lean_box(31 + answer);
        lean_object *result = omega_macro_methods_query(methods, context, state);
        if (lean_obj_tag(result) != 0 || lean_unbox(lean_ctor_get(result, 0)) != answer ||
            lean_ctor_get(result, 1) != state) return 2;
        lean_dec(result);
    }
    return 0;
}
