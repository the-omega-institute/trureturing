#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_obj_res runtime_initialize_SharedPointerConsumer(uint8_t);
extern uint8_t l_ShareCommon_Object_ptrEq(b_lean_obj_arg, b_lean_obj_arg);
extern uint8_t l_omegaTestSharedPointer(b_lean_obj_arg, b_lean_obj_arg);

static int matches(b_lean_obj_arg a, b_lean_obj_arg b, uint8_t expected) {
    return l_ShareCommon_Object_ptrEq(a, b) == expected &&
           l_omegaTestSharedPointer(a, b) == expected;
}

int main(void) {
    lean_initialize_runtime_module();
    lean_object *init = runtime_initialize_SharedPointerConsumer(1);
    if (lean_io_result_is_error(init)) return 1;
    lean_dec_ref(init);
    lean_io_mark_end_initialization();
    lean_object *first = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(first, 0, lean_box(42));
    lean_object *second = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(second, 0, lean_box(42));
    int ok = matches(first, first, 1) && matches(first, second, 0) && matches(second, first, 0);
    lean_dec(first);
    lean_dec(second);
    return ok ? 0 : 2;
}
