#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_obj_res runtime_initialize_ExclusiveConsumer(uint8_t);
extern uint8_t l_omegaTestExclusive(b_lean_obj_arg);

static int matches(b_lean_obj_arg value, uint8_t expected) {
    return lean_is_exclusive_obj(value) == expected &&
           l_omegaTestExclusive(value) == expected &&
           lean_is_exclusive_obj(value) == expected;
}

int main(void) {
    lean_initialize_runtime_module();
    lean_object *init = runtime_initialize_ExclusiveConsumer(1);
    if (lean_io_result_is_error(init)) return 1;
    lean_dec_ref(init);
    lean_io_mark_end_initialization();

    lean_object *value = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(value, 0, lean_box(42));
    lean_ctor_set(value, 1, lean_box(0));
    if (!matches(value, 1)) return 2;
    lean_inc_ref(value);
    if (!matches(value, 0)) return 3;
    lean_dec_ref(value);
    if (!matches(value, 1)) return 4;
    lean_mark_persistent(value);
    if (!matches(value, 0)) return 5;
    return 0;
}
