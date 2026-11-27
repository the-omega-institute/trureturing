#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_obj_res runtime_initialize_PointerHashConsumer(uint8_t);
extern uint64_t l_ShareCommon_Object_ptrHash(b_lean_obj_arg);
extern lean_obj_res l_omegaTestPointerHash(b_lean_obj_arg);

static int matches(b_lean_obj_arg value) {
    lean_object *expected = lean_uint64_to_nat(l_ShareCommon_Object_ptrHash(value));
    lean_object *actual = l_omegaTestPointerHash(value);
    int ok = lean_nat_dec_eq(expected, actual);
    lean_dec(expected);
    lean_dec(actual);
    return ok;
}

int main(void) {
    lean_initialize_runtime_module();
    lean_object *init = runtime_initialize_PointerHashConsumer(1);
    if (lean_io_result_is_error(init)) return 1;
    lean_dec_ref(init);
    lean_io_mark_end_initialization();
    lean_object *first = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(first, 0, lean_box(42));
    lean_object *second = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(second, 0, lean_box(42));
    int ok = matches(first) && matches(second) && matches(first);
    lean_dec(first);
    lean_dec(second);
    return ok ? 0 : 2;
}
