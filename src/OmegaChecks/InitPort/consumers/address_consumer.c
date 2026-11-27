#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_obj_res runtime_initialize_AddressConsumer(uint8_t);
extern lean_obj_res l_omegaTestPointerAddress(b_lean_obj_arg);

static int same_address(b_lean_obj_arg value) {
    lean_object *expected = lean_usize_to_nat(lean_ptr_addr(value));
    lean_object *actual = l_omegaTestPointerAddress(value);
    int matches = lean_nat_dec_eq(actual, expected);
    lean_dec(actual);
    lean_dec(expected);
    return matches;
}

static lean_obj_res singleton(void) {
    lean_object *value = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(value, 0, lean_box(42));
    lean_ctor_set(value, 1, lean_box(0));
    return value;
}

int main(void) {
    lean_initialize_runtime_module();
    lean_object *init = runtime_initialize_AddressConsumer(1);
    if (lean_io_result_is_error(init)) return 1;
    lean_dec_ref(init);
    lean_io_mark_end_initialization();
    lean_object *a = singleton();
    lean_object *b = singleton();
    int matches = a != b && same_address(a) && same_address(b) && same_address(lean_box(0));
    lean_inc_ref(a);
    matches = matches && same_address(a);
    lean_dec_ref(a);
    lean_dec_ref(a);
    lean_dec_ref(b);
    return matches ? 0 : 2;
}
