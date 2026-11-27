#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_obj_res runtime_initialize_AddressCallbackConsumer(uint8_t);
extern lean_obj_res l_omegaTestAddressCallback(b_lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res l_withPtrAddrUnsafe(lean_obj_arg, lean_obj_arg, b_lean_obj_arg, lean_obj_arg, lean_obj_arg);

static lean_object *active;
static unsigned calls;

static lean_obj_res strict_callback(lean_obj_arg n) {
    lean_object *expected = lean_usize_to_nat(lean_ptr_addr(active));
    calls += lean_nat_dec_eq(n, expected);
    lean_dec(n);
    lean_dec(expected);
    return lean_box(17);
}

static lean_obj_res official_callback(lean_obj_arg n) {
    calls += lean_unbox_usize(n) == lean_ptr_addr(active);
    lean_dec(n);
    return lean_box(17);
}

static int check(b_lean_obj_arg x) {
    active = x;
    calls = 0;
    lean_object *official = l_withPtrAddrUnsafe(lean_box(0), lean_box(0), x,
        lean_alloc_closure((void *)official_callback, 1, 0), lean_box(0));
    lean_object *strict = l_omegaTestAddressCallback(x,
        lean_alloc_closure((void *)strict_callback, 1, 0), lean_box(0));
    int ok = calls == 2 && official == lean_box(17) && strict == official;
    lean_dec(strict);
    lean_dec(official);
    return ok;
}

int main(void) {
    lean_initialize_runtime_module();
    lean_object *init = runtime_initialize_AddressCallbackConsumer(1);
    if (lean_io_result_is_error(init)) return 1;
    lean_dec(init);
    lean_io_mark_end_initialization();
    lean_object *cell = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(cell, 0, lean_box(3));
    lean_ctor_set(cell, 1, lean_box(0));
    int ok = check(cell) && check(lean_box(0));
    lean_dec(cell);
    return ok ? 0 : 2;
}
