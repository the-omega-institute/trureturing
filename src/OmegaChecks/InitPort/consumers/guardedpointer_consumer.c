#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_obj_res runtime_initialize_GuardedPointerConsumer(uint8_t);
extern uint8_t omega_test_guarded_identity(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern uint8_t l_withPtrEqUnsafe(lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg, lean_obj_arg, lean_obj_arg);

static unsigned callback_calls;
static uint8_t callback_result;

static lean_obj_res fallback(lean_obj_arg unit) {
    ++callback_calls;
    return lean_box(callback_result);
}

static int guarded(b_lean_obj_arg a, b_lean_obj_arg b, uint8_t result, unsigned calls) {
    callback_result = result;
    callback_calls = 0;
    uint8_t pinned = l_withPtrEqUnsafe(lean_box(0), a, b,
        lean_alloc_closure((void *)fallback, 1, 0), lean_box(0));
    if (pinned != result || callback_calls != calls) return 0;

    callback_calls = 0;
    lean_inc(a);
    lean_inc(b);
    uint8_t strict = omega_test_guarded_identity(lean_box(0), a, b,
        lean_alloc_closure((void *)fallback, 1, 0), lean_box(0));
    return strict == pinned && callback_calls == calls;
}

static lean_obj_res singleton(unsigned n) {
    lean_object *value = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(value, 0, lean_box(n));
    lean_ctor_set(value, 1, lean_box(0));
    return value;
}

int main(void) {
    lean_initialize_runtime_module();
    lean_object *init = runtime_initialize_GuardedPointerConsumer(1);
    if (lean_io_result_is_error(init)) return 1;
    lean_dec_ref(init);
    lean_io_mark_end_initialization();

    lean_object *value = singleton(42);
    lean_object *copy = singleton(42);
    lean_object *different = singleton(17);
    if (!guarded(value, value, 1, 0) || !guarded(value, copy, 1, 1) ||
        !guarded(value, different, 0, 1) || !guarded(lean_box(3), lean_box(3), 1, 0) ||
        !guarded(lean_box(3), lean_box(4), 0, 1)) return 2;
    lean_dec_ref(copy);
    lean_dec_ref(different);
    lean_dec_ref(value);
    return 0;
}
