#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_obj_res runtime_initialize_PointerComparisonConsumer(uint8_t);
extern uint8_t l_omegaTestPointerEq(b_lean_obj_arg, b_lean_obj_arg);
extern uint8_t l_omegaTestGuardedPointerEq(b_lean_obj_arg, b_lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern uint8_t l_ptrEq(lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);
extern uint8_t l_withPtrEqUnsafe(lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg, lean_obj_arg, lean_obj_arg);

static unsigned calls;

static lean_obj_res fallback(lean_obj_arg unit) {
    ++calls;
    return lean_box(0);
}

static int compare(b_lean_obj_arg a, b_lean_obj_arg b, uint8_t equal) {
    if (l_ptrEq(lean_box(0), a, b) != equal || l_omegaTestPointerEq(a, b) != equal) return 0;
    calls = 0;
    uint8_t official = l_withPtrEqUnsafe(lean_box(0), a, b,
        lean_alloc_closure((void *)fallback, 1, 0), lean_box(0));
    if (official != equal || calls != (unsigned)!equal) return 0;
    calls = 0;
    uint8_t strict = l_omegaTestGuardedPointerEq(a, b,
        lean_alloc_closure((void *)fallback, 1, 0), lean_box(0));
    return strict == official && calls == (unsigned)!equal;
}

static lean_obj_res singleton(unsigned n) {
    lean_object *list = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(list, 0, lean_box(n));
    lean_ctor_set(list, 1, lean_box(0));
    return list;
}

int main(void) {
    lean_initialize_runtime_module();
    lean_object *init = runtime_initialize_PointerComparisonConsumer(1);
    if (lean_io_result_is_error(init)) return 1;
    lean_dec_ref(init);
    lean_io_mark_end_initialization();
    lean_object *a = singleton(3);
    lean_object *b = singleton(3);
    int ok = compare(a, a, 1) && compare(a, b, 0) && compare(lean_box(0), lean_box(0), 1) &&
             compare(lean_box(0), b, 0);
    lean_dec(a);
    lean_dec(b);
    return ok ? 0 : 2;
}
