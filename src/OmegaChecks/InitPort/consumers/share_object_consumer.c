#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_obj_res runtime_initialize_ShareObjectConsumer(uint8_t);
extern uint8_t lean_sharecommon_eq(b_lean_obj_arg, b_lean_obj_arg);
extern uint64_t lean_sharecommon_hash(b_lean_obj_arg);
extern uint8_t l_omegaShareObjectEq(b_lean_obj_arg, b_lean_obj_arg);
extern lean_obj_res l_omegaShareObjectHash(b_lean_obj_arg);

static int matches(b_lean_obj_arg a, b_lean_obj_arg b) {
    lean_object *expected = lean_uint64_to_nat(lean_sharecommon_hash(a));
    lean_object *actual = l_omegaShareObjectHash(a);
    int ok = lean_nat_dec_eq(expected, actual) &&
             l_omegaShareObjectEq(a, b) == lean_sharecommon_eq(a, b);
    lean_dec(actual);
    lean_dec(expected);
    return ok;
}

static lean_obj_res singleton(lean_obj_arg head) {
    lean_object *xs = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(xs, 0, head);
    lean_ctor_set(xs, 1, lean_box(0));
    return xs;
}

int main(void) {
    lean_initialize_runtime_module();
    lean_object *init = runtime_initialize_ShareObjectConsumer(1);
    if (lean_io_result_is_error(init)) return 1;
    lean_dec(init);
    lean_io_mark_end_initialization();
    lean_object *a = lean_uint64_to_nat(UINT64_MAX);
    lean_object *b = lean_uint64_to_nat(UINT64_MAX);
    int ok = matches(a, a) && matches(a, b);
    lean_dec(a);
    lean_dec(b);
    a = singleton(lean_box(3));
    b = singleton(lean_box(3));
    int leaves = a != b && matches(a, b);
    a = singleton(a);
    b = singleton(b);
    ok = ok && leaves && !lean_sharecommon_eq(a, b) &&
         matches(a, a) && matches(a, b) && matches(b, a);
    lean_dec(a);
    lean_dec(b);
    return ok ? 0 : 2;
}
