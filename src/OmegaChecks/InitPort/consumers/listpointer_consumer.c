#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_obj_res runtime_initialize_ListPointerConsumer(uint8_t);
extern uint8_t l_ptrEqList(lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);
extern uint8_t l_omegaTestListPointer(b_lean_obj_arg, b_lean_obj_arg);

static int matches(b_lean_obj_arg xs, b_lean_obj_arg ys, uint8_t expected) {
    return l_ptrEqList(lean_box(0), xs, ys) == expected && l_omegaTestListPointer(xs, ys) == expected;
}

static lean_obj_res cons(b_lean_obj_arg head, b_lean_obj_arg tail) {
    lean_object *cell = lean_alloc_ctor(1, 2, 0);
    lean_inc(head);
    lean_inc(tail);
    lean_ctor_set(cell, 0, head);
    lean_ctor_set(cell, 1, tail);
    return cell;
}

int main(void) {
    lean_initialize_runtime_module();
    lean_object *init = runtime_initialize_ListPointerConsumer(1);
    if (lean_io_result_is_error(init)) return 1;
    lean_dec_ref(init);
    lean_io_mark_end_initialization();
    lean_object *nil = lean_box(0);
    lean_object *a = cons(lean_box(3), nil);
    lean_object *b = cons(lean_box(3), nil);
    lean_object *as = cons(a, nil);
    lean_object *bs = cons(b, nil);
    lean_object *aa = cons(a, as);
    lean_object *same = cons(a, as);
    lean_object *ab = cons(a, bs);
    int ok = matches(nil, nil, 1) && matches(nil, as, 0) && matches(as, nil, 0) &&
             matches(aa, same, 1) && matches(aa, ab, 0) && matches(as, bs, 0) && matches(as, aa, 0);
    lean_dec(aa);
    lean_dec(same);
    lean_dec(ab);
    lean_dec(as);
    lean_dec(bs);
    lean_dec(a);
    lean_dec(b);
    return ok ? 0 : 2;
}
