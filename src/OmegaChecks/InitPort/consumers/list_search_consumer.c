#include <lean/lean.h>

extern lean_obj_res runtime_initialize_ListSearchConsumer(uint8_t);
extern uint8_t omega_test_list_search(uint8_t, lean_obj_arg, lean_obj_arg);

static unsigned calls;
static bool ordered;

static lean_obj_res predicate(lean_obj_arg universal, lean_obj_arg stop, lean_obj_arg value) {
    ordered = ordered && lean_unbox(value) == calls;
    ++calls;
    bool hit = lean_unbox(value) == lean_unbox(stop);
    return lean_box(lean_unbox(universal) ? !hit : hit);
}

static bool check(bool universal, unsigned length, unsigned stop) {
    lean_object *xs = lean_box(0);
    for (unsigned i = length; i > 0; --i) {
        lean_object *cons = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(cons, 0, lean_box(i - 1));
        lean_ctor_set(cons, 1, xs);
        xs = cons;
    }
    lean_object *callback = lean_alloc_closure((void *)predicate, 3, 2);
    lean_closure_set(callback, 0, lean_box(universal));
    lean_closure_set(callback, 1, lean_box(stop));
    ordered = true;
    calls = 0;
    bool result = omega_test_list_search(universal, callback, xs);
    bool hit = stop < length;
    return ordered && calls == (hit ? stop + 1 : length) && result == (universal ? !hit : hit);
}

int main(void) {
    lean_object *initialized = runtime_initialize_ListSearchConsumer(1);
    if (lean_io_result_is_error(initialized)) return 1;
    lean_dec_ref(initialized);
    lean_io_mark_end_initialization();
    for (unsigned length = 0; length <= 16; ++length)
        for (unsigned stop = 0; stop <= 17; ++stop)
            if (!check(false, length, stop) || !check(true, length, stop)) return 2;
    return 0;
}
