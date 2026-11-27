#include <lean/lean.h>

extern lean_obj_res runtime_initialize_Lean_Util_ShareCommon(uint8_t);
extern lean_obj_res runtime_initialize_ShareCommonConsumer(uint8_t);
extern lean_object *l_Lean_ShareCommon_objectFactory;
extern lean_object *l_Lean_ShareCommon_persistentObjectFactory;
extern lean_obj_res omega_share_common_pair(lean_obj_arg, lean_obj_arg, lean_obj_arg);

static lean_object *singleton(size_t value) {
    lean_object *xs = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(xs, 0, lean_box(value));
    lean_ctor_set(xs, 1, lean_box(0));
    return xs;
}

static int shares(lean_object *factory, size_t x, size_t y) {
    lean_object *a = singleton(x);
    lean_object *b = singleton(y);
    lean_inc(factory);
    lean_object *pair = omega_share_common_pair(factory, a, b);
    lean_object *left = lean_ctor_get(pair, 0);
    lean_object *right = lean_ctor_get(pair, 1);
    int ok = (left == right) == (x == y)
        && lean_unbox(lean_ctor_get(left, 0)) == x && lean_unbox(lean_ctor_get(right, 0)) == y;
    lean_dec(pair);
    return ok;
}

int main(void) {
    lean_object *status = runtime_initialize_Lean_Util_ShareCommon(1);
    if (lean_io_result_is_error(status)) return 1;
    lean_dec(status);
    status = runtime_initialize_ShareCommonConsumer(1);
    if (lean_io_result_is_error(status)) return 1;
    lean_dec(status);
    lean_io_mark_end_initialization();
    if (!shares(l_Lean_ShareCommon_objectFactory, 0, 0) ||
        !shares(l_Lean_ShareCommon_objectFactory, 0, 1)) return 2;
    if (!shares(l_Lean_ShareCommon_persistentObjectFactory, 1, 1) ||
        !shares(l_Lean_ShareCommon_persistentObjectFactory, 1, 0)) return 3;
    return 0;
}
