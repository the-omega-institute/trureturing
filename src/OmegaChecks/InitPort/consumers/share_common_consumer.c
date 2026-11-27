#include "share_common_word.h"

extern lean_obj_res runtime_initialize_Lean_Util_ShareCommon(uint8_t);
extern lean_obj_res runtime_initialize_ShareCommonConsumer(uint8_t);
extern lean_object *l_Lean_ShareCommon_objectFactory;
extern lean_object *l_Lean_ShareCommon_persistentObjectFactory;
extern lean_obj_res omega_share_common_custom_factory(lean_obj_arg);
extern lean_obj_res omega_share_common_pair(lean_obj_arg, lean_obj_arg, lean_obj_arg);

extern lean_obj_res omega_share_common_new_state(lean_obj_arg);

static lean_object *singleton(size_t value) {
    lean_object *xs = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(xs, 0, lean_box(value));
    lean_ctor_set(xs, 1, lean_box(0));
    return xs;
}

static int shares(lean_object *factory, size_t x, size_t y, int expected_shared) {
    lean_object *a = singleton(x);
    lean_object *b = singleton(y);
    lean_inc(factory);
    lean_object *pair = omega_share_common_pair(factory, a, b);
    lean_object *left = lean_ctor_get(pair, 0);
    lean_object *right = lean_ctor_get(pair, 1);
    int ok = (left == right) == expected_shared
        && lean_unbox(lean_ctor_get(left, 0)) == x && lean_unbox(lean_ctor_get(right, 0)) == y;
    lean_dec(pair);
    return ok;
}

static int has_capacities(b_lean_obj_arg custom) {
    lean_inc(custom);
    lean_object *state = omega_share_common_new_state(custom);
    int ok = lean_nat_dec_eq(lean_ctor_get(lean_ctor_get(state, 0), 0), lean_box(1024))
          && lean_nat_dec_eq(lean_ctor_get(lean_ctor_get(state, 1), 0), lean_box(1024));
    lean_dec(state);
    return ok;
}

static lean_obj_res small_hash(lean_obj_arg key) {
    return lean_box_uint64(lean_unbox(key));
}

static int hash_result(unsigned value) {
    lean_object *result = strict_hash(lean_alloc_closure((void *)small_hash, 1, 0), lean_box(value));
    int ok = lean_nat_dec_eq(result, lean_box(value));
    lean_dec(result);
    return ok;
}

int main(void) {
    lean_object *status = runtime_initialize_ShareCommonConsumer(1);
    if (lean_io_result_is_error(status)) return 1;
    lean_dec(status);
    lean_object *custom = omega_share_common_custom_factory(lean_box(0));
    if (!has_capacities(custom) || !hash_result(0) || !hash_result(257)) return 5;
    if (!shares(custom, 1, 1, 1) || !shares(custom, 0, 1, 0)) return 4;
    lean_dec(custom);
    status = runtime_initialize_Lean_Util_ShareCommon(1);
    if (lean_io_result_is_error(status)) return 1;
    lean_dec(status);
    lean_io_mark_end_initialization();
    if (!shares(l_Lean_ShareCommon_objectFactory, 0, 0, 1) ||
        !shares(l_Lean_ShareCommon_objectFactory, 0, 1, 0)) return 2;
    if (!shares(l_Lean_ShareCommon_persistentObjectFactory, 1, 1, 1) ||
        !shares(l_Lean_ShareCommon_persistentObjectFactory, 1, 0, 0)) return 3;
    return 0;
}
