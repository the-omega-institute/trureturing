#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_obj_res runtime_initialize_PersistentConsumer(uint8_t);
extern lean_obj_res omega_test_persistent(lean_obj_arg, lean_obj_arg, lean_obj_arg);

static int check(lean_obj_arg value, b_lean_obj_arg world) {
    uintptr_t original = (uintptr_t)value;
    lean_inc_ref(world);
    lean_object *out = omega_test_persistent(lean_box(0), value, world);
    int match = lean_obj_tag(out) == 0 && (uintptr_t)lean_ctor_get(out, 0) == original &&
                lean_ctor_get(out, 1) == world;
    lean_dec_ref(out);
    return match;
}

int main(void) {
    lean_initialize_runtime_module();
    lean_object *init = runtime_initialize_PersistentConsumer(1);
    if (lean_io_result_is_error(init)) return 1;
    lean_dec_ref(init);
    lean_io_mark_end_initialization();

    lean_object *child = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(child, 0, lean_box(7));
    lean_object *parent = lean_alloc_ctor(0, 2, 0);
    lean_inc_ref(child);
    lean_ctor_set(parent, 0, child);
    lean_ctor_set(parent, 1, child);
    lean_object *world = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(world, 0, lean_box(0));
    lean_inc_ref(parent);
    if (lean_is_persistent(parent) || lean_is_persistent(child) || !check(parent, world) ||
        !lean_is_persistent(parent) || !lean_is_persistent(child) || lean_is_persistent(world)) return 2;
    if (!check(parent, world) || !check(lean_box(42), world)) return 3;
    lean_dec_ref(world);
    return 0;
}
