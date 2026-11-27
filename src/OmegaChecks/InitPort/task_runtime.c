#include <lean/lean.h>

/* The strict Nat is a unary inductive. The upstream scheduler receives an unsigned
   priority, so count the predecessors in that same unsigned type. */
static unsigned omega_task_priority(lean_obj_arg priority) {
    unsigned value = 0;
    lean_object *cursor = priority;
    while (!lean_is_scalar(cursor)) {
        ++value;
        cursor = lean_ctor_get(cursor, 0);
    }
    lean_dec(priority);
    return value;
}

LEAN_EXPORT lean_obj_res omega_task_spawn(lean_obj_arg fn, lean_obj_arg priority) {
    return lean_task_spawn_core(fn, omega_task_priority(priority), false);
}

LEAN_EXPORT lean_obj_res omega_task_map(lean_obj_arg fn, lean_obj_arg task, lean_obj_arg priority, uint8_t sync) {
    return lean_task_map_core(fn, task, omega_task_priority(priority), sync, false);
}

LEAN_EXPORT lean_obj_res omega_task_bind(lean_obj_arg task, lean_obj_arg fn, lean_obj_arg priority, uint8_t sync) {
    return lean_task_bind_core(task, fn, omega_task_priority(priority), sync, false);
}
