#include <lean/lean.h>

LEAN_EXPORT lean_obj_res omega_task_spawn(lean_obj_arg fn, lean_obj_arg priority) {
    return lean_task_spawn(fn, priority);
}

LEAN_EXPORT lean_obj_res omega_task_map(lean_obj_arg fn, lean_obj_arg task, lean_obj_arg priority, uint8_t sync) {
    return lean_task_map(fn, task, priority, sync);
}

LEAN_EXPORT lean_obj_res omega_task_bind(lean_obj_arg task, lean_obj_arg fn, lean_obj_arg priority, uint8_t sync) {
    return lean_task_bind(task, fn, priority, sync);
}
