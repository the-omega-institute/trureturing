#include <lean/lean.h>

#include "task_priority.h"

LEAN_EXPORT lean_obj_res omega_task_spawn(lean_obj_arg fn, lean_obj_arg priority) {
    return lean_task_spawn_core(fn, omega_task_priority(priority), false);
}

LEAN_EXPORT lean_obj_res omega_task_map(lean_obj_arg fn, lean_obj_arg task, lean_obj_arg priority, uint8_t sync) {
    return lean_task_map_core(fn, task, omega_task_priority(priority), sync, false);
}

LEAN_EXPORT lean_obj_res omega_task_bind(lean_obj_arg task, lean_obj_arg fn, lean_obj_arg priority, uint8_t sync) {
    return lean_task_bind_core(task, fn, omega_task_priority(priority), sync, false);
}
