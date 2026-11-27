#include <lean/lean.h>

extern uint8_t lean_io_get_task_state(b_lean_obj_arg);
extern uint8_t lean_io_check_canceled(void);
extern lean_obj_res lean_io_cancel(b_lean_obj_arg);
extern lean_obj_res lean_io_wait(lean_obj_arg);
extern lean_obj_res lean_io_wait_any(b_lean_obj_arg);
extern uint8_t l_IO_hasFinished___redArg(b_lean_obj_arg);

static lean_obj_res state_result(lean_obj_arg value, lean_obj_arg world) {
    lean_object *out = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(out, 0, value);
    lean_ctor_set(out, 1, world);
    return out;
}
LEAN_EXPORT lean_obj_res omega_io_get_task_state(b_lean_obj_arg task, lean_obj_arg world) {
    return state_result(lean_box(lean_io_get_task_state(task)), world);
}
LEAN_EXPORT lean_obj_res omega_io_task_has_finished(lean_obj_arg task, lean_obj_arg world) {
    uint8_t result = l_IO_hasFinished___redArg(task);
    lean_dec(task);
    return state_result(lean_box(result), world);
}
LEAN_EXPORT lean_obj_res omega_io_wait(lean_obj_arg task, lean_obj_arg world) {
    return state_result(lean_io_wait(task), world);
}
LEAN_EXPORT lean_obj_res omega_io_wait_any(b_lean_obj_arg tasks, lean_obj_arg world) {
    return state_result(lean_io_wait_any(tasks), world);
}
LEAN_EXPORT lean_obj_res omega_io_cancel(b_lean_obj_arg task, lean_obj_arg world) {
    return state_result(lean_io_cancel(task), world);
}
LEAN_EXPORT lean_obj_res omega_io_check_canceled(lean_obj_arg world) {
    return state_result(lean_box(lean_io_check_canceled()), world);
}
