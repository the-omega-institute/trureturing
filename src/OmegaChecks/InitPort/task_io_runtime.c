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

#include "task_priority.h"

extern lean_obj_res lean_io_as_task(lean_obj_arg, lean_obj_arg);
extern lean_obj_res lean_io_map_task(lean_obj_arg, lean_obj_arg, lean_obj_arg, uint8_t);
extern lean_obj_res lean_io_bind_task(lean_obj_arg, lean_obj_arg, lean_obj_arg, uint8_t);

/* The official worker returns the payload. A strict worker receives a world
   and returns ST.Out; its final world belongs to that independent execution. */
static lean_obj_res take_payload(lean_obj_arg out) {
    lean_object *payload = lean_ctor_get(out, 0);
    lean_inc(payload);
    lean_dec(out);
    return payload;
}

static lean_obj_res run_action(lean_obj_arg action, lean_obj_arg world, lean_obj_arg native_world) {
    return take_payload(lean_apply_1(action, world));
}

static lean_obj_res continue_action(lean_obj_arg action, lean_obj_arg world,
                                    lean_obj_arg input, lean_obj_arg native_world) {
    return take_payload(lean_apply_2(action, input, world));
}

static lean_obj_res wrap_action(void *entry, unsigned arity, lean_obj_arg action, b_lean_obj_arg world) {
    lean_object *fn = lean_alloc_closure(entry, arity, 2);
    lean_inc(world);
    lean_closure_set(fn, 0, action);
    lean_closure_set(fn, 1, world);
    return fn;
}

LEAN_EXPORT lean_obj_res omega_io_as_task(lean_obj_arg action, lean_obj_arg priority, lean_obj_arg world) {
    lean_object *fn = wrap_action((void *)run_action, 3, action, world);
    return state_result(lean_io_as_task(fn, lean_box(omega_task_priority(priority))), world);
}

LEAN_EXPORT lean_obj_res omega_io_map_task(lean_obj_arg action, lean_obj_arg task,
                                           lean_obj_arg priority, uint8_t sync, lean_obj_arg world) {
    lean_object *fn = wrap_action((void *)continue_action, 4, action, world);
    return state_result(lean_io_map_task(fn, task, lean_box(omega_task_priority(priority)), sync), world);
}

LEAN_EXPORT lean_obj_res omega_io_bind_task(lean_obj_arg task, lean_obj_arg action,
                                            lean_obj_arg priority, uint8_t sync, lean_obj_arg world) {
    lean_object *fn = wrap_action((void *)continue_action, 4, action, world);
    return state_result(lean_io_bind_task(task, fn, lean_box(omega_task_priority(priority)), sync), world);
}
