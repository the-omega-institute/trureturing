#include <lean/lean.h>

extern lean_obj_res lean_io_promise_new(void);
extern lean_obj_res lean_io_promise_resolve(lean_obj_arg value, b_lean_obj_arg promise);

extern uint8_t l_IO_Promise_isResolved___redArg(b_lean_obj_arg promise);

/* Omega.ST.Out retains both its result and its world token. */
static lean_obj_res state_result(lean_obj_arg value, lean_obj_arg state) {
    lean_object *result = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result, 0, value);
    lean_ctor_set(result, 1, state);
    return result;
}

LEAN_EXPORT lean_obj_res omega_io_promise_new(lean_obj_arg state) {
    return state_result(lean_io_promise_new(), state);
}

LEAN_EXPORT lean_obj_res omega_io_promise_resolve(
    lean_obj_arg value, b_lean_obj_arg promise, lean_obj_arg state) {
    return state_result(lean_io_promise_resolve(value, promise), state);
}

LEAN_EXPORT lean_obj_res omega_io_promise_is_resolved(lean_obj_arg promise, lean_obj_arg state) {
    uint8_t finished = l_IO_Promise_isResolved___redArg(promise);
    lean_dec(promise);
    return state_result(lean_box(finished), state);
}
