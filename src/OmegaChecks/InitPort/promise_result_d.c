#include "promise-result-d.c"

/* Exported Lean functions accept their erased type argument at the boxed entry. */
LEAN_EXPORT lean_obj_res omega_io_promise_result_d(lean_obj_arg promise, lean_obj_arg fallback) {
    return omega_pinned_promise_result_d(lean_box(0), promise, fallback);
}
