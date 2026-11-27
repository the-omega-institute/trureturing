#include <lean/lean.h>
extern void exit(int);
extern int puts(const char *);
extern lean_obj_res runtime_initialize_TaskIOConsumer(uint8_t);
extern lean_obj_res omega_io_smoke_state(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_io_smoke_finished(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_io_smoke_wait(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_io_smoke_any(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_io_smoke_cancel(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_io_smoke_canceled(lean_obj_arg);
extern lean_obj_res lean_io_promise_new(void);
extern lean_obj_res lean_io_promise_result_opt(b_lean_obj_arg);
extern lean_obj_res lean_io_promise_resolve(lean_obj_arg, b_lean_obj_arg);

static lean_obj_res value(lean_obj_arg out, b_lean_obj_arg world) {
    if (lean_ctor_get(out, 1) != world) exit(2);
    lean_obj_res result = lean_ctor_get(out, 0);
    lean_inc(result);
    lean_dec(out);
    return result;
}
static lean_obj_res identity(lean_obj_arg input) {
    return input;
}
static lean_obj_res observe_cancellation(lean_obj_arg started, lean_obj_arg gate, lean_obj_arg unit) {
    lean_dec(lean_io_promise_resolve(lean_box(0), started));
    lean_dec(started);
    lean_dec(lean_task_get_own(gate));
    lean_object *world = lean_box(31);
    return value(omega_io_smoke_canceled(world), world);
}

int main(void) {
    lean_object *status = runtime_initialize_TaskIOConsumer(1);
    if (lean_io_result_is_error(status)) return 1;
    lean_dec(status);
    lean_io_mark_end_initialization();
    lean_init_task_manager();
    lean_object *type = lean_box(0), *world = lean_box(29), *p = lean_io_promise_new();
    lean_object *pending = lean_io_promise_result_opt(p);
    lean_inc(pending);
    if (value(omega_io_smoke_state(type, pending, world), world) != lean_box(LEAN_TASK_STATE_RUNNING)) return 3;
    lean_inc(pending);
    lean_object *waiting = lean_task_map_core(lean_alloc_closure((void *)identity, 1, 0), pending, 0, true, false);
    if (value(omega_io_smoke_state(type, waiting, world), world) != lean_box(LEAN_TASK_STATE_WAITING)) return 13;
    lean_inc(pending);
    if (value(omega_io_smoke_finished(type, pending, world), world) != lean_box(0)) return 4;
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, lean_box(21));
    lean_object *ready = lean_task_pure(some);
    lean_inc(pending);
    lean_object *first = value(omega_io_smoke_any(type, pending, ready, world), world);
    if (lean_obj_tag(first) != 1 || lean_unbox(lean_ctor_get(first, 0)) != 21) return 5;
    lean_dec(first);
    lean_dec(lean_io_promise_resolve(lean_mk_string("resolved"), p));
    lean_dec(p);
    lean_inc(pending);
    if (value(omega_io_smoke_state(type, pending, world), world) != lean_box(LEAN_TASK_STATE_FINISHED)) return 6;
    lean_inc(pending);
    if (value(omega_io_smoke_finished(type, pending, world), world) != lean_box(1)) return 7;
    lean_inc(pending);
    if (value(omega_io_smoke_cancel(type, pending, world), world) != lean_box(0)) return 8;
    if (value(omega_io_smoke_canceled(world), world) != lean_box(0)) return 9;
    some = value(omega_io_smoke_wait(type, pending, world), world);
    lean_object *expected = lean_mk_string("resolved");
    if (lean_obj_tag(some) != 1 || !lean_string_eq(lean_ctor_get(some, 0), expected)) return 10;
    lean_dec(some);
    lean_dec(expected);
    lean_object *started = lean_io_promise_new(), *release = lean_io_promise_new();
    lean_object *started_task = lean_io_promise_result_opt(started);
    lean_object *fn = lean_alloc_closure((void *)observe_cancellation, 3, 2);
    lean_closure_set(fn, 0, started);
    lean_closure_set(fn, 1, lean_io_promise_result_opt(release));
    lean_object *cancellable = lean_task_spawn_core(fn, 9, false);
    lean_dec(lean_task_get_own(started_task));
    lean_inc(cancellable);
    if (value(omega_io_smoke_cancel(type, cancellable, world), world) != lean_box(0)) return 11;
    lean_dec(lean_io_promise_resolve(lean_box(0), release));
    lean_dec(release);
    if (value(omega_io_smoke_wait(type, cancellable, world), world) != lean_box(1)) return 12;
    lean_finalize_task_manager();
    puts("Strict task I/O passed pending, finished, wait-any and cooperative cancellation checks");
    return 0;
}
