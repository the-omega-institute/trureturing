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
extern lean_obj_res omega_io_smoke_launch(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_io_smoke_map(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_io_smoke_bind(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_io_smoke_chain(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_io_smoke_collect(lean_obj_arg, lean_obj_arg, uint8_t, lean_obj_arg);
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

static lean_obj_res signal_after_gate(lean_obj_arg gate, lean_obj_arg done, lean_obj_arg world) {
    lean_dec(lean_task_get_own(gate));
    lean_inc(world);
    lean_dec(lean_io_promise_resolve(world, done));
    lean_dec(done);
    lean_object *out = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(out, 0, lean_box(0));
    lean_ctor_set(out, 1, world);
    return out;
}

static void check_effect_scheduling(lean_obj_arg type) {
    lean_object *world = lean_mk_string("task-world");
    lean_object *gate = lean_io_promise_new(), *done = lean_io_promise_new();
    lean_object *observed = lean_io_promise_result_opt(done);
    lean_object *action = lean_alloc_closure((void *)signal_after_gate, 3, 2);
    lean_closure_set(action, 0, lean_io_promise_result_opt(gate));
    lean_closure_set(action, 1, done);
    lean_inc(world);
    lean_dec(value(omega_io_smoke_launch(type, action, world), world));
    lean_dec(lean_io_promise_resolve(lean_box(0), gate));
    lean_dec(gate);
    lean_object *ran = lean_task_get_own(observed);
    if (lean_obj_tag(ran) != 1 || lean_ctor_get(ran, 0) != world) exit(14);
    lean_dec(ran);

    lean_object *source = lean_io_promise_new(), *pending = lean_io_promise_result_opt(source);
    lean_inc(world);
    lean_object *mapped = value(omega_io_smoke_map(type, pending, world), world);
    lean_inc(world);
    lean_object *bound = value(omega_io_smoke_bind(type, mapped, world), world);
    lean_dec(lean_io_promise_resolve(lean_mk_string("payload"), source));
    lean_dec(source);
    lean_object *result = lean_task_get_own(bound), *cursor = result;
    for (unsigned i = 0; i < 3; ++i) {
        if (lean_obj_tag(cursor) != 1) exit(15);
        cursor = lean_ctor_get(cursor, 0);
    }
    lean_object *expected = lean_mk_string("payload");
    if (!lean_string_eq(cursor, expected)) exit(16);
    lean_dec(expected);
    lean_dec(result);
    lean_dec(world);
}

static lean_obj_res cons(lean_obj_arg head, lean_obj_arg tail) {
    lean_object *node = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(node, 0, head);
    lean_ctor_set(node, 1, tail);
    return node;
}

static lean_obj_res signal_value(lean_obj_arg done, lean_obj_arg value, lean_obj_arg world) {
    lean_dec(lean_io_promise_resolve(value, done));
    lean_dec(done);
    lean_object *out = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(out, 0, lean_box(0));
    lean_ctor_set(out, 1, world);
    return out;
}

static void check_composite_tasks(lean_obj_arg type, lean_obj_arg world) {
    lean_object *source = lean_io_promise_new(), *done = lean_io_promise_new();
    lean_object *observed = lean_io_promise_result_opt(done);
    lean_object *fn = lean_alloc_closure((void *)signal_value, 3, 1);
    lean_closure_set(fn, 0, done);
    lean_object *pending = lean_io_promise_result_opt(source);
    lean_inc(pending);
    if (value(omega_io_smoke_chain(type, pending, fn, world), world) != lean_box(0)) exit(17);
    lean_object *list = cons(lean_task_pure(lean_box(0)), cons(pending, cons(lean_task_pure(lean_box(0)), lean_box(0))));
    lean_object *collected = value(omega_io_smoke_collect(type, list, false, world), world);
    lean_dec(lean_io_promise_resolve(lean_box(57), source));
    lean_dec(source);
    lean_object *effect = lean_task_get_own(observed);
    if (lean_obj_tag(effect) != 1 || lean_obj_tag(lean_ctor_get(effect, 0)) != 1 ||
        lean_ctor_get(lean_ctor_get(effect, 0), 0) != lean_box(57)) exit(18);
    lean_dec(effect);
    lean_object *results = lean_task_get_own(collected), *node = results;
    for (unsigned i = 0; i < 3; ++i) {
        if (lean_obj_tag(node) != 1) exit(19);
        lean_object *entry = lean_ctor_get(node, 0);
        if (i == 1) {
            if (lean_obj_tag(entry) != 1 || lean_ctor_get(entry, 0) != lean_box(57)) exit(20);
        } else if (entry != lean_box(0)) exit(21);
        node = lean_ctor_get(node, 1);
    }
    if (node != lean_box(0)) exit(22);
    lean_dec(results);
    for (unsigned sync = 0; sync < 2; ++sync) {
        lean_object *empty = value(omega_io_smoke_collect(type, lean_box(0), sync, world), world);
        if (lean_task_get_own(empty) != lean_box(0)) exit(23);
    }
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
    check_effect_scheduling(type);
    check_composite_tasks(type, world);
    lean_finalize_task_manager();
    puts("Strict task I/O passed all task states, wait-any, cancellation and effectful scheduling checks");
    return 0;
}
