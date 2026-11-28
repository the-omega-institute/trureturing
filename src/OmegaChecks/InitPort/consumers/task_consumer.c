#include <lean/lean.h>
extern int puts(const char *);
extern lean_obj_res runtime_initialize_TaskConsumer(uint8_t);
extern lean_obj_res omega_task_smoke_spawn(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_task_smoke_map(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_task_smoke_bind(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_task_smoke_read(lean_obj_arg, lean_obj_arg);
extern lean_obj_res lean_io_promise_new(void);
extern lean_obj_res lean_io_promise_result_opt(b_lean_obj_arg);
extern lean_obj_res lean_io_promise_resolve(lean_obj_arg, b_lean_obj_arg);

int main(void) {
    lean_object *status = runtime_initialize_TaskConsumer(1);
    if (lean_io_result_is_error(status)) return 1;
    lean_dec(status);
    lean_io_mark_end_initialization();
    lean_init_task_manager();
    lean_object *type = lean_box(0);
    lean_object *spawned = omega_task_smoke_spawn(type, lean_mk_string("spawned"));
    lean_object *result = omega_task_smoke_read(type, spawned);
    lean_object *expected = lean_mk_string("spawned");
    if (!lean_string_eq(result, expected)) return 2;
    lean_dec(result);
    lean_dec(expected);
    lean_object *promise = lean_io_promise_new();
    lean_object *pending = lean_io_promise_result_opt(promise);
    lean_object *mapped = omega_task_smoke_map(type, type, pending, lean_mk_string("mapped"));
    lean_object *bound = omega_task_smoke_bind(type, mapped);
    lean_dec(lean_io_promise_resolve(lean_box(39), promise));
    lean_dec(promise);
    result = omega_task_smoke_read(type, bound);
    expected = lean_mk_string("mapped");
    if (!lean_string_eq(result, expected)) return 3;
    lean_dec(expected);
    lean_dec(result);
    lean_finalize_task_manager();
    puts("Strict task spawn, pending map and bind preserved their results");
    return 0;
}
