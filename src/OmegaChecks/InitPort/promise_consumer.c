#include <lean/lean.h>
extern void exit(int);
extern int puts(const char *);

extern lean_obj_res omega_smoke_new(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_smoke_resolve(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_smoke_is_resolved(lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_smoke_result(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_smoke_task_get(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_smoke_task_pattern(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_smoke_task_pure(lean_obj_arg, lean_obj_arg);
extern lean_obj_res l_omegaRawTaskRead(lean_obj_arg, lean_obj_arg);
extern lean_obj_res runtime_initialize_PromiseConsumer(uint8_t builtin);

static lean_object *field(lean_object *pair, unsigned i) {
    lean_object *x = lean_ctor_get(pair, i);
    lean_inc(x);
    return x;
}
static lean_object *allocate(void) {
    lean_object *out = omega_smoke_new(lean_box(0), lean_box(0), lean_box(0));
    if (lean_ctor_get(out, 1) != lean_box(0)) exit(2);
    lean_object *handle = field(out, 0);
    lean_dec(out);
    return handle;
}
static void resolve(lean_object *p, size_t value) {
    lean_inc(p);
    lean_object *out = omega_smoke_resolve(lean_box(0), lean_box(value), p, lean_box(0));
    if (lean_ctor_get(out, 0) != lean_box(0) || lean_ctor_get(out, 1) != lean_box(0)) exit(3);
    lean_dec(out);
}
static void check_resolved(lean_object *p, size_t expected) {
    lean_inc(p);
    lean_object *out = omega_smoke_is_resolved(lean_box(0), p, lean_box(0));
    if (lean_ctor_get(out, 0) != lean_box(expected) || lean_ctor_get(out, 1) != lean_box(0)) exit(7);
    lean_dec(out);
}
static lean_object *pending_result(lean_object *promise) {
    lean_inc(promise);
    return omega_smoke_result(lean_box(0), promise);
}
static void expect(lean_object *result, size_t value) {
    if (lean_obj_tag(result) != 1 || lean_unbox(lean_ctor_get(result, 0)) != value) exit(4);
    lean_dec(result);
}
int main(void) {
    lean_object *initialized = runtime_initialize_PromiseConsumer(1);
    if (lean_io_result_is_error(initialized)) return 1;
    lean_dec(initialized);
    lean_io_mark_end_initialization();
    lean_init_task_manager();
    lean_object *p = allocate(), *q = allocate();
    if (p == q) exit(5);
    lean_object *a = pending_result(p), *b = pending_result(q);
    check_resolved(p, 0);
    resolve(p, 42);
    check_resolved(p, 1);
    check_resolved(q, 0);
    resolve(p, 23);
    resolve(q, 19);
    lean_inc(a);
    expect(omega_smoke_task_get(lean_box(0), a), 42);
    expect(l_omegaRawTaskRead(lean_box(0), a), 42);
    expect(omega_smoke_task_pattern(lean_box(0), b), 19);
    lean_object *pure = omega_smoke_task_pure(lean_box(0), lean_box(73));
    if (lean_unbox(l_omegaRawTaskRead(lean_box(0), pure)) != 73) exit(8);
    lean_dec(p);
    lean_dec(q);
    lean_object *drop = allocate();
    lean_object *t = pending_result(drop);
    lean_dec(drop);
    lean_object *none = omega_smoke_task_pattern(lean_box(0), t);
    if (none != lean_box(0)) exit(6);
    lean_finalize_task_manager();
    puts("promise creation, independent resolution, task projection, pattern matching and cancellation passed");
    return 0;
}
