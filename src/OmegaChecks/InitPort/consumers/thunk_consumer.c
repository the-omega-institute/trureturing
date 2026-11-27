#include <lean/lean.h>
extern lean_obj_res runtime_initialize_ThunkConsumer(uint8_t);
extern lean_obj_res omega_memo_make(lean_obj_arg);
extern lean_obj_res omega_memo_pure(lean_obj_arg);
extern lean_obj_res omega_memo_get(lean_obj_arg);
extern lean_obj_res omega_memo_field(lean_obj_arg);
extern lean_obj_res omega_memo_impl(lean_obj_arg);
extern lean_obj_res omega_memo_cases(lean_obj_arg);
extern lean_obj_res omega_memo_map(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_memo_bind(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_memo_default(lean_obj_arg);

static unsigned base_calls, map_calls, bind_calls;

static lean_obj_res base(lean_obj_arg unit) {
    ++base_calls;
    return lean_box(21);
}

static lean_obj_res twice(lean_obj_arg value) {
    ++map_calls;
    return lean_box(2 * lean_unbox(value));
}

static lean_obj_res plus_one(lean_obj_arg value) {
    ++bind_calls;
    return omega_memo_pure(lean_box(lean_unbox(value) + 1));
}

static int check_all_readers(lean_object *thunk, unsigned expected) {
    lean_object *(*readers[])(lean_object *) = {
        omega_memo_get, omega_memo_field, omega_memo_impl, omega_memo_cases
    };
    for (unsigned i = 0; i < sizeof(readers) / sizeof(readers[0]); ++i) {
        lean_inc(thunk);
        if (readers[i](thunk) != lean_box(expected)) return 0;
    }
    return 1;
}

int main(void) {
    lean_object *initialized = runtime_initialize_ThunkConsumer(1);
    if (lean_io_result_is_error(initialized)) return 1;
    lean_dec(initialized);
    lean_io_mark_end_initialization();

    lean_object *source = omega_memo_make(lean_alloc_closure((void *)base, 1, 0));
    lean_inc(source);
    lean_object *mapped = omega_memo_map(lean_alloc_closure((void *)twice, 1, 0), source);
    lean_inc(mapped);
    lean_object *bound = omega_memo_bind(mapped, lean_alloc_closure((void *)plus_one, 1, 0));
    if (base_calls || map_calls || bind_calls) return 2;
    if (!check_all_readers(bound, 43) || !check_all_readers(source, 21) || !check_all_readers(mapped, 42)) return 3;
    if (base_calls != 1 || map_calls != 1 || bind_calls != 1) return 4;
    lean_dec(source);
    lean_dec(mapped);
    lean_dec(bound);

    lean_object *inhabited = omega_memo_default(lean_box(13));
    if (!check_all_readers(inhabited, 13)) return 5;
    lean_dec(inhabited);
    return 0;
}
