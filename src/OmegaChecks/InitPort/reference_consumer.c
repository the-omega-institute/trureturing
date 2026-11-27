#include <lean/lean.h>
extern int puts(const char *);
extern void exit(int);
extern lean_obj_res runtime_initialize_ReferenceConsumer(uint8_t);
extern lean_obj_res omega_ref_smoke(lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg);
static lean_obj_res allocate(lean_obj_arg input, lean_obj_arg world) {
    lean_obj_res out = omega_ref_smoke(lean_box(0), lean_box(0), input, world);
    lean_obj_res ref = lean_ctor_get(out, 0);
    if (lean_ctor_get(out, 1) != world) exit(2);
    lean_inc(ref);
    lean_dec(out);
    return ref;
}
int main(void) {
    lean_object *status = runtime_initialize_ReferenceConsumer(1);
    if (lean_io_result_is_error(status)) return 1;
    lean_dec(status);
    lean_io_mark_end_initialization();
    lean_object *first = allocate(lean_box(9), lean_box(12));
    lean_object *second = allocate(lean_box(15), lean_box(7));
    lean_object *old = lean_st_ref_swap(first, lean_box(3));
    if (first == second || lean_unbox(old) != 9 || lean_unbox(lean_st_ref_get(first)) != 3 ||
        lean_unbox(lean_st_ref_get(second)) != 15) return 3;
    lean_dec(first);
    lean_dec(second);
    puts("Strict ST.Prim.mkRef preserved the world and both independent initial values");
    return 0;
}
