#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern b_lean_obj_res l_borrowedArrayGet(lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg, lean_obj_arg);
extern b_lean_obj_res l_borrowedArrayGetChecked(lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);
extern b_lean_obj_res l_borrowedArrayUGet(lean_obj_arg, b_lean_obj_arg, lean_obj_arg, lean_obj_arg);

static lean_obj_res cons(lean_obj_arg head, lean_obj_arg tail) {
    lean_object *cell = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(cell, 0, head);
    lean_ctor_set(cell, 1, tail);
    return cell;
}

int main(void) {
    lean_initialize_runtime_module();
    lean_object *first = lean_alloc_ctor(0, 0, 0);
    lean_object *second = lean_alloc_ctor(0, 0, 0);
    lean_object *values[] = {first, second};
    lean_object *xs = cons(first, cons(second, lean_box(0)));
    lean_object *array = lean_alloc_array(2, 2);
    for (size_t i = 0; i < 2; ++i)
        lean_array_set_core(array, i, lean_alloc_ctor(0, 0, 0));
    for (size_t i = 0; i < 2; ++i) {
        lean_object *index = lean_box(i);
        lean_object *element = lean_array_get_core(array, i);
        if (lean_array_fget_borrowed(array, index) != element ||
            lean_array_get_borrowed(lean_box(0), array, index) != element ||
            lean_array_uget_borrowed(array, i) != element ||
            !lean_is_exclusive(element)) return 4;
        if (l_borrowedArrayGet(lean_box(0), xs, index, lean_box(0)) != values[i] ||
            l_borrowedArrayGetChecked(lean_box(0), lean_box(0), xs, index) != values[i] ||
            l_borrowedArrayUGet(lean_box(0), xs, index, lean_box(0)) != values[i] ||
            !lean_is_exclusive(values[i])) return 1;
    }
    lean_set_panic_messages(false);
    lean_set_exit_on_panic(false);
    lean_object *fallback = lean_alloc_ctor(0, 0, 0);
    lean_object *bad[] = {lean_box(2), lean_uint64_to_nat(UINT64_MAX)};
    for (size_t i = 0; i < 2; ++i) {
        lean_object *result = l_borrowedArrayGetChecked(lean_box(0), fallback, xs, bad[i]);
        if (result != fallback || lean_is_exclusive(fallback)) return 2;
        lean_dec(result);
        if (!lean_is_exclusive(fallback)) return 3;
        lean_object *pinned = lean_array_get_borrowed(fallback, array, bad[i]);
        if (pinned != fallback || lean_is_exclusive(fallback)) return 5;
        lean_dec(pinned);
        if (!lean_is_exclusive(fallback)) return 6;
        lean_dec(bad[i]);
    }
    lean_dec(fallback);
    lean_dec(xs);
    lean_dec(array);
    return 0;
}
