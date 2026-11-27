#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);

typedef lean_obj_res traversal(lean_obj_arg, lean_obj_arg, lean_obj_arg,
                               lean_obj_arg, lean_obj_arg, lean_obj_arg);
extern traversal omega_test_array_map_unsafe;
extern traversal omega_test_array_index_map_unsafe;
extern traversal l_Array_mapMUnsafe;
extern traversal l_Array_mapFinIdxMUnsafe;

static size_t visits, stop, exclusivity;
static bool called_pure, branch;
static lean_object *first_branch;

static lean_obj_res pure(lean_obj_arg type, lean_obj_arg x) {
    (void)type;
    called_pure = true;
    return x;
}

static lean_obj_res bind(lean_obj_arg a, lean_obj_arg b, lean_obj_arg x, lean_obj_arg next) {
    (void)a;
    (void)b;
    if (visits == stop) {
        lean_dec(x);
        lean_dec(next);
        return lean_box(0);
    }
    if (branch && visits == 2) {
        lean_inc(next);
        first_branch = lean_apply_1(next, lean_box(77));
    }
    return lean_apply_1(next, x);
}

static lean_obj_res callback(lean_obj_arg x) {
    if (lean_is_exclusive(x)) exclusivity++;
    size_t v = lean_unbox(lean_ctor_get(x, 0));
    lean_dec(x);
    if (v != visits++) return lean_box(200);
    return lean_box(10 + v);
}

static lean_obj_res indexed(lean_obj_arg i, lean_obj_arg x, lean_obj_arg proof) {
    (void)proof;
    if (lean_unbox(i) != visits) { lean_dec(x); return lean_box(100); }
    return callback(x);
}

static lean_obj_res dictionary(void) {
    lean_object *app = lean_alloc_ctor(0, 5, 0);
    for (unsigned i = 2; i < 5; ++i) lean_ctor_set(app, i, lean_box(0));
    lean_ctor_set(app, 0, lean_box(0));
    lean_ctor_set(app, 1, lean_alloc_closure((void*)pure, 2, 0));
    lean_object *inst = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(inst, 0, app);
    lean_ctor_set(inst, 1, lean_alloc_closure((void*)bind, 4, 0));
    return inst;
}

static lean_obj_res input(bool strict, size_t n) {
    lean_object *xs = strict ? lean_box(0) : lean_alloc_array(n, n);
    for (size_t k = n; k > 0; k--) {
        lean_object *x = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(x, 0, lean_box(k - 1));
        if (strict) {
            lean_object *tail = xs;
            xs = lean_alloc_ctor(1, 2, 0);
            lean_ctor_set(xs, 0, x);
            lean_ctor_set(xs, 1, tail);
        } else lean_array_set_core(xs, k - 1, x);
    }
    return xs;
}

static int check(bool strict, bool with_index, bool shared, size_t n, size_t end) {
    lean_object *xs = input(strict, n);
    lean_object *original = xs;
    if (shared) lean_inc(xs);
    lean_object *inst = dictionary();
    lean_object *f = with_index ? lean_alloc_closure((void*)indexed, 3, 0) :
                                 lean_alloc_closure((void*)callback, 1, 0);
    visits = 0; exclusivity = 0; called_pure = false; stop = end;
    lean_object *result;
    lean_object *erased = lean_box(0);
    if (with_index) {
        result = strict ? omega_test_array_index_map_unsafe(erased, erased, erased, inst, xs, f) :
                          l_Array_mapFinIdxMUnsafe(erased, erased, erased, inst, xs, f);
    } else {
        result = strict ? omega_test_array_map_unsafe(erased, erased, erased, inst, f, xs) :
                          l_Array_mapMUnsafe(erased, erased, erased, inst, f, xs);
    }
    size_t expected = end < n ? end : n;
    if (visits != expected || exclusivity != (shared ? 0 : visits) || called_pure != (end > n)) return 1;
    if (called_pure) {
        if ((result == original) != (!shared || n == 0)) return 2;
        lean_object *tail = result;
        for (size_t i = 0; i < n; i++) {
            lean_object *val = strict ? lean_ctor_get(tail, 0) : lean_array_get_core(result, i);
            if (!lean_is_scalar(val) || lean_unbox(val) != 10 + i) return 3;
            if (strict) tail = lean_ctor_get(tail, 1);
        }
        if (strict ? !lean_is_scalar(tail) : lean_array_size(result) != n) return 4;
    }
    if (branch) {
        if (!first_branch || first_branch == result || first_branch == original) return 5;
        lean_object *first = strict ? lean_ctor_get(first_branch, 0) : lean_array_get_core(first_branch, 0);
        lean_object *last = strict ? lean_ctor_get(lean_ctor_get(first_branch, 1), 0) : lean_array_get_core(first_branch, 1);
        if (first != lean_box(10) || last != lean_box(77)) return 6;
        lean_dec(first_branch);
        first_branch = NULL;
    }
    if (shared) lean_dec(original);
    lean_dec(result);
    return 0;
}

int main(void) {
    lean_initialize_runtime_module();
    for (unsigned strict = 0; strict < 2; strict++) {
        for (unsigned indexed = 0; indexed < 2; indexed++) {
            for (unsigned shared = 0; shared < 2; shared++) {
                int result = check(strict, indexed, shared, 3, 4);
                if (!result) result = check(strict, indexed, shared, 3, 2);
                if (!result) result = check(strict, indexed, shared, 0, 1);
                branch = true;
                if (!result) result = check(strict, indexed, shared, 2, 3);
                branch = false;
                if (result) return result + 8 * strict + 16 * indexed + 32 * shared;
            }
        }
    }
    return 0;
}
