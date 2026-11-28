#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_obj_res runtime_initialize_SyntaxArrayConsumer(uint8_t);
extern lean_obj_res l_omegaTestMakeSyntaxArray(b_lean_obj_arg, b_lean_obj_arg);
extern lean_obj_res l_omegaTestReadSyntaxArray(b_lean_obj_arg, b_lean_obj_arg);
extern lean_obj_res l_Lean_TSyntaxArray_mkImpl(b_lean_obj_arg, b_lean_obj_arg);
extern lean_obj_res l_Lean_TSyntaxArray_rawImpl(b_lean_obj_arg, b_lean_obj_arg);

typedef lean_obj_res (*convert)(b_lean_obj_arg, b_lean_obj_arg);

static int keeps_array(convert mk, convert raw, b_lean_obj_arg xs) {
    lean_object *typed = mk(lean_box(0), xs);
    lean_object *plain = raw(lean_box(0), typed);
    int same = typed == xs && plain == xs;
    lean_dec(plain);
    lean_dec(typed);
    return same;
}

int main(void) {
    lean_initialize_runtime_module();
    lean_object *result = runtime_initialize_SyntaxArrayConsumer(1);
    if (lean_io_result_is_error(result)) return 1;
    lean_dec(result);
    lean_io_mark_end_initialization();

    lean_object *array = lean_alloc_array(1, 1);
    lean_array_set_core(array, 0, lean_box(0));
    int official = keeps_array(l_Lean_TSyntaxArray_mkImpl, l_Lean_TSyntaxArray_rawImpl, array);
    lean_dec(array);

    /* The strict array wrapper erases to its list of syntax elements. */
    lean_object *list = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(list, 0, lean_box(0));
    lean_ctor_set(list, 1, lean_box(0));
    int strict = keeps_array(l_omegaTestMakeSyntaxArray, l_omegaTestReadSyntaxArray, list);
    lean_dec(list);
    return official && strict ? 0 : 2;
}
