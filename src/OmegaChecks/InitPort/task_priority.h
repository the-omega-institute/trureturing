#pragma once
#include <lean/lean.h>

/* The strict Nat is a unary inductive. The upstream scheduler receives an unsigned
   priority, so count the predecessors in that same unsigned type. */
static unsigned omega_task_priority(lean_obj_arg priority) {
    unsigned value = 0;
    lean_object *cursor = priority;
    while (!lean_is_scalar(cursor)) {
        ++value;
        cursor = lean_ctor_get(cursor, 0);
    }
    lean_dec(priority);
    return value;
}
