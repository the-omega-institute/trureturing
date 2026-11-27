#ifndef OMEGA_EST_OUT_ELIM_H
#define OMEGA_EST_OUT_ELIM_H
#include <lean/lean.h>

/* In each branch EST.Out.ctorElim passes its payload and world to the
   continuation selected by the caller's proof of the constructor index. */
LEAN_EXPORT lean_obj_res omega_est_out_elim(lean_obj_arg index, lean_obj_arg out, lean_obj_arg k) {
    lean_object *value = lean_ctor_get(out, 0);
    lean_object *world = lean_ctor_get(out, 1);
    lean_inc(value);
    lean_inc(world);
    lean_dec(out);
    lean_dec(index);
    return lean_apply_2(k, value, world);
}

#endif
