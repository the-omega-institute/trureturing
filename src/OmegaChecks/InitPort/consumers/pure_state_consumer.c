#include <lean/lean.h>

extern lean_obj_res runtime_initialize_PureStateConsumer(uint8_t);
extern uint8_t omega_pure_state(uint8_t);
extern lean_obj_res omega_pure_exception_state(uint8_t, uint8_t, uint8_t);

extern uint8_t omega_state_instances(uint8_t);
extern uint8_t omega_state_elim(uint8_t, uint8_t);
extern lean_obj_res omega_exception_instances(uint8_t, uint8_t, uint8_t);

static int is_result(lean_obj_arg result, int ok, uint8_t value) {
    int valid = lean_obj_tag(result) == ok && lean_unbox(lean_ctor_get(result, 0)) == value;
    lean_dec(result);
    return valid;
}

int main(void) {
    lean_object *status = runtime_initialize_PureStateConsumer(1);
    if (lean_io_result_is_error(status)) return 1;
    lean_dec(status);
    lean_io_mark_end_initialization();
    for (uint8_t a = 0; a < 2; ++a) {
        if (omega_pure_state(a) != !a || omega_state_instances(a) != !a) return 2;
        for (uint8_t raise = 0; raise < 2; ++raise) {
            if (omega_state_elim(raise, a) != (raise ? a : !a)) return 4;
            for (uint8_t recover = 0; recover < 2; ++recover) {
                if (!is_result(omega_pure_exception_state(raise, recover, a), !raise || recover, raise ? a : !a)) return 3;
                if (!is_result(omega_exception_instances(raise, recover, a), !raise || recover, !a)) return 5;
            }
        }
    }
    return 0;
}
