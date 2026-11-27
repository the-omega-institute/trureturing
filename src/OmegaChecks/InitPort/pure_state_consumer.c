#include <lean/lean.h>

extern lean_obj_res runtime_initialize_PureStateConsumer(uint8_t);
extern uint8_t omega_pure_state(uint8_t);
extern lean_obj_res omega_pure_exception_state(uint8_t, uint8_t, uint8_t);

int main(void) {
    lean_object *status = runtime_initialize_PureStateConsumer(1);
    if (lean_io_result_is_error(status)) return 1;
    lean_dec(status);
    lean_io_mark_end_initialization();
    for (uint8_t a = 0; a < 2; ++a) {
        if (omega_pure_state(a) != !a) return 2;
        for (uint8_t raise = 0; raise < 2; ++raise) {
            for (uint8_t recover = 0; recover < 2; ++recover) {
                lean_object *result = omega_pure_exception_state(raise, recover, a);
                int ok = lean_obj_tag(result) == (!raise || recover)
                    && lean_unbox(lean_ctor_get(result, 0)) == (raise ? a : !a);
                lean_dec(result);
                if (!ok) return 3;
            }
        }
    }
    return 0;
}
