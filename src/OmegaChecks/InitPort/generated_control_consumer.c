#include <lean/lean.h>
#include <stdint.h>
extern lean_obj_res runtime_initialize_GeneratedControlConsumer(uint8_t);
extern uint8_t omega_generated_except(uint8_t, uint8_t);
extern uint8_t omega_generated_option(uint8_t, uint8_t);
extern uint8_t omega_generated_state(uint8_t, uint8_t);
int main(void) {
    lean_object *status = runtime_initialize_GeneratedControlConsumer(1);
    if (lean_io_result_is_error(status)) return 1;
    lean_dec(status);
    lean_io_mark_end_initialization();
    for (uint8_t x = 0; x <= 1; x++) {
        for (uint8_t y = 0; y <= 1; y++) {
            if (omega_generated_except(x, y) != (x || y)) return 2;
            if (omega_generated_option(x, y) != (x && y)) return 3;
            if (omega_generated_state(x, y) != (x && y)) return 4;
        }
    }
    return 0;
}
