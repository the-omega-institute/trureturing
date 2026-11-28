#include "../strict_name.h"

extern int puts(const char *);
extern lean_obj_res runtime_initialize_DynamicValueConsumer(uint8_t);
extern lean_obj_res omega_dynamic_pack_nat(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_dynamic_read_nat(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_dynamic_read_bool(lean_obj_arg, lean_obj_arg);
extern lean_obj_res omega_dynamic_name(lean_obj_arg);

int main(void) {
    lean_object *init = runtime_initialize_DynamicValueConsumer(1);
    if (lean_io_result_is_error(init)) return 1;
    lean_dec(init);
    lean_io_mark_end_initialization();

    lean_object *nat = lean_name_mk_string(lean_box(0), lean_mk_string("Nat"));
    lean_object *bool_name = lean_name_mk_string(
        lean_name_mk_string(lean_box(0), lean_mk_string("Omega")), lean_mk_string("Bool"));
    for (unsigned i = 0; i < 3; ++i) {
        lean_object *payload = i == 2 ? lean_uint64_to_nat(UINT64_MAX) : lean_box(i);
        lean_inc(payload);
        lean_object *packed = omega_dynamic_pack_nat(omega_name_from_lean(nat), payload);
        lean_inc(packed);
        lean_object *read = omega_dynamic_read_nat(omega_name_from_lean(nat), packed);
        if (lean_obj_tag(read) != 1 || lean_ctor_get(read, 0) != payload) return 2;
        lean_dec(read);
        lean_dec(payload);
        lean_inc(packed);
        read = omega_dynamic_read_bool(omega_name_from_lean(bool_name), packed);
        if (read != lean_box(0)) return 3;
        lean_object *strict = omega_dynamic_name(packed);
        lean_object *name = omega_name_to_lean(strict);
        lean_dec(strict);
        if (!lean_name_eq(name, nat)) return 4;
        lean_dec(name);
    }
    lean_dec(nat);
    lean_dec(bool_name);
    puts("Dynamic retained scalar and heap payloads, checked type names, and rejected different tags.");
    return 0;
}
