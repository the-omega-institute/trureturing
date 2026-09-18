#include <lean/lean.h>
#include <stdint.h>

/* The caller supplies metadata from an engine-owned CompactedRegion. Never
 * traverse an object graph or read a relocated/unmapped buffer here. Returning
 * zero retains the caller's complete serialization check. The exported Lean
 * declaration has owned object arguments and an object-valued Nat result. */
LEAN_EXPORT lean_obj_res lean_dtr_mapped_image_match(
    lean_obj_arg root, lean_obj_arg coordinates, lean_obj_arg bytes) {
    int matches = 0;
    if (!lean_is_scalar(root) && lean_array_size(coordinates) == 4) {
        size_t size = lean_unbox_usize(lean_array_uget_borrowed(coordinates, 0));
        uintptr_t base = lean_unbox_usize(lean_array_uget_borrowed(coordinates, 1));
        size_t offset = lean_unbox_usize(lean_array_uget_borrowed(coordinates, 2));
        size_t mapped = lean_unbox_usize(lean_array_uget_borrowed(coordinates, 3));
        uintptr_t address = (uintptr_t) root;
        if (mapped == 1 && size > 0 && offset < size && address >= offset &&
            base != 0 && base <= UINTPTR_MAX - size && address - offset == base &&
            lean_sarray_size(bytes) == size) {
            matches = __builtin_memcmp((const void *) base, lean_sarray_cptr(bytes), size) == 0;
        }
    }
    lean_dec(root);
    lean_dec(coordinates);
    lean_dec(bytes);
    return lean_box(matches ? 1 : 0);
}
