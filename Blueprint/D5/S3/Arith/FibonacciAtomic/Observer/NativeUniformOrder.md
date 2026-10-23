# NativeUniformOrder

## Abstract

NativeUniformOrder

The comparator is the original Boolean-list lexicographic order. Filtering, native rightmost deduplication and insertion sorting preserve the exact finite-set ordering used by symbolicOrdered.

**Theorem 1.1 (address_lt_prim).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformOrder.address_lt_prim`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformOrder.address_lt_prim` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A decreasing recursion over pairs of finite Boolean addresses decides the original native lexicographic strict order.

**Theorem 1.2 (address_le_prim).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformOrder.address_le_prim`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformOrder.address_le_prim` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The non-strict comparator combines native strict order and equality for canonical insertion sorting.

**Theorem 1.3 (symbolic_ordered_prim).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformOrder.symbolic_ordered_prim`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformOrder.symbolic_ordered_prim` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive filtering, deduplication and sorting produce exactly the native list of reached cut addresses for arbitrary finite input lists, including duplicates and unsorted addresses.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformOrder.address_le_prim`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformOrder.address_lt_prim`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformOrder.symbolic_ordered_prim`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree](NativeUniformTree.md)
