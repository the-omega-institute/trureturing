# Retain Actual States While Supplying the Parent

## Abstract

The parent uses its original retained states, chosen child cycles and exact opening inventories throughout.

**Theorem 1.1 (Choose the Parent and Its Actual Children Once).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateSuppliers.parent_from_state_suppliers`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateSuppliers.parent_from_state_suppliers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

From complete old-order states with their parity flags, the construction chooses the special path and ordinary cycles once. The P child is attached to the specified old P state. The output saves these actual children, their literal openings, and the support and edge identities of the same parent cycle.

**Theorem 1.2 (Earn the Three Parent Edge Invariants).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateSuppliers.state_parent_retention`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateSuppliers.state_parent_retention` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same chosen parent cycle preserves every protected-a edge outside the protected pair, every remaining-b edge outside the enlarged selected set, and the selected-c restriction. Each conclusion is derived from the retained child states and their exact deleted opening edges.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateSuppliers.parent_from_state_suppliers`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateSuppliers.state_parent_retention`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualInductionState](NativeActualInductionState.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeSelectedCInvariant](NativeSelectedCInvariant.md)
