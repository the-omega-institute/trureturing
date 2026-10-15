# The Complete Actual Induction State

## Abstract

An actual induction state retains one supplied cycle and all data later consumed by the native recursion.

**Definition 1.1 (One Cycle with Both Literal Boundary Orders).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualInductionState.StateFor`

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualInductionState.StateFor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a supplied frame, the state contains one actual Hamilton cycle in its marked domain, two disjoint cut groups with their exact native images, a joint partition and both restored partitions on that cycle. It records each distinguished endpoint as a literal port coordinate, the primary and opposite parity flags, and the retained protected-a, remaining-b and selected-c edge conditions. Its opposite frame is the canonical selected-order exchange. This structure specifies the data required by the recursion; existence is proved by the separate all-order construction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualInductionState.StateFor`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders](NativeOppositeSelectedOrders.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeProtectedLabels](NativeProtectedLabels.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeSimultaneousBoundaryState](NativeSimultaneousBoundaryState.md)
