# Earn Two-Cut Q Slicing from Literal Even and Odd Routes

## Abstract

Earn Two-Cut Q Slicing from Literal Even and Odd Routes.

**Theorem 1.1 (Use the Exact Even Native Piece Position).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualQBoundarySlicing.native_actual_q_even_three_fragments`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualQBoundarySlicing.native_actual_q_even_three_fragments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The supplied actual ordered even boundary pieces and their exact route endpoints place the zero left port at index s+1, after the first rooted joint piece. Together with the same cycle joint inventory and retained-edge invariants, this earns three paths that exhaust the supplied Hamilton Q route and preserve its literal support and edge split.

**Theorem 1.2 (Use the Exact Odd Native Piece Position).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualQBoundarySlicing.native_actual_q_odd_three_fragments`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualQBoundarySlicing.native_actual_q_odd_three_fragments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The supplied actual ordered odd boundary pieces put the zero left port at index s+1, including the empty-ladder order-three case. Exact endpoints, the same cycle inventories and its retained-edge invariants earn the three-fragment split of that supplied Hamilton Q route.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualQBoundarySlicing.native_actual_q_even_three_fragments`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualQBoundarySlicing.native_actual_q_odd_three_fragments`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualQRouteSlicing](NativeActualQRouteSlicing.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ActualRouteCutOrder](../Walks/ActualRouteCutOrder.md)
