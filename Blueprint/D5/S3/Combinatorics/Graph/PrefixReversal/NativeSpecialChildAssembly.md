# Actual Paths on the Complete Native Special Child

## Abstract

Actual Paths on the Complete Native Special Child.

**Theorem 1.1 (Assemble a Hamilton Path from Literal Pieces).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSpecialChildAssembly.native_special_child_assembled`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSpecialChildAssembly.native_special_child_assembled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A supplied Hamilton cycle on the independently defined native special child is sliced at its actual special cuts. If every slice endpoint pair satisfies a relation identified exactly once by a supplied port route, and that route has the native internal seams, the same slices join into a Hamilton path between the first and last supplied route ports. Exact support and retained-edge inventories come from the cycle; the route and endpoint law remain hypotheses.

**Theorem 1.2 (Earn the Assembly Inputs from One Actual Cycle).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSpecialChildAssembly.native_special_child_from_actual_partition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSpecialChildAssembly.native_special_child_from_actual_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given a Hamilton cycle on the native special child, its complete actual partition at the special cuts, and an alternating port route that identifies the endpoints of those actual pieces, the partition is reordered and joined into one Hamilton path. Coverage and edge inventories come from the supplied cycle and its literal partition; the result does not assume an all-size recursive state.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSpecialChildAssembly.native_special_child_assembled`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSpecialChildAssembly.native_special_child_from_actual_partition`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains](NativeRecursiveExpansionDomains.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeStarGrafting](NativeStarGrafting.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/RecursivePortBoundary](RecursivePortBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering](../Walks/ActualCyclePieceReordering.md)
