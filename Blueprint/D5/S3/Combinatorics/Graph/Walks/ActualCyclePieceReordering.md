# Reordering and Joining Actual Cycle Pieces

## Abstract

A supplied actual partition can be oriented along a route and joined while retaining exact support and edge inventories.

The vertex type and simple graph are arbitrary. All paths and cycle inventories refer to the literal supplied walks. These statements provide actual graph-surgery steps; an all-order recursive Hamilton construction is a separate consumer.

**Theorem 1.1 (Earn the Number of Pieces).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering.actual_cycle_partition_inventory`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering.actual_cycle_partition_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact full-support and filtered-edge permutations of one supplied Hamilton cycle give unique vertex coverage, the retained-edge membership and a number of pieces equal to the actual cut cardinality. Nil pieces are counted through their one support vertex.

**Theorem 1.2 (Reorder the Supplied Actual Pieces).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering.actual_partition_pieces_reordered`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering.actual_partition_pieces_reordered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every supplied piece matches a whole route edge. Unique vertex ownership makes the assignment injective, and equal finite cardinality makes it a permutation. Each selected piece is copied or reversed to the directed route endpoints; coverage and retained edges are preserved.

**Theorem 1.3 (Reorder the Actual Slices of a Cycle).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering.actual_cycle_slices_reordered`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering.actual_cycle_slices_reordered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the supplied-piece reordering to the actual slicing chosen from one Hamilton cycle and its nonempty set of actual cuts. The endpoint matching premise concerns that same chosen family.

**Theorem 1.4 (Join Supplied Pieces into a Hamilton Path).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering.actual_partition_pieces_joined`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering.actual_partition_pieces_joined` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual adjacency between consecutive route endpoints joins the reordered supplied pieces into an actual Hamilton path. Its support is literally the concatenation of their full supports, and its edges are literally the actual chain inventory.

**Theorem 1.5 (Join the Actual Cycle Slices).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering.actual_cycle_slices_joined`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering.actual_cycle_slices_joined` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The corresponding cycle-slicing wrapper selects its slicing once, reorders that family and joins it with the supplied real connectors. It returns the same support and retained-edge readouts.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering.actual_cycle_partition_inventory`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering.actual_cycle_slices_joined`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering.actual_cycle_slices_reordered`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering.actual_partition_pieces_joined`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering.actual_partition_pieces_reordered`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/EdgeSlicing](EdgeSlicing.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/PathRingSplicing](PathRingSplicing.md)
