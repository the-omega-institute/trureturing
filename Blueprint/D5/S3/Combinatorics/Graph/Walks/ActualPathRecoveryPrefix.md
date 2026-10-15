# Recovering Actual Path Prefixes from Retained Inventories

## Abstract

Actual vertex ownership and retained edges recover literal prefixes inside supplied simple boundary paths.

The vertex type and simple graph are arbitrary. All paths and cycle inventories refer to the literal supplied walks. These statements provide actual graph-surgery steps; an all-order recursive Hamilton construction is a separate consumer.

**Theorem 1.1 (Recover the Rooted Piece Edges).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix.actual_partition_rooted_walk_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix.actual_partition_rooted_walk_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a family whose full support contains no repeated vertex, every edge of a supplied walk starting in one family piece belongs to that piece whenever it belongs to the global family edge inventory. Induction keeps each visited vertex with its unique actual owner.

**Theorem 1.2 (Retained Edges Force a Literal Prefix).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix.actual_rooted_path_is_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix.actual_rooted_path_is_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A supplied walk and a supplied simple path start at the same vertex. If the first walk has no repeated support and all of its edges occur in the simple path, it is the literal initial segment of that path. The remainder is an actual simple walk with the correct endpoints.

**Theorem 1.3 (Recover a Joint Prefix after Restoration).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix.actual_restored_partition_joint_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix.actual_restored_partition_joint_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual joint and restored single-order families have duplicate-free full supports. Edges of a supplied joint walk retained by the restored family belong to its actual boundary piece, and give a literal prefix there. This conclusion uses actual edge membership rather than an assumed route factorization.

**Theorem 1.4 (Recover the Distinguished Initial Joint Path).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix.actual_restored_initial_joint_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix.actual_restored_initial_joint_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact joint and single-order inventories of a supplied source walk show that the distinguished actual joint path begins its actual restored boundary. Every edge remains in that boundary, and the returned tail is simple.

**Theorem 1.5 (Recover the Restored Crossing Prefix).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix.actual_restored_bridge_route_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix.actual_restored_bridge_route_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual marked seam in the old restored cut group joins the reverse crossing path to the distinguished joint path. Cycle simplicity and the exact retained inventories earn the joined support simplicity, its membership in the actual boundary and the literal remaining tail.

**Theorem 1.6 (Locate a Cut in the Recovered Prefix).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix.actual_restored_joint_cut_position`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix.actual_restored_joint_cut_position` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A cut at a supplied index of an actual joint path has a corresponding directed index in the actual restored boundary. The previous retained-inventory prefix theorem earns that position instead of requiring it as an input.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix.actual_partition_rooted_walk_edges`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix.actual_restored_bridge_route_prefix`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix.actual_restored_initial_joint_prefix`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix.actual_restored_joint_cut_position`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix.actual_restored_partition_joint_prefix`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix.actual_rooted_path_is_prefix`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix](ActualPiecePrefix.md)
