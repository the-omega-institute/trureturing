# Actual Path Families Retain the Same Cycle Inventory

## Abstract

An actual path family covering each vertex once earns the full support and retained-edge inventories of the same Hamilton cycle.

The graph and vertex type are arbitrary. The inputs are actual walks, unique vertex coverage and edge membership against one supplied Hamilton cycle. The proof derives the list permutations: it does not assume a target support permutation or select a different cycle. Nil paths retain their one vertex.

**Theorem 1.1 (Vertex Ownership Eliminates Repeated Edges).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualPathFamilyInventory.actual_path_partition_edges_nodup`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualPathFamilyInventory.actual_path_partition_edges_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the concatenation of actual piece supports has no repeated vertex, the concatenation of their edge lists has no repeated edge. A repeated edge would repeat one of its incident vertices either inside a path or across two different pieces. This live helper is used by the same-cycle family inventory and by supplier-edge restoration.

**Theorem 1.2 (Earn Full Support and Exactly the Uncut Edges).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualPathFamilyInventory.actual_path_family_cycle_inventory`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualPathFamilyInventory.actual_path_family_cycle_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite family of actual paths covering every graph vertex in exactly one member, the concatenated supports are a permutation of the supplied Hamilton cycle's support tail. If family edge membership is exactly membership in that cycle excluding a specified finite cut set, the concatenated edges are a permutation of the cycle edge list filtered by those cuts. Simplicity and unique vertex ownership eliminate repeated edges, so membership determines the exact retained-edge inventory.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualPathFamilyInventory.actual_path_family_cycle_inventory`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualPathFamilyInventory.actual_path_partition_edges_nodup`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/EdgeSlicing](EdgeSlicing.md)
