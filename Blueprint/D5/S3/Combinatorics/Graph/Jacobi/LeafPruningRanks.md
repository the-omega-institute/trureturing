# Chronological leaf deletion and component boundaries

## Abstract

Chronological leaf deletion and component boundaries

**Definition 1.1 (Chronological leaf-deletion ranks).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.LeafRanks`

*Formalization.* `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.LeafRanks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex scheduled before the cut has at most one adjacent vertex whose rank is no smaller. This generic graph condition is the live input extracted from the literal flag-counted deletion chronology.

**Theorem 1.2 (Deleted vertices induce a forest).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.deleted_acyclic`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.deleted_acyclic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A cycle would have a minimum-rank vertex with two distinct later neighbors. Therefore the graph induced by ranks below the cut is acyclic.

**Theorem 1.3 (Every actual cycle survives the cut).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.cycle_retained`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.cycle_retained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The minimum rank on a cycle cannot lie below the cut; every vertex of that cycle is retained. No cycle-existence hypothesis is inserted into the rank structure.

**Theorem 1.4 (Simple paths between retained vertices stay retained).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.retained_path`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.retained_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If such a path dipped below the cut, its minimum-rank internal vertex would have distinct predecessor and successor of no smaller rank, contradicting the actual one-later-neighbor condition.

**Theorem 1.5 (The nonempty retained core is connected).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.retained_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.retained_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a connected source and a nonempty retained vertex set, a source simple path between retained endpoints remains in the retained induced graph. This is consumed in the actual flag pruning extraction.

**Definition 1.6 (An actual boundary adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.ComponentBoundary`

*Formalization.* `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.ComponentBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A boundary records a deleted-component vertex, its component membership, a retained exterior vertex and their literal adjacency. It is not a postulated unique-root structure.

**Theorem 1.7 (A deleted component has at most one boundary adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.component_boundary_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.component_boundary_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A simple deleted path between two proposed boundary adjacencies forces its earliest vertex to have two later neighbors. Thus both interior and exterior endpoints agree.

**Theorem 1.8 (A deleted component of a connected source reaches the retained core).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.component_boundary_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.component_boundary_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the connected source has any retained vertex, a path from a deleted component to that vertex has a first cut-crossing edge. Its deleted endpoint remains in the original component, furnishing an actual boundary. Together with uniqueness this supplies the real root used by flag pruning.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.ComponentBoundary`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.LeafRanks`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.component_boundary_nonempty`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.component_boundary_unique`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.cycle_retained`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.deleted_acyclic`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.retained_connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.retained_path`
