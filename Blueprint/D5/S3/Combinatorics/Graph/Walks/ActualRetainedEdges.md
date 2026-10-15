# Actual Route Inventories

## Abstract

Closing an actual piece chain preserves every retained child edge.

**Theorem 1.1 (Keep Every Piece Edge in the Chain).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualRetainedEdges.actual_chain_keeps_piece_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualRetainedEdges.actual_chain_keeps_piece_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every edge of any supplied piece remains in the literal chained edge list. The argument includes all intermediate pieces and makes no disjointness or Hamiltonian assumption.

**Theorem 1.2 (Keep Every Piece Edge After Closure).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualRetainedEdges.actual_closed_route_keeps_piece_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualRetainedEdges.actual_closed_route_keeps_piece_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The supplied cycle has the literal reversed chain-edge inventory with its closing seam. Every edge of every constituent piece therefore belongs to that same cycle. This is the inventory lemma used by native recursive retention proofs; it supplies no independent cycle existence statement.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualRetainedEdges.actual_chain_keeps_piece_edges`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualRetainedEdges.actual_closed_route_keeps_piece_edges`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/PathRingSplicing](PathRingSplicing.md)
