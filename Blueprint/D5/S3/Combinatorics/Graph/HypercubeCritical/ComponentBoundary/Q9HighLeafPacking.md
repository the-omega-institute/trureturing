# Signed direction sets control high-degree exterior neighbors

## Abstract

Signed direction sets control high-degree exterior neighbors

**Theorem 1.1 (Signed direction sets control high-degree exterior neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9HighLeafPacking.card_highLeafDirections_le_by_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9HighLeafPacking.card_highLeafDirections_le_by_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider an exterior mate of vertices which each have eight neighbors in a balanced cubic support. The four positive directions of one such vertex intersect those of another in at most one direction. This follows from the sign around each selected triple.

Four of these direction sets would occupy at least ten coordinates. Three sets exhaust the nine coordinates and leave no direction with a uniform sign. At most two sets can coexist when the mate has selected neighbors, and a mate with four or more selected neighbors permits at most one.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9HighLeafPacking.card_highLeafDirections_le_by_degree`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverLocal](Q9EightfoldCoverLocal.md)
