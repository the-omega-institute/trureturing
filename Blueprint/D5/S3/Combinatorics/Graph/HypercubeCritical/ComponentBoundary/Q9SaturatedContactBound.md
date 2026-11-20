# Saturated pairs force many distance-two contacts

## Abstract

Saturated pairs force many distance-two contacts

**Theorem 1.1 (Saturated pairs force many distance-two contacts).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SaturatedContactBound.distanceTwoPairs_card_ge_322`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SaturatedContactBound.distanceTwoPairs_card_ge_322` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose a 258-vertex candidate consists of two separated balanced cubic components of orders 72 and 186. If the 72-vertex component has at least 142 exterior neighbors, the two components have at least 322 ordered cross pairs at Hamming distance two.

Partition the exterior points by their neighbor counts in the larger component. A vertex with eight selected neighbors has a unique exterior mate. High-high mates form eightfold edges, and the other mates satisfy the signed direction bound.

The resulting incidence budget forces enough neighbors of the larger component in the common boundary. Every such incidence is counted by the cross-distance-two pairs because each common neighbor has a positive even count on the smaller side.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SaturatedContactBound.distanceTwoPairs_card_ge_322`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CommonBoundaryObstruction](Q9CommonBoundaryObstruction.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverPacking](Q9EightfoldCoverPacking.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9HighLeafPacking](Q9HighLeafPacking.md)
