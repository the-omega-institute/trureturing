# Two-axis eight-star geometry

## Abstract

Two-axis eight-star geometry

**Theorem 1.1 (Twelve edges in the second direction).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwoStarAxisBound.directionEdges_ge_twelve_of_two_stars`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwoStarAxisBound.directionEdges_ge_twelve_of_two_stars` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A full eight-star on one axis supplies four edges along each transverse axis. If one of these were a spoke of another star, commuting flips would force a selected center or a forbidden same-part corner in the first star. These four edges and the eight spokes are disjoint.

**Theorem 1.2 (Component order at least seventy-two).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwoStarAxisBound.card_ge_seventy_two_of_two_stars`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwoStarAxisBound.card_ge_seventy_two_of_two_stars` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Huang balance and cubicity give equal direction counts. The two-axis geometric bound therefore gives a lower bound of 72 vertices in an actual component for Hong–Wu–Xia Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwoStarAxisBound.card_ge_seventy_two_of_two_stars`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwoStarAxisBound.directionEdges_ge_twelve_of_two_stars`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OccupiedFibreParity](Q9OccupiedFibreParity.md)
