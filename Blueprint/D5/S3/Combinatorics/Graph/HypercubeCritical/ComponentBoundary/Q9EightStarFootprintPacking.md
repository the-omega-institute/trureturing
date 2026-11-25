# Packing eight-stars across coordinate axes

## Abstract

Packing eight-stars across coordinate axes

**Theorem 1.1 (Disjoint thirty-two-vertex footprints).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarFootprintPacking.starFootprint_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarFootprintPacking.starFootprint_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A star uses sixteen lifted spokes and sixteen cross-corner vertices. A center of another axis cannot approach within three transverse flips. Consequently the second spoke set avoids the first footprint. A shared cross corner would have four selected neighbors, violating cubicity.

**Theorem 1.2 (Counting distinct star directions).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarFootprintPacking.thirty_two_mul_card_le_of_eight_stars`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarFootprintPacking.thirty_two_mul_card_le_of_eight_stars` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing pairwise disjoint footprints gives 32 vertices per distinct star direction. In a component of order at most 126, at most three axes can have full eight-stars. Nine star directions are impossible in any cubic subset of a hypothetical 258-set.

**Theorem 1.3 (Both transverse parity classes contain pairs).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarFootprintPacking.doubleFibres_ge_two_of_eightStar`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarFootprintPacking.doubleFibres_ge_two_of_eightStar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four cross edges in each other direction split two per axial layer. This forces at least two pairs of each projected parity, linking local cube geometry with the arithmetic of weighted boundary supports. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarFootprintPacking.doubleFibres_ge_two_of_eightStar`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarFootprintPacking.starFootprint_disjoint`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarFootprintPacking.thirty_two_mul_card_le_of_eight_stars`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwoStarAxisBound](Q9TwoStarAxisBound.md)
