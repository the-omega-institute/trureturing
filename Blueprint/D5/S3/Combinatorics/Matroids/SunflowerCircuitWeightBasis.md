# Weight Coordinates for Disjoint Petals

## Abstract

A pivot and a disjoint family of coordinate sets admit a shared weight basis.

**Theorem 1.1 (Weight Coordinates for Disjoint Petals).**

Lean statement: `D5/S3/Combinatorics/Matroids/SunflowerCircuitWeightBasis.exists_sunflower_weight_basis`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SunflowerCircuitWeightBasis.exists_sunflower_weight_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a finite coordinate set with positive integer weights and pairwise disjoint petals, each of size at least two and each avoiding the pivot. Partition the indices by petal membership and by equality to the pivot. An integral change of basis concentrates the weights on one index per block. The change and its inverse preserve each petal, and the inverse change sends the pivot vector to a coordinate vector supported at the pivot. Each petal meets the zero-weight set away from the pivot, so the intersections for distinct petals differ.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SunflowerCircuitWeightBasis.exists_sunflower_weight_basis`
- Dependency: [D5/S3/Combinatorics/Matroids/CircuitWeightBlocks](CircuitWeightBlocks.md)
