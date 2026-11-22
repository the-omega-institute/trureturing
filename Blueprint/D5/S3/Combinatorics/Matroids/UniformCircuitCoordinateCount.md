# Uniform Circuit Coordinate Count

## Abstract

Subsets avoiding two elements.

**Theorem 1.1 (Subsets avoiding two elements).**

Lean statement: `D5/S3/Combinatorics/Matroids/UniformCircuitCoordinateCount.card_avoid_both`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/UniformCircuitCoordinateCount.card_avoid_both` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the two designated elements are distinct, the number of size-r subsets that avoid both is the binomial coefficient choosing r from the ground size minus two.

**Theorem 1.2 (Subsets containing the second element).**

Lean statement: `D5/S3/Combinatorics/Matroids/UniformCircuitCoordinateCount.card_include_nonpivot`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/UniformCircuitCoordinateCount.card_include_nonpivot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two distinct designated elements, delete the second from a size-(r + 1) subset containing it and avoiding the first. Inserting it back gives the inverse. The number of such subsets is the binomial coefficient choosing r from the ground size minus two.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/UniformCircuitCoordinateCount.card_avoid_both`
- Truth anchor: `D5/S3/Combinatorics/Matroids/UniformCircuitCoordinateCount.card_include_nonpivot`
