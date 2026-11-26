# Uniform Circuit Basis

## Abstract

The gcd coordinate for a positive weight vector.

**Theorem 1.1 (The gcd coordinate for a positive weight vector).**

Lean statement: `D5/S3/Combinatorics/Matroids/UniformCircuitBasis.weight_vector_in_basis`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/UniformCircuitBasis.weight_vector_in_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a nonempty finite index set, a positive weight vector is its gcd times a vector in an integral basis. Dualize the unimodular change of coordinates that reduces the weighted scalar sum to a single coordinate.

**Theorem 1.2 (A basis adapted to both operations).**

Lean statement: `D5/S3/Combinatorics/Matroids/UniformCircuitBasis.exists_adapted_weight_basis`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/UniformCircuitBasis.exists_adapted_weight_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive integer weight vector on k + 2 coordinates, there is an integral basis whose first vector sums to one and in which the weight vector is the total weight times that first vector plus the gcd of the remaining original weights times the second vector.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/UniformCircuitBasis.exists_adapted_weight_basis`
- Truth anchor: `D5/S3/Combinatorics/Matroids/UniformCircuitBasis.weight_vector_in_basis`
- Dependency: [D5/S3/Combinatorics/Matroids/RankTwoCircuitInvariantFactors](RankTwoCircuitInvariantFactors.md)
