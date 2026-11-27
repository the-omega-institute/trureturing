# Uniform Circuit Invariant Factors

## Abstract

The invariant factors for a uniform core.

**Theorem 1.1 (The invariant factors for a uniform core).**

Lean statement: `D5/S3/Combinatorics/Matroids/UniformCircuitInvariantFactors.uniform_lifting_obstruction_invariant_factors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/UniformCircuitInvariantFactors.uniform_lifting_obstruction_invariant_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a loopless uniform core have rank r + 2 on k + 2 ordered elements with r at most k. Expand each element to a nonempty class, with the order respecting the classes. The joint lifting quotient is a product of k choose r cyclic groups of order the gcd of the class sizes and k choose (r + 1) cyclic groups of order the total ground size. The alternating form reduction gives a pivot, then separates the coordinates according to whether their subset contains the direction of the remaining weight vector.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/UniformCircuitInvariantFactors.uniform_lifting_obstruction_invariant_factors`
- Dependency: [D5/S3/Combinatorics/Matroids/UniformCircuitBasis](UniformCircuitBasis.md)
- Dependency: [D5/S3/Combinatorics/Matroids/UniformCircuitCoordinateCount](UniformCircuitCoordinateCount.md)
- Dependency: [D5/S3/Combinatorics/Matroids/UniformCircuitResidueDiagonal](UniformCircuitResidueDiagonal.md)
- Dependency: [D5/S3/Combinatorics/Matroids/UniformMatroidCircuitCoordinates](UniformMatroidCircuitCoordinates.md)
