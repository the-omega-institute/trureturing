# Punctured Circuit Invariant Factors

## Abstract

The cyclic factors with one omitted uniform basis.

**Theorem 1.1 (The cyclic factors after one basis is omitted).**

Lean statement: `D5/S3/Combinatorics/Matroids/PuncturedCircuitInvariantFactors.punctured_lifting_obstruction_invariant_factors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/PuncturedCircuitInvariantFactors.punctured_lifting_obstruction_invariant_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the ordered core on k elements have rank r with 2 at most r and r strictly less than k. Its bases are all r-subsets except one H. In a parallel expansion whose order respects the classes, put n equal to the total size and g equal to the gcd of all class sizes. The joint lifting quotient has binomial(k-2,r-2) minus one factors of order g, binomial(k-2,r-1) minus one factors of order n, and one factor of order the gcd of n and the sizes outside H.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/PuncturedCircuitInvariantFactors.punctured_lifting_obstruction_invariant_factors`
- Dependency: [D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinates](PuncturedCircuitCoordinates.md)
- Dependency: [D5/S3/Combinatorics/Matroids/PuncturedCircuitSplit](PuncturedCircuitSplit.md)
- Dependency: [D5/S3/Combinatorics/Matroids/PuncturedCircuitWeightBasis](PuncturedCircuitWeightBasis.md)
