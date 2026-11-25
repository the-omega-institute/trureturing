# Cyclic Factors at a Common Pivot

## Abstract

The integral joint lifting obstruction for common-pivot sparse-paving omissions.

**Theorem 1.1 (Cyclic factors with only the intersection bound).**

Lean statement: `D5/S3/Combinatorics/Matroids/CommonPivotCircuitInvariantFactors.common_pivot_lifting_obstruction_invariant_factors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/CommonPivotCircuitInvariantFactors.common_pivot_lifting_obstruction_invariant_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let 3 <= r < K for a finite ordered ground set of size K. The core bases are all r-element subsets except t omitted sets. All omissions contain a common element, and distinct omissions intersect in at most r minus two elements. In a finite block-ordered parallel expansion write n for the total size, g for the gcd of the class sizes, and q(T) for the gcd of n and the class sizes outside T. The lifting obstruction is integrally linearly equivalent to the product of binom(K minus 2, r minus 2) minus t factors of order g, binom(K minus 2, r minus 1) minus t factors of order n, and one factor of order q(T) per omission. The two binomial coefficients are at least t. The primary exchange and the existing finite cancellation argument prove the decomposition.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/CommonPivotCircuitInvariantFactors.common_pivot_lifting_obstruction_invariant_factors`
- Dependency: [D5/S3/Combinatorics/Matroids/CommonPivotCircuitResidueProduct](CommonPivotCircuitResidueProduct.md)
- Dependency: [D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions](MembershipSeparatedOmissions.md)
- Dependency: [D5/S3/Combinatorics/Matroids/PuncturedCircuitInvariantFactors](PuncturedCircuitInvariantFactors.md)
- Dependency: [D5/S3/Combinatorics/Matroids/UniformCircuitInvariantFactors](UniformCircuitInvariantFactors.md)
- Dependency: [D5/S3/FiniteGroups/Modules/FiniteModuleProductCancellation](../../FiniteGroups/Modules/FiniteModuleProductCancellation.md)
