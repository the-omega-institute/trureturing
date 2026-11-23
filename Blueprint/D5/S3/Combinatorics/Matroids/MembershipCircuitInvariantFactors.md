# Cyclic Factors from Petal Membership

## Abstract

The integral lifting obstruction for omitted bases separated by their membership classes.

**Theorem 1.1 (Independent replacement for separated petals).**

Lean statement: `D5/S3/Combinatorics/Matroids/MembershipCircuitInvariantFactors.membership_lifting_obstruction_invariant_factors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/MembershipCircuitInvariantFactors.membership_lifting_obstruction_invariant_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the ordered core have K elements and suppose 3 <= r < K. Its bases are all r-element sets outside a family of t omissions sharing a pivot. Partition the remaining indices by their membership in the petals. For each pair of petals, require a membership class of at least two indices lying in exactly one of the two petals. In a finite block-ordered parallel expansion, let n be the total size, g the gcd of all class sizes, and q(T) the gcd of n and the class sizes outside T. Both binom(K - 2, r - 2) and binom(K - 2, r - 1) are at least t. The integral joint lifting obstruction is the direct sum of binom(K - 2, r - 2) - t cyclic factors of order g, binom(K - 2, r - 1) - t of order n, and one factor of order q(T) per omission. Weight concentration within each membership class separates the omitted coefficients. Deletion and complement injections give the multiplicity bounds.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/MembershipCircuitInvariantFactors.membership_lifting_obstruction_invariant_factors`
- Dependency: [D5/S3/Combinatorics/Matroids/CommonPivotCircuitInvariantFactors](CommonPivotCircuitInvariantFactors.md)
- Dependency: [D5/S3/Combinatorics/Matroids/MembershipCircuitResidueProduct](MembershipCircuitResidueProduct.md)
- Dependency: [D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions](MembershipSeparatedOmissions.md)
- Dependency: [D5/S3/Combinatorics/Matroids/PuncturedCircuitInvariantFactors](PuncturedCircuitInvariantFactors.md)
- Dependency: [D5/S3/Combinatorics/Matroids/UniformCircuitInvariantFactors](UniformCircuitInvariantFactors.md)
- Dependency: [D5/S3/FiniteGroups/Modules/FiniteModuleProductCancellation](../../FiniteGroups/Modules/FiniteModuleProductCancellation.md)
