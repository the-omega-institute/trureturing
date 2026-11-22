# Cyclic Factors with Two Omitted Uniform Bases

## Abstract

The joint lifting obstruction for a core with two separated omissions.

**Theorem 1.1 (The two separate cyclic factors).**

Lean statement: `D5/S3/Combinatorics/Matroids/TwoOmittedCircuitInvariantFactors.two_omitted_lifting_obstruction_invariant_factors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/TwoOmittedCircuitInvariantFactors.two_omitted_lifting_obstruction_invariant_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a uniform core of rank at least three. Omit two bases whose intersection has cardinality at most the rank minus two. Their union then forces corank at least two. In a block-ordered parallel expansion, write n for the total size and g for the gcd of the class sizes. Starting from the uniform decomposition, decrease the multiplicities of the factors of orders g and n by two each. For each omitted basis, add a cyclic factor whose order is the gcd of n and the class sizes outside that basis. The two exceptions may have incomparable orders. The residue product identity and cancellation of the uniform factors give the stated decomposition.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/TwoOmittedCircuitInvariantFactors.two_omitted_lifting_obstruction_invariant_factors`
- Dependency: [D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching](AliabadiZerbibMatroidMatching.md)
- Dependency: [D5/S3/Combinatorics/Matroids/PuncturedCircuitInvariantFactors](PuncturedCircuitInvariantFactors.md)
- Dependency: [D5/S3/Combinatorics/Matroids/SparsePavingCircuitProduct](SparsePavingCircuitProduct.md)
- Dependency: [D5/S3/Combinatorics/Matroids/UniformCircuitInvariantFactors](UniformCircuitInvariantFactors.md)
- Dependency: [D5/S3/FiniteGroups/Modules/FiniteModuleProductCancellation](../../FiniteGroups/Modules/FiniteModuleProductCancellation.md)
