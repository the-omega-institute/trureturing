# Positive energy on the complete tail powerset

## Abstract

The strict lower endpoint for every finite repeated-pair support operator.

The source is the repeated-pair-product-tail note at PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02, blob 66664013207b88567bf74f1a9a0c6eaf65d07f24. This representation proves the arbitrary-index lower endpoint using the complete weighted signless energy. The empty-support loop and its edge to every tail support make the energy strictly positive; no fixed-size tensor or sampled support replaces the full domain. The upper product criterion and its equality case remain separate obligations.

**Theorem 1.1 (Strict weighted energy).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductTail.lower_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductTail.lower_energy` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every finite tail index set, positive real repeated exponent a, positive real tail weights, and nonzero function h on every subset, the weighted quadratic form of K-I is positive. The proof is a full sum-of-squares identity plus the nonnegative diagonal remainder. Empty tail index sets are included.

**Theorem 1.2 (The general lower endpoint).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductTail.eigenvalue_gt_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductTail.eigenvalue_gt_one` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every nonzero real eigenvector of the full K at positive real parameters, its eigenvalue is strictly greater than one. No upper criterion, integer assumption, fixed number of primes, or spectrum-integrality premise is used.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductTail.eigenvalue_gt_one`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductTail.lower_energy`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairSupport](RepeatedPairSupport.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions](../PairedIdealIntersectionObstructions.md)
