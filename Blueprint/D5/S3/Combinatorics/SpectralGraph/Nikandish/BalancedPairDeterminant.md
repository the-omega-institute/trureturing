# Complete balanced-region spectral determinant positivity.

## Abstract

Complete balanced-region spectral determinant positivity.

Source: four-prime-single-pair-balanced, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The original parameter domains, attribution and failed-method limitations are retained. Formal proofs are task-local integrations of the full source results. General four-prime and higher-prime Q3 remain open outside the stated families. Original academic approval and publication boundaries are unchanged.

**Theorem 1.1 (Every real spectral value at or below three is excluded).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairDeterminant.shifted_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairDeterminant.shifted_positive` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Over the complete domain a<=b<=c<=2a-6, the determinant at every x<=3 is strictly positive. The nonnegative variables b-a, c-b and 2a-c-6 retain all boundaries. All symbolic coefficients are checked by Lean ring reduction.

**Theorem 1.2 (Every actual weighted-tensor eigenpair is above three).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairDeterminant.eigenvalue_gt_three`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairDeterminant.eigenvalue_gt_three` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The determinant identity applies to every nonzero real tensor eigenvector; it is not a finite set of sample eigenvalues.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairDeterminant.eigenvalue_gt_three`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairDeterminant.shifted_positive`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionDeterminants](../PairedIdealIntersectionDeterminants.md)
