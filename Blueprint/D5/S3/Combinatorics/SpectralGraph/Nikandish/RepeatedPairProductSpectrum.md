# The full finite-tail product criterion, including equality.

## Abstract

The full finite-tail product criterion, including equality.

The source is repeated-pair-product-tail at PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02, blob 66664013207b88567bf74f1a9a0c6eaf65d07f24. Every tail subset and every positive parameter is retained. Diagonal similarity, the complete energy identity, a nonempty proper support and the real finite spectral theorem give the actual minimum. The equality argument requires at least two tail coordinates and makes no claim for the three-prime equality block. General Q3 outside the sufficient condition remains open.

**Theorem 1.1 (A genuine smallest eigenvalue in (1,2)).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductSpectrum.product_minimum_window`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductSpectrum.product_minimum_window` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every finite nontrivial tail index, a>=1, all positive real tail weights, and a squared times the full tail product at least (a squared minus one) times the shifted tail product plus (a-1)(a-2), the complete operator has a nonzero eigenvector of eigenvalue strictly between one and two. This eigenvalue is no larger than the eigenvalue of every nonzero real eigenpair of the same full operator. Equality in the hypothesis is included.

**Theorem 1.2 (Actual ideal-graph nonintegrality for every number of primes at least four).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductSpectrum.actual_product_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductSpectrum.actual_product_tail` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For arbitrary distinct prime coordinates, positive natural repeated exponent and positive tail exponents over every finite nontrivial index, the exact source product condition gives an actual graph eigenvalue strictly between V-1 and V and proves nonintegrality. The vertex count is the natural cardinal expression, not a scalar surrogate or a redefined graph.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductSpectrum.actual_product_tail`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductSpectrum.product_minimum_window`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductTail](RepeatedPairProductTail.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairSupport](RepeatedPairSupport.md)
