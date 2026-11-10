# Ordered second-smallest eigenvalue of the entire paired tensor

## Abstract

Ordered second-smallest eigenvalue of the entire paired tensor

Sources: the complete four-prime large-tail, harmonic-tail and unique-tail manuscripts at supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. All original positive natural parameters are retained, with no ordering between a and b. The sorted spectrum contains all four eigenvalues with multiplicity; the full characteristic polynomial and nonzero tensor eigenpairs identify the actual operator. Original attribution, prerequisites, reports, uncertainties and failed-method boundaries remain unchanged. Necessary tail tests do not assert integrality. General Q3, a6 certification and enumeration reproduction limits stay open. The linked issue #28398 audit remains unfinished; academic approval and publication are separate.

**Theorem 1.1 (The complete decreasing spectrum).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairTailOrdering.values_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairTailOrdering.values_antitone` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The second-smallest value has index two in this four-element decreasing spectrum, with multiplicity.

**Theorem 1.2 (The entire characteristic polynomial).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairTailOrdering.polynomial`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairTailOrdering.polynomial` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

All four sorted values factor the characteristic polynomial of the full weighted tensor, with no scalar proxy.

**Theorem 1.3 (Nonzero full-operator eigenvectors).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairTailOrdering.eigenpair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairTailOrdering.eigenpair` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Every sorted value is realized by a nonzero vector of the entire paired tensor.

**Theorem 1.4 (The ordered strict bounded-tail window).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairTailOrdering.bounded_window`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairTailOrdering.bounded_window` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every a>0,b>0,c>=1 the second-smallest eigenvalue lies strictly between a+1 and (a+1)(b+1).

**Theorem 1.5 (The ordered strict harmonic-tail window).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairTailOrdering.harmonic_window`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairTailOrdering.harmonic_window` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For all a>=1,b>=1,c>b, including the complete original positive natural domain, the second-smallest value lies strictly between a+b+1 and a+1+2bc/(b+c), below a+2b+1.

**Theorem 1.6 (Actual graph application for all distinct prime assignments).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairTailOrdering.actual_ordered_value`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairTailOrdering.actual_ordered_value` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every positive natural a,b,c and every injective prime assignment, the ordered tensor value lifts to the stated actual ideal-intersection graph Laplacian eigenvalue.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairTailOrdering.actual_ordered_value`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairTailOrdering.bounded_window`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairTailOrdering.eigenpair`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairTailOrdering.harmonic_window`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairTailOrdering.polynomial`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairTailOrdering.values_antitone`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/PairTailSpectrum](PairTailSpectrum.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/RepeatedPairBinaryPolynomial](RepeatedPairBinaryPolynomial.md)
