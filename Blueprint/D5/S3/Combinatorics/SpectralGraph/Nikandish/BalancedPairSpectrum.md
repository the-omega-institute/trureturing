# Balanced intervals and the separate general upper-four bound.

## Abstract

Balanced intervals and the separate general upper-four bound.

Source: four-prime-single-pair-balanced, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The original parameter domains, attribution and failed-method limitations are retained. General four-prime and higher-prime Q3 remain open outside the stated families. Original academic approval and publication boundaries are unchanged.

**Theorem 1.1 (The general repeated-minimum upper-four bound).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairSpectrum.repeated_minimum_low`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairSpectrum.repeated_minimum_low` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every real a>=5 and b,c>=a, with no ordering between tails, the empty/full principal minor produces an eigenpair in (1,4). This bound alone proves no nonintegrality in that larger region.

**Theorem 1.2 (The full real balanced interval).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairSpectrum.balanced_eigenpair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairSpectrum.balanced_eigenpair` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Every a<=b<=c<=2a-6 has a genuine full tensor eigenpair in (3,4); the hypotheses imply a>=6.

**Theorem 1.3 (Actual graph interval including both tail boundaries).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairSpectrum.actual_balanced_interval`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairSpectrum.actual_balanced_interval` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

All natural balanced parameters and arbitrary distinct primes have an actual ideal-graph eigenvalue in (V-3,V-2).

**Theorem 1.4 (Whole balanced family nonintegrality).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairSpectrum.actual_nonintegral`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairSpectrum.actual_nonintegral` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The strict unit interval proves nonintegrality throughout the original domain, with no finite exponent base. The neighboring offset-five interval is not asserted.

**Theorem 1.5 (The genuine smallest full-operator interval).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairSpectrum.minimum_window`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairSpectrum.minimum_window` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The exact minimum compares against every nonzero real eigenpair of the full weighted tensor and lies in (3,4) on the entire real balanced domain.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairSpectrum.actual_balanced_interval`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairSpectrum.actual_nonintegral`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairSpectrum.balanced_eigenpair`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairSpectrum.minimum_window`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairSpectrum.repeated_minimum_low`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairDeterminant](BalancedPairDeterminant.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/Nikandish/PairedTensorMinimum](PairedTensorMinimum.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift](../PairedIdealIntersectionLift.md)
