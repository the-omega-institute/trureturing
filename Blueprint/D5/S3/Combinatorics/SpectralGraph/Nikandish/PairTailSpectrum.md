# Strict full-operator windows and necessary actual-graph tail equations.

## Abstract

Strict full-operator windows and necessary actual-graph tail equations.

Sources: the complete large-tail, quadratic-tail-reduction, harmonic-tail and unique-tail notes at supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The actual weighted four-cell tensor and ideal-graph lift are used throughout. Complete original attribution, antecedents, finite controls, failed-method and reproduction boundaries remain unchanged. Necessary root conditions are not sufficient integrality conditions. General single-pair, fully unequal and higher-prime Q3 remain open, and academic approval/publication remains separate.

**Theorem 1.1 (The strict bounded root window).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSpectrum.bounded_eigenpair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSpectrum.bounded_eigenpair` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every positive real a,b and c>=1 there is a nonzero full tensor eigenpair strictly between a+1 and (a+1)(b+1). The separate PairTailOrdering owner proves the ordered second-smallest window from the complete spectrum.

**Theorem 1.2 (The full harmonic eigenpair window).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSpectrum.harmonic_eigenpair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSpectrum.harmonic_eigenpair` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every positive real a and c>b>=1 the same full operator has an eigenpair between a+b+1 and a+1+2bc/(b+c), strictly below a+2b+1. This theorem states a genuine eigenpair; PairTailOrdering separately supplies the full source second-smallest indexing result.

**Theorem 1.3 (All actual integral graphs force a positive quadratic root).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSpectrum.actual_tail_candidate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSpectrum.actual_tail_candidate` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

All positive natural a,b,c and arbitrary distinct prime coordinates retain an integer offset 0<t<(a+1)b, the complete determinant equation and c dividing its positive constant. Passing these tests never proves graph integrality.

**Theorem 1.4 (The complete unequal-tail candidate window).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSpectrum.actual_harmonic_candidate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSpectrum.actual_harmonic_candidate` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For all positive a,b,c with b<c, actual integrality forces b<t<2b and a negative leading coefficient. There is no ordering between a and b.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSpectrum.actual_harmonic_candidate`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSpectrum.actual_tail_candidate`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSpectrum.bounded_eigenpair`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSpectrum.harmonic_eigenpair`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/Nikandish/PairGapSigns](PairGapSigns.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailArithmetic](PairTailArithmetic.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift](../PairedIdealIntersectionLift.md)
