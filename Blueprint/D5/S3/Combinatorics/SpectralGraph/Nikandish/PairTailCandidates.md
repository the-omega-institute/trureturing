# Complete finite candidate sets and uniform effective bounds.

## Abstract

Complete finite candidate sets and uniform effective bounds.

Sources: the complete large-tail, quadratic-tail-reduction, harmonic-tail and unique-tail notes at supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The actual weighted four-cell tensor and ideal-graph lift are used throughout. Complete original attribution, antecedents, finite controls, failed-method and reproduction boundaries remain unchanged. Necessary root conditions are not sufficient integrality conditions. General single-pair, fully unequal and higher-prime Q3 remain open, and academic approval/publication remains separate.

**Theorem 1.1 (The complete fixed-pair candidate count).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates.candidate_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates.candidate_card` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

All roots at all d-1 offsets are retained in the finite set. The cardinal is at most 2(d-1); no convenient finite sample replaces the candidate domain.

**Theorem 1.2 (The full sharpened b-1 candidate count).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates.harmonic_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates.harmonic_card` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Positive-root uniqueness at every harmonic offset reduces the complete set to at most b-1 candidates. The empty b=1 case remains included.

**Theorem 1.3 (Every actual integral tail belongs to the complete set).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates.actual_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates.actual_mem` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Every positive free tail with actual graph integral spectrum lies in the full fixed-pair candidate set, uniformly over arbitrary distinct prime coordinates.

**Theorem 1.4 (All unequal integral tails belong to the smaller set).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates.actual_harmonic_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates.actual_harmonic_mem` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For b<c the complete harmonic set is necessary for actual integrality. This is no classification in variable a,b.

**Theorem 1.5 (The full floor-square cutoff).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates.actual_le_cutoff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates.actual_le_cutoff` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The entire actual integral domain obeys c<=U[U+a(d-1)+a squared b], with d=(a+1)b and U=floor(d squared/4). Larger tails are excluded without scanning them.

**Theorem 1.6 (The full sharpened harmonic cutoff).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates.actual_le_harmonic`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates.actual_le_harmonic` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For a>=3 and b<c the exact maximum of the source constant at T=2b-1 gives the smaller effective upper bound. Equality in the offset estimate is retained.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates.actual_harmonic_mem`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates.actual_le_cutoff`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates.actual_le_harmonic`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates.actual_mem`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates.candidate_card`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates.harmonic_card`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSpectrum](PairTailSpectrum.md)
