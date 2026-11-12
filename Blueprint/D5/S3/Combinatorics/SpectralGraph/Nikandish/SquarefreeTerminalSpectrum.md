# SquarefreeTerminalSpectrum

## Abstract

Full squarefree alternating spectral construction

Source: PR3 b93becea662a746badeadba42fdc3d3eb3db9382, paper/sections/squarefree.tex, blob2cd18d52cd3f4581d624bb94006480340756a5c3. Original Nikandish graph/problem attribution and manuscript Ma/Nikandish/Zhang credit, prerequisites, reports, failed methods and rights boundaries are preserved. All alternating pairs and all tail supports are retained; nonzero vectors lift to the genuine ideal-intersection graph for arbitrary injective prime assignments. This is the full spectral construction, separately from the already-delivered stronger unit-entry nonintegrality theorem. General Q3, exact n7/paused exclusions, a6 certification and finite-enumeration reproducibility limits are unchanged. Unfinished escape audits are disclosed at issue28398; disclosure is not proof, audit completion or a waiver of other gates.

**Theorem 1.1 (Both irrational odd-count eigenvalues).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/SquarefreeTerminalSpectrum.odd_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/SquarefreeTerminalSpectrum.odd_spectrum` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every odd prime count at least3, the two signs give both original explicit irrational eigenvalues. The proof supplies the full two-dimensional residual eigenvector, proves irrationality by strict consecutive-square brackets and transports it to the actual graph. The nested finite index is the complete odd coordinate set, not a restricted family of prime values.

**Theorem 1.2 (Entire even residual spectral window).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/SquarefreeTerminalSpectrum.even_window`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/SquarefreeTerminalSpectrum.even_window` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For all real a>=2 and s squared equal1, every eigenvalue of the original symmetric3-dimensional restriction exceeds a-1 and a nonzero eigenpair has eigenvalue below a. Thus its actual smallest eigenvalue lies in(a-1,a); no chosen root is encoded as an assumption.

**Theorem 1.3 (All even squarefree prime counts).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/SquarefreeTerminalSpectrum.even_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/SquarefreeTerminalSpectrum.even_spectrum` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every even count at least4 and every distinct-prime assignment, the complete alternating construction gives an actual graph eigenvalue in the original strict consecutive-integer interval. The actual full tensor action and nonzero lift are proved, including all omitted-support zero cells.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/SquarefreeTerminalSpectrum.even_spectrum`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/SquarefreeTerminalSpectrum.even_window`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/SquarefreeTerminalSpectrum.odd_spectrum`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/Nikandish/SquarefreeAlternatingSupport](SquarefreeAlternatingSupport.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions](../PairedIdealIntersectionObstructions.md)
