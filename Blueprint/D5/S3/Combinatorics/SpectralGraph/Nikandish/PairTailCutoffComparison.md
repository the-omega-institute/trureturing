# The complete old/new uniform tail-cutoff comparison

## Abstract

The complete old/new uniform tail-cutoff comparison

Sources: four-prime-large-tail and four-prime-tail-reduction, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. All positive repeated and first-tail exponents are retained, with no relative ordering. The old large-tail graph conclusion is reused through the stronger quadratic cutoff; this does not supply the separate original ordered-second-eigenvalue statement or claim to rerun original exact controls. Necessary candidate membership never proves integrality. Original attribution, prerequisites, reported controls, failed methods and general Q3 boundaries remain. The escape audit is unfinished under linked issue #28398.

**Theorem 1.1 (The full strict improvement by more than 128).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCutoffComparison.cutoff_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCutoffComparison.cutoff_comparison` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The floor of d squared over four remains actual integer division. The proof establishes 128Q<R for every positive integer a and b.

For the original five/five application, a=b=5 gives d=(a+1)b=30, floor(d squared/4)=225 and M=(a+1)(b+1)=36. Substitution into PairTailCandidates.cutoff gives Q=225(225+5(30-1)+25 times 5)=111375. Substitution into oldCutoff gives R=24(36+5) cubed times (3 times 36+5)=186913752. These are applications of the cutoff definitions; the uniform strict comparison and actual-graph conclusion retain their full parameter ranges.

**Theorem 1.2 (Every actual ideal graph beyond the old cutoff is nonintegral).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCutoffComparison.actual_large_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCutoffComparison.actual_large_tail` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

All four distinct graph primes and every positive repeated and first-tail exponent are retained. The stronger full actual-graph quadratic candidate bound supplies the conclusion without a tail scan.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCutoffComparison.actual_large_tail`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCutoffComparison.cutoff_comparison`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailCandidates](PairTailCandidates.md)
