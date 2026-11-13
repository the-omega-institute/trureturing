# Full paired-tensor middle-root separation and actual graph applications

## Abstract

Full paired-tensor middle-root separation and actual graph applications

Sources: the entire original large-tail and harmonic-tail manuscripts, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The harmonic source assumes all positive natural a,b,c with b<c and no ordering between a and b. The full four-value spectrum retains multiplicity. The lower ordered value is the second-smallest and the next is the third-smallest. Both lift through the existing actual ideal-intersection graph application for every injective prime assignment. Original attribution, prerequisites, source reports, failed methods, uncertainties and rights boundaries remain unchanged. Root conditions and candidate tests do not establish integral spectrum. General Q3, a6 certification and finite-enumeration reproduction limits remain open.

**Theorem 1.1 (Full bounded middle-root separation).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSeparation.bounded_separation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSeparation.bounded_separation` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every real a>0,b>0,c>=1 the bounded endpoint (a+1)(b+1) lies strictly between the ordered second-smallest and third-smallest roots; the second-smallest also exceeds a+1.

**Theorem 1.2 (Entire original harmonic separation and endpoint chain).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSeparation.harmonic_separation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSeparation.harmonic_separation` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every real a>=1,b>=1,c>b, the full chain a+b+1 < kappa2 < a+1+2bc/(b+c) < kappa3 holds, with the strict endpoint bound a+1+2bc/(b+c) < a+2b+1.

**Theorem 1.3 (Every ordered tensor value lifts to the actual graph).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSeparation.actual_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSeparation.actual_spectrum` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every positive natural a,b,c and every distinct-prime assignment, every one of the four sorted values yields the stated actual graph Laplacian eigenvalue V+1-kappa.

**Theorem 1.4 (Both middle values are actual graph eigenvalues).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSeparation.actual_harmonic_separation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSeparation.actual_harmonic_separation` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The original complete harmonic chain and both genuine graph eigenvalue applications hold together over all positive natural parameters with b<c, without an order restriction between a and b.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSeparation.actual_harmonic_separation`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSeparation.actual_spectrum`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSeparation.bounded_separation`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailSeparation.harmonic_separation`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailOrdering](PairTailOrdering.md)
