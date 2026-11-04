# FourPrimeIdealIntersectionObstructions

## Abstract

Actual ideal-intersection graphs and uniform higher-prime Laplacian obstructions.

The public mathematical input is unit-exponent.tex at immutable revision b93becea662a746badeadba42fdc3d3eb3db9382. General endpoint arguments follow the completed mathematical note supplied 2026-11-02. The formal proofs and this exposition are independently authored; no priority claim follows.

**Theorem 1.1 (All actual four-prime (2,2,b,c) obstructions).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FourPrimeIdealIntersectionObstructions.two_equal_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FourPrimeIdealIntersectionObstructions.two_equal_obstruction` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For four arbitrary distinct primes, every positive b,c and every permutation of the four exponent positions, the actual ideal-intersection graph is not Laplacian integral. If either tail is one, H1 applies. Otherwise the paired spectrum contains a real kappa in (1,3). The exact P2 endpoint classification excludes kappa=2 except at the unordered pair {5,8}. Away from that pair, kappa is noninteger; at the pair, the entire mod-nine family supplies a noninteger real eigenvalue. The proved paired lift gives an actual graph eigenvalue V+1-kappa. Its integrality would imply that of kappa, a contradiction.

**Theorem 1.2 (All actual four-prime (3,3,b,c) obstructions).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/FourPrimeIdealIntersectionObstructions.three_equal_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FourPrimeIdealIntersectionObstructions.three_equal_obstruction` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every four distinct primes, positive b,c and exponent-position permutation, the actual graph is nonintegral. If both tails are at least two, the paired eigenvalue kappa lies in (1,3), and the exact P3 exclusion gives kappa different from two. Its actual lift lies strictly in (V-2,V) and differs from V-1, with V=16(b+1)(c+1)-2. Thus the exact requested interval and middle-point exclusion hold. When a tail is one, H1 supplies nonintegrality at that unit boundary.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FourPrimeIdealIntersectionObstructions.three_equal_obstruction`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FourPrimeIdealIntersectionObstructions.two_equal_obstruction`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionCongruence](PairedIdealIntersectionCongruence.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift](PairedIdealIntersectionLift.md)
