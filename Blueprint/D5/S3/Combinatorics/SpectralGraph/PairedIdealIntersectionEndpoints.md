# PairedIdealIntersectionEndpoints

## Abstract

Actual ideal-intersection graphs and uniform higher-prime Laplacian obstructions.

The public mathematical input is unit-exponent.tex at immutable revision b93becea662a746badeadba42fdc3d3eb3db9382. General endpoint arguments follow the completed mathematical note supplied 2026-11-02. The formal proofs and this exposition are independently authored; no priority claim follows.

**Definition 1.1 (Exact H4 endpoint polynomial).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionEndpoints.P2`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionEndpoints.P2` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

P2(b,c)=-5 b squared c squared+12 b squared c-3 b squared+12 b c squared+48bc+8b-3c squared+8c+3. It is the determinant of K2 minus twice the identity.

**Definition 1.2 (Exact H5 endpoint polynomial).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionEndpoints.P3`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionEndpoints.P3` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

P3(b,c)=-7 b squared c squared+48 b squared c-8 b squared+48 b c squared+302bc+76b-8 c squared+76c+40. It is the determinant of K3 minus twice the identity.

**Theorem 1.3 (Complete unbounded H4 endpoint classification).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionEndpoints.P2_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionEndpoints.P2_zero_iff` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every integer b,c at least two, P2 is zero exactly at (5,8) and (8,5). Order b at most c. Parity excludes both even. Modulo three, b congruent to one would force a square root of minus one, which cannot exist in F3. For b at least six and c at least seven, write P2=-c(dc-B)-e with d=5b squared-12b+3, e=(3b+1)(b-3), B=12b squared+48b+8; all required factors are strictly positive. The only remaining symbolic rows are b=2,3,5; their formulas are c squared+152c+7, 4c(65-3c), and -4(c-8)(17c-1). These arguments cover the entire unbounded domain, not a finite list of exponent pairs.

**Theorem 1.4 (Complete unbounded H5 endpoint exclusion).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionEndpoints.P3_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionEndpoints.P3_nonzero` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

A hypothetical zero forces b,c both even by reduction modulo two and eight. Put b=2u,c=2v with 1 at most u at most v. P3=8Q where Q=-(14u squared-48u+4)v squared+(48u squared+151u+19)v-(4u+1)(u-5). The whole range u from one to three is positive; the infinite range u at least nine is negative. Rows u=4,6,8 have successive integer sign gaps at v=38/39,12/13,8/9 respectively. Rows u=5,7 factor as -6v(19v-329) and -2(3v-29)(59v-1), whose possible zero equations contradict integer divisibility. Every larger coordinate remains unbounded. No nonsquare table is a premise.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionEndpoints.P2`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionEndpoints.P2_zero_iff`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionEndpoints.P3`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionEndpoints.P3_nonzero`
