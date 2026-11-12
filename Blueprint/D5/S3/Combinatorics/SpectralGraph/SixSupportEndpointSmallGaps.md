# SixSupportEndpointSmallGaps

## Abstract

Exact received three-prime spectral statements with actual ideal-graph consumers.

**Theorem 1.1 (At most two distinct positive cubic roots).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointSmallGaps.no_three_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointSmallGaps.no_three_positive` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Every real cubic with positive leading and constant coefficients has at most two distinct positive roots. The original small-gap proof and the full endpoint-one geometry consume this shared coefficient/Vieta helper; its existing proof body is reused.

**Definition 1.2 (cubic).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointSmallGaps.cubic`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointSmallGaps.cubic` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The complete source cubic h_C(1), as a polynomial in c, with all coefficients in the original parameters a,b.

**Theorem 1.3 (endpoint_identity).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointSmallGaps.endpoint_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointSmallGaps.endpoint_identity` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The cubic is exactly the characteristic quotient at one for every real a,b,c.

**Definition 1.4 (lower).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointSmallGaps.lower`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointSmallGaps.lower` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The original two lower endpoints L1=2a^2-a-2 and L2=2a^2+a-6, indexed by precisely the two gaps.

**Theorem 1.5 (result).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointSmallGaps.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointSmallGaps.result` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every real a>=2 and either gap d=1 or2, the complete cubic has exactly one root above b=a+d; it lies strictly between Ld and Ld+1. Positive-coefficient shifted identities give all signs. A cubic with positive leading and constant coefficients cannot have three distinct positive roots; the additional root in (0,b) proves uniqueness above b.

**Theorem 1.6 (integer_nonzero).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointSmallGaps.integer_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointSmallGaps.integer_nonzero` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every integer a>=2 and c>a+d, either original gap d=1 or2 has h_C(1) nonzero. The unique real root lies between consecutive integers; no finite exponent base is used.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointSmallGaps.cubic`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointSmallGaps.endpoint_identity`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointSmallGaps.integer_nonzero`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointSmallGaps.lower`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointSmallGaps.no_three_positive`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportEndpointSmallGaps.result`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/SixSupportClassificationAlgebra](SixSupportClassificationAlgebra.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/SixSupportIdealIntersectionLift](SixSupportIdealIntersectionLift.md)
