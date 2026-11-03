# SupportedFourFieldMiddleInjectivity

## Abstract

SupportedFourFieldMiddleInjectivity

**Definition 1.1 (Actual nested support).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldMiddleInjectivity.MiddleSupport`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldMiddleInjectivity.MiddleSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signed coefficient order is x,b,z,y. There is a global b lower bound, a y lower bound at each b, and a z lower bound at each b,y, all uniform in outer x. The nested bounds may depend arbitrarily on the preceding exponents.

**Theorem 1.2 (Literal middle cancellation).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldMiddleInjectivity.middle_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldMiddleInjectivity.middle_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact ten-factor Rmid is injective on this nested support. Fixed-y slices reuse the three-field triple difference and x-z kernels; fixed-z slices reuse the three-field x-y difference kernel. The balanced core is cancelled at each fixed outer x by the three-field balanced injectivity theorem. Finite Laurent translations preserve the necessary support; no fixed global cone is assumed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldMiddleInjectivity.MiddleSupport`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldMiddleInjectivity.middle_injective`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddlePolynomial](FourFieldMiddlePolynomial.md)
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial](ThreeFieldBalancedPolynomial.md)
