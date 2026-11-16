# Full Literal T Radial Evolution and Input Boundary

## Abstract

Full Literal T Radial Evolution and Input Boundary

The square resolvent is half the sum of the two actual signed inverses. Its derivative uses the original rank-one operator derivative and ordinary bilinear transpose. The full externalT includes its identity contribution.

**Theorem 1.1 (externalT_radial_equation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.externalT_radial_equation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.externalT_radial_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all signed modes and real 0<r<1, the derivative of the actual T at sqrt(r) is the sum of its two mode frequencies plus (1-r)(V_p V_q-U_p U_q)/2, all divided by 2r.

**Theorem 1.2 (external_negative_zero_boundary).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.external_negative_zero_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.external_negative_zero_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either remaining sign and mode and 0<r<1, the literal negative-zero J row is sqrt(1-r)(V-U)/2 and the literal negative-zero T row is sqrt(1-r)(V+U)/2. Both follow from v(-,0)=-w.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.externalT_radial_equation`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.external_negative_zero_boundary`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadial](OriginalGaussianExternalRadial.md)
