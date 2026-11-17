# Full Literal T Radial Evolution and Input Boundary

## Abstract

Full Literal T Radial Evolution and Input Boundary

**Theorem 1.1 (square_half).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.square_half`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.square_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex z with norm(z)<1, the actual squareResolvent is one half of the sum of the original resolvent and oppositeResolvent.

**Theorem 1.2 (opposite_bilinear_transpose).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.opposite_bilinear_transpose`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.opposite_bilinear_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex z with norm(z)<1 and original Hilbert vectors x,y, the oppositeResolvent has ordinary complex bilinear transpose symmetry, with no Hermitian substitution.

The square resolvent is half the sum of the two actual signed inverses. Its derivative uses the original rank-one operator derivative and ordinary bilinear transpose. The full externalT includes its identity contribution.

**Theorem 1.3 (externalT_radial_equation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.externalT_radial_equation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.externalT_radial_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all signed modes and real 0<r<1, the derivative of the actual T at sqrt(r) is the sum of its two mode frequencies plus (1-r)(V_p V_q-U_p U_q)/2, all divided by 2r.

**Theorem 1.4 (external_negative_zero_boundary).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.external_negative_zero_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.external_negative_zero_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either remaining sign and mode and 0<r<1, the literal negative-zero J row is sqrt(1-r)(V-U)/2 and the literal negative-zero T row is sqrt(1-r)(V+U)/2. Both follow from v(-,0)=-w.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.externalT_radial_equation`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.external_negative_zero_boundary`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.opposite_bilinear_transpose`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.square_half`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadial](OriginalGaussianExternalRadial.md)
