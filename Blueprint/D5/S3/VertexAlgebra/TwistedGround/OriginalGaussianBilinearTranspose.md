# Ordinary Bilinear Transpose of the Original Gaussian

## Abstract

Ordinary Bilinear Transpose of the Original Gaussian

The pairing is the ordinary complex bilinear sum, implemented by innerSL with star in the first slot. The literal symmetric kernel passes through the norm-absolutely summable rank-one operator series using continuous linear maps and product-index interchange. The actual Neumann inverse inherits this transpose from its geometric inverse identity.

**Theorem 1.1 (sourceBilinearFunctional_comm).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBilinearTranspose.sourceBilinearFunctional_comm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBilinearTranspose.sourceBilinearFunctional_comm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all square-summable complex vectors x and y, the ordinary source bilinear functional is symmetric.

**Theorem 1.2 (operator_bilinear_transpose).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBilinearTranspose.operator_bilinear_transpose`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBilinearTranspose.operator_bilinear_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex z of norm less than one and all square-summable x and y, B(x,K(z)y)=B(K(z)x,y).

**Theorem 1.3 (resolvent_bilinear_transpose).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBilinearTranspose.resolvent_bilinear_transpose`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBilinearTranspose.resolvent_bilinear_transpose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex z of norm less than one and all square-summable x and y, B(x,R(z)y)=B(R(z)x,y), where R is the actual signed Neumann inverse of one minus K.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBilinearTranspose.operator_bilinear_transpose`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBilinearTranspose.resolvent_bilinear_transpose`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBilinearTranspose.sourceBilinearFunctional_comm`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation](OriginalGaussianDifferentiation.md)
