# Radial Derivative of the Literal Original Source Constant

## Abstract

Radial Derivative of the Literal Original Source Constant

The real derivative of the source-column pairing is computed using the existing vector derivatives, the ordinary bilinear transpose, the scaled radial column derivative and the exact pair normalization. Real differentiation of star and the inner product retains all conjugations correctly. Eventual equality with source_pairings_explicit transfers the result to the literal sourceConstant series, including its inverse-frequency factor.

**Theorem 1.1 (hasDerivAt_radial_source_pairing).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceDerivative.hasDerivAt_radial_source_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceDerivative.hasDerivAt_radial_source_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real r strictly between zero and one, the real radial source-column pairing has complex derivative equal to the real coefficient (1/((1-r)F(r)^2)-1)/(2r).

**Theorem 1.2 (hasDerivAt_radial_sourceConstant).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceDerivative.hasDerivAt_radial_sourceConstant`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceDerivative.hasDerivAt_radial_sourceConstant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real r strictly between zero and one, u mapped to sourceConstant(sqrt(u)) has complex derivative equal to the embedded real coefficient (1/((1-r)F(r)^2)-1)/(2r).

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceDerivative.hasDerivAt_radial_sourceConstant`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceDerivative.hasDerivAt_radial_source_pairing`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBilinearTranspose](OriginalGaussianBilinearTranspose.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceMeans](OriginalGaussianSourceMeans.md)
