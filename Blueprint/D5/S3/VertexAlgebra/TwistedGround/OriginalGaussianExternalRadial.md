# Differentiation of the Original External Vectors

## Abstract

Differentiation of the Original External Vectors

Polynomial-geometric bounds justify differentiating the complete Hilbert-space external series. The radial derivative is obtained by the real square-root chain rule at positive r, not by changing the original series.

**Definition 1.1 (externalDerivative).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadial.externalDerivative`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadial.externalDerivative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The derivative vector is the termwise differentiated original external-column Hilbert series, with coefficient (n+1) z^n.

**Theorem 1.2 (hasDerivAt_externalVector).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadial.hasDerivAt_externalVector`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadial.hasDerivAt_externalVector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either label, every natural p and complex norm(z)<1, externalVector has the complex derivative externalDerivative.

**Theorem 1.3 (hasDerivAt_radial_externalVector).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadial.hasDerivAt_radial_externalVector`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadial.hasDerivAt_radial_externalVector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all signed modes and real 0<r<1, the real derivative of externalVector at sqrt(r) is frequencyVector divided by 2r.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadial.externalDerivative`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadial.hasDerivAt_externalVector`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadial.hasDerivAt_radial_externalVector`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments](OriginalGaussianExternalMoments.md)
