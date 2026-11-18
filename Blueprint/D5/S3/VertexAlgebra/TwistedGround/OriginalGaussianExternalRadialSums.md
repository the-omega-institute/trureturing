# Radial Differentiation of the Original T Generator

## Abstract

Radial Differentiation of the Original T Generator

The literal square-resolvent mode series is differentiated on the radial square-root disk by a local complex normal-convergence argument.

**Theorem 1.1 (literal_differentiable).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.literal_differentiable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.literal_differentiable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original full T mode, for all signed indices, is complex differentiable at every point of the unit disk. The existing scalar pairing and resolvent proof supplies the actual positive difference power-series expansions used in the finite candidate identification.

**Theorem 1.2 (kernelMode_radial_derivative).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.kernelMode_radial_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.kernelMode_radial_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every signed pair and 0<r<1 with the two mode radii inside the convergence disk, the real radial derivative of the full literal T generator is the normally convergent sum of the radial derivatives of its original mode coefficients. The proof uses the actual external vectors, square resolvent, and square-root chain rule.

**Theorem 1.3 (radial_differential).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.radial_differential`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.radial_differential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every signed pair and 0<r<1 inside the joint convergence disk, the complete original T radial derivative, after subtracting both genuine frequency actions, equals the product of the two literal source modes times the difference of the two diagonal jet products. The proof retains the square-root boundary normalization and the actual zero-row correction.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.kernelMode_radial_derivative`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.literal_differentiable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.radial_differential`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations](OriginalGaussianExternalEquations.md)
