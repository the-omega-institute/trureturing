# Complex Radial Differentiation of the Original J/T Generators

## Abstract

Complex Radial Differentiation of the Original J/T Generators

Both original J/T mode series admit complex radial differentiation on norm(u)+norm(z)<1 and norm(v)+norm(z)<1. The actual odd and square resolvents, bilinear external-vector contractions and existing summable vector bounds supply the local normal-convergence proof. The real square-root T derivative and its radial PDE retain their original conclusions.

**Theorem 1.1 (kernel_complex_derivative).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.kernel_complex_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.kernel_complex_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For square,out,out' ranging over Bool and arbitrary complex u,v,z with norm(u)+norm(z)<1 and norm(v)+norm(z)<1, the derivatives in z of the original selected externalT or externalJ coefficients, multiplied by u^p v^q, have sum equal to the complex derivative of kernelMode(square,out,out',u,v,z). The same kernel is complex differentiable at z. Mathlib normal-sum differentiation applies to the existing larger-radius external-vector majorants; odd-resolvent holomorphy follows from odd_eq_half_difference. Zero, axes and diagonal remain in the domain. This proves radial holomorphy and derivative interchange; equality with an analytic candidate is a separate obligation.

**Theorem 1.2 (literal_differentiable).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.literal_differentiable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.literal_differentiable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original full T mode, for all signed indices, is complex differentiable at every point of the unit disk. The existing scalar pairing and resolvent proof supplies the actual positive difference power-series expansions used in the finite candidate identification.

**Theorem 1.3 (kernelMode_radial_derivative).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.kernelMode_radial_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.kernelMode_radial_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every signed pair and 0<r<1 with the two mode radii inside the convergence disk, the real radial derivative of the full literal T generator is the normally convergent sum of the radial derivatives of its original mode coefficients. The proof uses the actual external vectors, square resolvent, and square-root chain rule.

**Theorem 1.4 (radial_differential).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.radial_differential`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.radial_differential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every signed pair and 0<r<1 inside the joint convergence disk, the complete original T radial derivative, after subtracting both genuine frequency actions, equals the product of the two literal source modes times the difference of the two diagonal jet products. The proof retains the square-root boundary normalization and the actual zero-row correction.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.kernelMode_radial_derivative`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.kernel_complex_derivative`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.literal_differentiable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums.radial_differential`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations](OriginalGaussianExternalEquations.md)
