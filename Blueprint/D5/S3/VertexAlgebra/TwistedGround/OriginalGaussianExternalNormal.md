# Joint Normal Bounds for the Literal Kernels

## Abstract

Joint Normal Bounds for the Literal Kernels

The finite antidiagonal binomial theorem reduces every polynomial frequency majorant to a polynomial times (delta+rho)^n. The smaller joint disk delta+rho<1 suffices; no uniform external radius at the whole radial disk boundary is asserted. These estimates do not by themselves establish differentiation of every generated equation.

**Theorem 1.1 (external_binomial_joint_summable).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.external_binomial_joint_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.external_binomial_joint_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either sign, every natural polynomial degree d and nonnegative delta,rho with delta+rho<1, the double sum of (p+s+1)^d delta^p rho^s times the norm of the actual external binomial is summable.

**Theorem 1.2 (externalColumn_joint_summable).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.externalColumn_joint_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.externalColumn_joint_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either sign and complex u,z with norm(u)+norm(z)<1, the joint sum of norm(u)^p times the norm of the original externalColumn at n is summable.

**Theorem 1.3 (externalVector_mode_summable).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.externalVector_mode_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.externalVector_mode_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either sign and norm(u)+norm(z)<1, the norms of the actual Hilbert-space mode vectors u^p externalVector are summable.

**Theorem 1.4 (external_kernel_mode_summable).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.external_kernel_mode_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.external_kernel_mode_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For both signs and complex u,v,z with norm(u)+norm(z)<1 and norm(v)+norm(z)<1, the full actual J and full actual T external mode double series are norm summable.

**Theorem 1.5 (sourceAmplitude_joint_summable).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.sourceAmplitude_joint_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.sourceAmplitude_joint_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either sign and norm(u)+norm(x)<1, the joint absolute series of the evaluated A coefficients times x^n u^p is summable.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.externalColumn_joint_summable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.externalVector_mode_summable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.external_binomial_joint_summable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.external_kernel_mode_summable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.sourceAmplitude_joint_summable`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadial](OriginalGaussianExternalRadial.md)
