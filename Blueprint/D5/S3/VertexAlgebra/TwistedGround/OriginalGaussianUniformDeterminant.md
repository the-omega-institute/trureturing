# Original Gaussian Uniform Trace Logarithms and Determinants

## Abstract

Original Gaussian Uniform Trace Logarithms and Determinants

For every nonnegative radius strictly below one, the original finite Gaussian trace logarithms converge uniformly on the closed complex disk. Each trace is expanded as the sum of an original signed matrix entry times a coordinate of a power of the actual cutoff operator. The geometric entry majorant controls the spatial tails, while the summable trace-length majorant controls the logarithm series. Uniform operator convergence and a telescoping power estimate control the remaining terms. The pointwise trace-log limit identifies the uniform limit.

All finite logarithms and their limit lie in one bounded closed complex ball. Continuity of the exponential on this compact ball therefore preserves uniform convergence. The finite determinant identity and the complex period identity give the literal finite determinants converging to the product of the principal-branch exponential and the existing half-binomial period. The finite matrix is squared after cutoff, including the empty section. Radius zero is included.

This supplies uniform analytic control for the original Gaussian coefficient model. Original energy-source factorization, its coefficient identity, and the full Moonshine, vertex operator algebra, conformal field theory, string theory and AdS/CFT construction require further results.

**Theorem 1.1 (finiteLog_tendstoUniformlyOn).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformDeterminant.finiteLog_tendstoUniformlyOn`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformDeterminant.finiteLog_tendstoUniformlyOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual finite trace logarithms converge to gaussianLogDet uniformly on every closed disk of nonnegative radius less than one.

**Theorem 1.2 (finite_determinants_tendstoUniformlyOn_period).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformDeterminant.finite_determinants_tendstoUniformlyOn_period`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformDeterminant.finite_determinants_tendstoUniformlyOn_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Determinants of one minus the square of each original finite section converge uniformly on the same disk to exp((1/4) log(1-z squared)) times period(z squared). The period occurs as a product factor.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformDeterminant.finiteLog_tendstoUniformlyOn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformDeterminant.finite_determinants_tendstoUniformlyOn_period`
- Dependency: [D5/S3/Quantum/Analysis/TrotterProduct](../../Quantum/Analysis/TrotterProduct.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity](OriginalGaussianPeriodIdentity.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff](OriginalGaussianUniformCutoff.md)
