# Finite Evaluation of the Literal Signed Source

## Abstract

Finite Evaluation of the Literal Signed Source

The finite Vandermonde identity is summed only after proving absolute double convergence. It evaluates the same-source sourceExternal, with 1-sourceExternal=A/F. No replacement source or covariance hypothesis is introduced.

**Theorem 1.1 (external_parameter_bound).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceEvaluation.external_parameter_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceEvaluation.external_parameter_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either Bool label and every natural mode p, the complex norm of its signed half-integer binomial parameter is at most p+1.

**Definition 1.2 (sourceAmplitude).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceEvaluation.sourceAmplitude`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceEvaluation.sourceAmplitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For either signed label, natural p and complex x, A is the centralWeight series with coefficient (-1)^n choose(alpha-1/2,n). The full n=0 term is retained.

**Theorem 1.3 (sourceAmplitude_hasSum).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceEvaluation.sourceAmplitude_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceEvaluation.sourceAmplitude_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every signed mode and complex x with norm less than one, the normally summable shifted-central convolution, including s=0, sums to A.

**Theorem 1.4 (sourceExternal_evaluation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceEvaluation.sourceExternal_evaluation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceEvaluation.sourceExternal_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every signed mode and complex z with norm less than one, 1 minus the actual sourceExternal equals A at z squared divided by the original period at z squared.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceEvaluation.external_parameter_bound`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceEvaluation.sourceAmplitude`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceEvaluation.sourceAmplitude_hasSum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceEvaluation.sourceExternal_evaluation`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceMeans](OriginalGaussianSourceMeans.md)
