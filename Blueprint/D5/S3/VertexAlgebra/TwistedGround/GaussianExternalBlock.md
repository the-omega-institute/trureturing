# GaussianExternalBlock

## Abstract

GaussianExternalBlock

Finite external coordinates and square-summable mixed rows define bounded bilinear Gaussian block operators. A positive external scale makes the joint operator a strict Hilbert-Schmidt contraction.

**Theorem 1.1 (Actual bilinear coordinate functional).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianExternalBlock.bilinear_eq_tsum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianExternalBlock.bilinear_eq_tsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bounded complex-linear functional is inner(star r,z). The coordinate conjugation cancels the conjugate-linear first slot of the Hilbert inner product, giving sum_i r_i z_i. Analytic estimates may use Hilbert inner products, but the sewing contraction has no coordinate conjugation.

**Theorem 1.2 (A genuine scaled joint operator).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianExternalBlock.operator_entry`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianExternalBlock.operator_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Extend A to the internal summand by the orthogonal coordinate inclusion and its adjoint. Add the actual finite sum of bilinear rank-one mixed terms and the external rank-one matrix. The resulting bounded operator polynomial has entries [[t^2 P,tR],[tR^t,A]]. No Gaussian coefficient or norm conclusion is stored as data.

**Theorem 1.3 (A positive external scale).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianExternalBlock.exists_positive_scale`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianExternalBlock.exists_positive_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At t=0 the actual bounded joint operator is just the orthogonal extension of A, whose norm is strictly less than one. Continuity of the operator polynomial and of its norm yields a positive real t for which the full scaled joint operator is a strict contraction. This imposes no restriction on the original finite P or mixed l2 rows.

**Theorem 1.4 (The two mixed rectangles).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/GaussianExternalBlock.operator_square_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/GaussianExternalBlock.operator_square_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The external rectangle is finite. Each mixed rectangle has a finite family of actual square-summable rows or columns. The remaining rectangle is the given Hilbert-Schmidt matrix of A. Splitting the product index into four disjoint rectangles proves the true full matrix square sum is finite.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianExternalBlock.bilinear_eq_tsum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianExternalBlock.exists_positive_scale`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianExternalBlock.operator_entry`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/GaussianExternalBlock.operator_square_summable`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock](InfiniteGaussianFock.md)
