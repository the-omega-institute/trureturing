# Maximal real-part projection

## Abstract

An absolutely summable exponential series projects asymptotically onto its maximal real-part line.

Let a and z be complex sequences indexed by ℕ and let Θ and t be real. Write P(t) for the sum over indices with Re(z(n))=Θ. The other terms decay after normalization.

**Definition 1.1 (Series on the maximal real-part line).**

Lean statement: `D5/S3/Analytic/Laplace/MaximalRealPartProjection.maximalSeries`

*Formalization.* `D5/S3/Analytic/Laplace/MaximalRealPartProjection.maximalSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P(t) is the sum of the maximal terms over ℕ.

**Theorem 1.2 (Uniform continuity of the projection).**

Lean statement: `D5/S3/Analytic/Laplace/MaximalRealPartProjection.uniformContinuous_maximalSeries`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/MaximalRealPartProjection.uniformContinuous_maximalSeries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With summable coefficient norms, P is uniformly continuous as a uniform limit of uniformly continuous finite Fourier sums.

**Theorem 1.3 (Projection of the externally normalized sum).**

Lean statement: `D5/S3/Analytic/Laplace/MaximalRealPartProjection.tendsto_exp_mul_tsum_sub_maximalSeries`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/MaximalRealPartProjection.tendsto_exp_mul_tsum_sub_maximalSeries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the coefficient norms are summable and Re(z(n))≤Θ for all n, then exp(−Θt) ∑ₙ a(n) exp(t z(n))−P(t) tends to zero as t tends to +∞.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/MaximalRealPartProjection.maximalSeries`
- Truth anchor: `D5/S3/Analytic/Laplace/MaximalRealPartProjection.tendsto_exp_mul_tsum_sub_maximalSeries`
- Truth anchor: `D5/S3/Analytic/Laplace/MaximalRealPartProjection.uniformContinuous_maximalSeries`
