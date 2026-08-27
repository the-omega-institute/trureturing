# Golden Displacement Series Limit at Infinity

## Abstract

The golden displacement series tends to one as its first parameter tends to infinity.

**Theorem 1.1 (The displacement series tends to one).**

$$\forall w \in \mathbb{R},\quad\\\lim_{s \to \infty} \sum_{n=0}^{\infty} \operatorname{dTerm}(s, w, n) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/GoldenDisplacementSeriesTendstoOne.golden_displacement_series_tendsto_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real w, as s tends to positive infinity, the sum of dTerm(s,w) tends to one. No summability hypothesis is required.

The terms at indices zero and one are identically zero and one. At every index n at least two, le_nS gives nS(n) at least n, hence strictly greater than one. Its negative-s real power therefore tends to zero, while the n-dependent second factor stays fixed.

For the fixed w, set s0=max(0,1-w)+1. Then s0 is nonnegative and s0+w is strictly greater than one, so dTerm_summable gives absolute summability at (s0,w). Term nonnegativity converts this to summability of dTerm(s0,w). Eventually s is at least s0, and the exported termwise parameter-order inequality then bounds the nonnegative term dTerm(s,w,n) by the summable baseline term dTerm(s0,w,n). Mathlib's dominated convergence theorem for infinite sums passes the pointwise limit through the sum.

The theorem does not claim a convergence rate, uniformity in w, a joint two-parameter limit, an infimum characterization, or any finite-s evaluation of the series.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/GoldenDisplacementSeriesTendstoOne.golden_displacement_series_tendsto_one`
- Dependency: [D5/S3/Analytic/Monotonicity/GoldenDisplacementSeriesStrictAntitone](../Monotonicity/GoldenDisplacementSeriesStrictAntitone.md)
