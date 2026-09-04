# Axis Convergence

## Abstract

Positive-axis word sums converge with an explicit double-exponential tail, and every finite truncation has a strictly positive remainder.

**Theorem 1.1 (The axis truncation has a double-exponential tail).**

$$\forall x, y \in \mathbb{R}, K \in \mathbb{N},\ 0 < x \Rightarrow |\operatorname{axisPartialSum}(x, y, K) - \sum_{n=0}^{\infty} \operatorname{wordWeight}(x, y, n)| \leq \frac{\exp{|y|\cdot\frac{|\psi|}{1-|\psi|}}}{1-\exp{-x}}\cdot\exp{-\frac{x}{\phi}\cdot\phi^{K}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/AxisConvergence.axisPartialSum_tsum_double_exponential_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x strictly positive and arbitrary real y, each word weight is bounded by exp(|y| B) exp(-x)^n, where B is |psi|/(1 - |psi|). This proves summability by comparison with a geometric series.

The main-embedding estimate uses the exact Zeckendorf Fibonacci sum. The conjugate estimate uses distinct occupied indices and the full geometric series in |psi|. Summing from fib(K + 1) gives a geometric tail, and phi^K/phi <= fib(K + 1) converts it to the displayed double-exponential rate.

The companion theorem axisPartialSum_lt_tsum supplies the other side: every finite truncation omits a strictly positive word. Thus the absolute error being bounded is never vacuously zero.

The condition 0 < x is essential. At x = y = 0 every word has weight one and the partial sums diverge along the Fibonacci cutoffs.

## References

- Truth anchor: `D5/S3/Axis/AxisConvergence.axisPartialSum_tsum_double_exponential_tail`
- Dependency: [D5/S3/AnalyticClosure/PositiveSeriesTail](../AnalyticClosure/PositiveSeriesTail.md)
- Dependency: [D5/S3/Axis/AxisPartialSum](AxisPartialSum.md)
