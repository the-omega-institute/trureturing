# Axis Convergence

## Abstract

Positive-x Zeckendorf axis sums converge, with a doubly-exponential depth tail.

Each natural number is read through its Zeckendorf digits. Positivity of the first coordinate makes the golden-ratio contribution decay at least geometrically in the represented integer, while the conjugate contribution has a uniform geometric budget. This gives absolute summability for every real second coordinate.

The depth-K window contains exactly the integers below Fib(K+1), so ordinary series convergence gives convergence of the axis partial sums. The omitted geometric tail begins there. Comparing Fib(K+1) with phi^K / phi converts that tail into the displayed doubly-exponential depth bound.

The condition x > 0 is essential. At x = y = 0 every word has weight one, the depth-K partial sum is Fib(K+1), and the sequence diverges to positive infinity. This is the corrected boundary clause of PZG 6.35.

**Theorem 1.1 (Positive-x word weights are summable).**

$$\forall x,y \in \mathbb{R}, 0 < x \Rightarrow \operatorname{Summable}(n \mapsto w_{x,y}(n)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/AxisConvergence.wordWeight_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof uses the pointwise geometric majorant obtained from the two Zeckendorf embedding estimates.

**Theorem 1.2 (Positive-x axis partial sums converge).**

$$\forall x,y \in \mathbb{R}, 0 < x \Rightarrow \lim_{K\to\infty} W_{K}(x,y) = \sum_{n=0}^{\infty} w_{x,y}(n).$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/AxisConvergence.axisPartialSum_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Series convergence is restricted along the cofinal Fibonacci cutoffs that define the depth windows.

**Theorem 1.3 (The axis tail is doubly exponentially small).**

$$\forall x,y \in \mathbb{R}, 0 < x \Rightarrow \forall K \in \mathbb{N}, \lvert W_{K}(x,y) - \sum_{n=0}^{\infty} w_{x,y}(n) \rvert \le \frac{\exp(\lvert y \rvert \cdot \frac{\lvert \psi \rvert}{1-\lvert \psi \rvert})}{1-\exp(-x)} \cdot \exp(-(\frac{x}{\varphi}) \cdot \varphi^{K}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/AxisConvergence.axisPartialSum_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact geometric tail constant is retained, and the Fibonacci cutoff is bounded below by phi^K / phi to obtain the depth rate.

**Theorem 1.4 (The origin window is Fibonacci).**

$$\forall K \in \mathbb{N}, W_{K}(0,0) = Fib_{K+1}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/AxisConvergence.axisPartialSum_zero_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every word weight is one at the origin, so the window cardinality is exactly the next Fibonacci number.

**Theorem 1.5 (The origin window diverges).**

$$\lim_{K\to\infty} W_{K}(0,0) = +\infty.$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/AxisConvergence.axisPartialSum_zero_zero_tendsto_atTop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Fibonacci identity turns standard Fibonacci growth into divergence of the partial sums to positive infinity.

## References

- Truth anchor: `D5/S3/Axis/AxisConvergence.axisPartialSum_tail_bound`
- Truth anchor: `D5/S3/Axis/AxisConvergence.axisPartialSum_tendsto`
- Truth anchor: `D5/S3/Axis/AxisConvergence.axisPartialSum_zero_zero`
- Truth anchor: `D5/S3/Axis/AxisConvergence.axisPartialSum_zero_zero_tendsto_atTop`
- Truth anchor: `D5/S3/Axis/AxisConvergence.wordWeight_summable`
- Dependency: [D5/S3/Axis/AxisPartialSum](AxisPartialSum.md)
