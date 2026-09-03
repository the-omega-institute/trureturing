# Fourier-Laplace Closed-Strip Decay

## Abstract

Fourier-Laplace transforms of Weil test functions decay uniformly on closed strips.

**Theorem 1.1 (Uniform quadratic decay on every closed strip).**

$$\forall b \in WeilTestFunction, eta \in \mathbb{R},\; 0 \le eta \Rightarrow \left(\exists C \in \mathbb{R},\; 0 \le C \land \left(\forall w \in \mathbb{C},\; \left|w.im\right| \le eta \Rightarrow \left\lVert \operatorname{fourierLaplace}(b, w) \right\rVert \le \frac{C}{1+w.re^{2}}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/FourierLaplaceClosedStripDecay.fourierLaplace_decay_closedStrip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary nonnegative strip width eta, compact support bounds the complex exponential by exp(eta times the absolute value of x). Two integrations by parts transfer two derivatives to the test function and give a quadratic denominator in the real direction.

The constant is the sum of the zeroth- and second-derivative strip majorants. The statement is uniform over the closed strip and does not assert a zero-sum or separator-limit conclusion.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/FourierLaplaceClosedStripDecay.fourierLaplace_decay_closedStrip`
