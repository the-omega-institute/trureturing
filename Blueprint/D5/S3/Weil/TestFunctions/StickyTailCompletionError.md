# Sticky-Tail Completion Error

## Abstract

A uniform first-variable Herglotz-kernel derivative estimate gives the quantitative sticky-tail completion error bound.

**Theorem 1.1 (Sticky-tail positive completion error).**

$$\forall r \in \mathbb{R}, D \in \mathbb{R}, z \in \mathbb{C}, Cxi \in \mathbb{C} \to \mathbb{C}, CT \in \mathbb{C} \to \mathbb{C},\; \left\lVert Cxi\left(z\right) - CT\left(z\right) \right\rVert \le \frac{2 \cdot r}{{1 - r}^{2}} \cdot D$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/StickyTailCompletionError.sticky_tail_completion_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the unit circle, the reverse triangle inequality bounds the kernel denominator below by one minus the disk radius. Differentiating in the spectral variable produces a squared denominator and hence the stated uniform constant.

The completion functions and tail budget are abstract parameters. The source's omitted transport and summation step is represented by an explicit hypothesis that converts the uniform derivative bound into a completion error estimate.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/StickyTailCompletionError.sticky_tail_completion_error`
- Dependency: [D5/S3/Weil/Budget/CaratheodoryScaleCovariance](../Budget/CaratheodoryScaleCovariance.md)
