# Fibonacci Convergent Error Ratio

## Abstract

Fibonacci convergents have an exact golden residual and a limiting error ratio.

<a id="describe-exact-signed-golden-residual"></a>

**Theorem 1.1 (Exact signed golden residual).**

$$\forall n\in\mathbb{N},\ F_n\varphi-F_{n+1}=-\left(-\frac{1}{\varphi}\right)^n.$$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/FibonacciErrorRatio.fibonacci_golden_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural index, multiplying the Fibonacci denominator by the golden ratio and subtracting the next Fibonacci number gives exactly the negative n-th power of the contracting factor -1/phi.

<a id="describe-adjacent-absolute-error-ratio"></a>

**Theorem 1.2 (Adjacent absolute-error ratio).**

$$e_n=\varphi-\frac{F_{n+2}}{F_{n+1}},\quad \frac{\lvert e_{n+1}\rvert}{\lvert e_n\rvert}=\frac{F_{n+1}}{F_{n+2}}\frac{1}{\varphi}.$$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/FibonacciErrorRatio.fibonacci_convergent_error_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let e_n be the signed error of the shifted Fibonacci convergent F_(n+2)/F_(n+1). Its adjacent absolute-error ratio is exactly the shifted ratio F_(n+1)/F_(n+2), divided by the golden ratio.

<a id="describe-absolute-error-ratio-limit"></a>

**Theorem 1.3 (Limit of adjacent absolute-error ratios).**

$$\lim_{n\to\infty}\frac{\lvert e_{n+1}\rvert}{\lvert e_n\rvert}=\frac{1}{\varphi^2}.$$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/FibonacciErrorRatio.fibonacci_convergent_error_ratio_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The adjacent absolute-error ratios of the shifted Fibonacci convergents tend to the reciprocal square of the golden ratio.

## References

- Truth anchor: `D5/S1/Scale/FibonacciErrorRatio.fibonacci_convergent_error_ratio`
- Truth anchor: `D5/S1/Scale/FibonacciErrorRatio.fibonacci_convergent_error_ratio_tendsto`
- Truth anchor: `D5/S1/Scale/FibonacciErrorRatio.fibonacci_golden_residual`
