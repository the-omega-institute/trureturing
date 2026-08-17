# Golden Fibonacci Series

## Abstract

The golden-conjugate weighting of the shifted Fibonacci scale has an exact sum.

**Theorem 1.1 (The alternating golden Fibonacci scale sums exactly).**

$$\sum_{k=0}^{\infty} \frac{\psi^{k} \cdot F_{k+1}}{\varphi^{k+2}} = \frac{1}{2 \varphi}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Limits/GoldenFibonacciSeries.golden_fibonacci_series_has_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's Binet formula splits each shifted Fibonacci number into golden-ratio and golden-conjugate powers. After the source weighting is distributed, both parts are summable geometric series. Their closed forms reduce with the quadratic golden-ratio identities to one half of the reciprocal golden ratio.

This partial closure covers the exact alternating-series identity in part two of the source atom and hence its stated r-bar value. It does not formalize the C-zero identity, the Mobius minus-two rule, the claimed value of D at one from below, or any critical-line remainder.

## References

- Truth anchor: `D5/S3/Constants/Limits/GoldenFibonacciSeries.golden_fibonacci_series_has_sum`
