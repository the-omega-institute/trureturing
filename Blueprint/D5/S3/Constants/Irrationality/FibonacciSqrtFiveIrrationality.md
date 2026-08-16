# Fibonacci Square-Root-Five Irrationality

## Abstract

Odd Fibonacci-square-root-five layer constants are irrational.

**Theorem 1.1 (Odd layer constants are irrational).**

$$m=2k+1 \implies \operatorname{Irrational}(\frac{1}{F_m \sqrt{5}}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Irrationality/FibonacciSqrtFiveIrrationality.odd_layer_constant_irrational` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An odd index is positive, so its Fibonacci number is nonzero. The square root of five is irrational because five is prime. Multiplying by the nonzero Fibonacci number and then taking the reciprocal both preserve irrationality.

This closes only the irrationality of the source atom's stated odd-layer expression 1/(F_m sqrt(5)). It does not identify an independently defined tower constant, prove the even-layer formula, or close any of the d = 48 preregistered claims.

## References

- Truth anchor: `D5/S3/Constants/Irrationality/FibonacciSqrtFiveIrrationality.odd_layer_constant_irrational`
