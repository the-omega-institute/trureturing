# Contraction-Face Dirichlet Series

## Abstract

The contraction-face Dirichlet series splits into zeta and a prime-axis factor.

**Theorem 1.1 (The contraction-face series has a diagonal prime-axis decomposition).**

$$\forall s\in\mathbb{C}, \operatorname{Re}(s) > 1,\\\sum_{n \geq 1}lambdaMinus(n)n^{-s} = \zeta(s)\,H(s),\\H(s) = \sum_{p \text{prime}}\operatorname{log}(p)(1-p^{-s})\sum_{v \geq 1}betaContraction(v)p^{-vs},\\\forall v\in\mathbb{N}, \lvert betaContraction(v) \rvert < 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/LambdaMinusDirichletSeries.lambda_minus_dirichlet_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The repository contraction reading is additive on coprime inputs. Its one-step prime-power differences form an arithmetic function supported on prime powers, and divisor summation recovers lambdaMinus.

Mathlib's convolution theorem supplies the zeta factor. Its exact prime-power support reindexing theorem turns the remaining L-series into a sum over primes and positive exponents; a convergent telescoping identity gives the displayed local factor.

The existing radical bound applied to powers of two gives the strict unit window for every betaContraction exponent. No finite truncation or numerical certificate is used.

## References

- Truth anchor: `D5/S3/Axis/LambdaMinusDirichletSeries.lambda_minus_dirichlet_series`
- Dependency: [D5/S1/Deficit/Displacement/GoldenContractionRadicalBound](../../S1/Deficit/Displacement/GoldenContractionRadicalBound.md)
- Dependency: [D5/S1/Deficit/LambdaMinusAdditive](../../S1/Deficit/LambdaMinusAdditive.md)
