# The hyperbolic Laplace kernel

## Abstract

A positive Laplace representation for the logarithmic Wallis remainder.

**Theorem 1.1 (Absolute convergence).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Laplace.integrableOn_laplaceKernel`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Laplace.integrableOn_laplaceKernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive x, the function exp(-xt) tanh(t/4)/(2t) is integrable over positive t. The hyperbolic sine bound gives an upper bound exp(-xt)/8.

**Theorem 1.2 (The integral representation).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Laplace.r_eq_laplace`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Laplace.r_eq_laplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive x, minus log B(x) equals the integral of exp(-xt) tanh(t/4)/(2t) over positive t. Gamma recurrence gives a half-step equation, and log convexity gives a nonnegative remainder tending to zero. The exponential case of Frullani's integral evaluates the corresponding difference integral. The proposed integral obeys the same half-step equation and tends to zero; their difference is periodic with period one, so the difference vanishes.

## References

- Truth anchor: `D5/S3/Analytic/WallisRemainder/Laplace.integrableOn_laplaceKernel`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Laplace.r_eq_laplace`
- Dependency: [D5/S3/Analytic/WallisRemainder/Defs](Defs.md)
- Dependency: [D5/S3/Observer/Fluctuation/ThermalCoefficientFloor](../../Observer/Fluctuation/ThermalCoefficientFloor.md)
