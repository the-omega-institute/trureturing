# PntSmoothing

## Abstract

The smoothed Chebyshev integral has a quantified smoothing error.

**Definition 1.1 (SmoothedChebyshevIntegrand).**

Lean statement: `D5/S3/Weil/PrimeNumberTheorem/PntSmoothing.SmoothedChebyshevIntegrand`

*Formalization.* `D5/S3/Weil/PrimeNumberTheorem/PntSmoothing.SmoothedChebyshevIntegrand` (`✓ std3`).

*Citation.* PrimeNumberTheoremAnd contributors (2026). *PrimeNumberTheoremAnd -- Medium prime number theorem*. URL: <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6a380f0c4658c04a420a9eb00b1ed62a1e3fde01>.

*Commentary.*

The integrand is minus the logarithmic derivative of zeta times the Mellin transform of the smoothed indicator times the complex power of X.

**Definition 1.2 (SmoothedChebyshev).**

Lean statement: `D5/S3/Weil/PrimeNumberTheorem/PntSmoothing.SmoothedChebyshev`

*Formalization.* `D5/S3/Weil/PrimeNumberTheorem/PntSmoothing.SmoothedChebyshev` (`✓ std3`).

*Citation.* PrimeNumberTheoremAnd contributors (2026). *PrimeNumberTheoremAnd -- Medium prime number theorem*. URL: <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6a380f0c4658c04a420a9eb00b1ed62a1e3fde01>.

*Commentary.*

The reading is the normalized vertical integral of that integrand on the line with real part 1 plus the reciprocal of log X.

**Theorem 1.3 (SmoothedChebyshevClose).**

Lean statement: `D5/S3/Weil/PrimeNumberTheorem/PntSmoothing.SmoothedChebyshevClose`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeNumberTheorem/PntSmoothing.SmoothedChebyshevClose` (`✓ std3`). ∎

*Citation.* PrimeNumberTheoremAnd contributors (2026). *PrimeNumberTheoremAnd -- Medium prime number theorem*. URL: <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6a380f0c4658c04a420a9eb00b1ed62a1e3fde01>.

*Commentary.*

For a nonnegative once continuously differentiable kernel supported in [1/2, 2] with unit multiplicative Haar mass, one positive constant bounds the smoothing error by C times epsilon times X times log X, whenever X is greater than three, epsilon lies strictly between zero and one, and X times epsilon is greater than two.

## References

- Truth anchor: `D5/S3/Weil/PrimeNumberTheorem/PntSmoothing.SmoothedChebyshev`
- Truth anchor: `D5/S3/Weil/PrimeNumberTheorem/PntSmoothing.SmoothedChebyshevClose`
- Truth anchor: `D5/S3/Weil/PrimeNumberTheorem/PntSmoothing.SmoothedChebyshevIntegrand`
- Dependency: [D5/S3/Weil/PrimeNumberTheorem/Smooth1](Smooth1.md)
- Dependency: [D5/S3/Weil/ZetaPntBase/ZetaConj](../ZetaPntBase/ZetaConj.md)
