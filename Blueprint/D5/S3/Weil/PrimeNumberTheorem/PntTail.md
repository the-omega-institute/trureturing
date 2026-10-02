# PntTail

## Abstract

The smoothed Chebyshev contour has controlled vertical and horizontal tails.

**Theorem 1.1 (I1Bound).**

Lean statement: `D5/S3/Weil/PrimeNumberTheorem/PntTail.I1Bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeNumberTheorem/PntTail.I1Bound` (`✓ std3`). ∎

*Citation.* PrimeNumberTheoremAnd contributors (2026). *PrimeNumberTheoremAnd -- Medium prime number theorem*. URL: <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6a380f0c4658c04a420a9eb00b1ed62a1e3fde01>.

*Commentary.*

For a nonnegative once continuously differentiable kernel supported in [1/2, 2] with unit multiplicative Haar mass, one positive constant bounds the first vertical tail by C times X times log X divided by epsilon times T, whenever X and T are greater than three and epsilon lies strictly between zero and one.

**Theorem 1.2 (I2Bound).**

Lean statement: `D5/S3/Weil/PrimeNumberTheorem/PntTail.I2Bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeNumberTheorem/PntTail.I2Bound` (`✓ std3`). ∎

*Citation.* PrimeNumberTheoremAnd contributors (2026). *PrimeNumberTheoremAnd -- Medium prime number theorem*. URL: <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6a380f0c4658c04a420a9eb00b1ed62a1e3fde01>.

*Commentary.*

Let the kernel be once continuously differentiable and supported in [1/2, 2]. Assume 0 < A <= 1/2 and C2 > 0, and for every real sigma and t with |t| > 3 and sigma >= 1 - A/(log |t|)^9 assume |zeta'(sigma + it)/zeta(sigma + it)| <= C2 (log |t|)^9. Then one C > 0 bounds the norm of I2 by C X/(epsilon T) for all X > 3, T > 3 and 0 < epsilon < 1, with sigma1 = 1 - A/(log T)^9.

I1. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I1 is i/(2 pi i) times the integral of G(1 + 1/log X + it) over t <= -T.

I2. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I2 is 1/(2 pi i) times the oriented integral of G(sigma - iT) from sigma1 to 1 + 1/log X.

I37. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I37 is i/(2 pi i) times the oriented integral of G(sigma1 + it) from t = -T to t = T.

I8. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I8 is 1/(2 pi i) times the oriented integral of G(sigma + iT) from sigma1 to 1 + 1/log X.

I9. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I9 is i/(2 pi i) times the integral of G(1 + 1/log X + it) over t >= T.

I3. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I3 is i/(2 pi i) times the oriented integral of G(sigma1 + it) from t = -T to t = -3.

I7. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I7 is i/(2 pi i) times the oriented integral of G(sigma1 + it) from t = 3 to t = T.

I4. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I4 is 1/(2 pi i) times the oriented integral of G(sigma - 3i) from sigma2 to sigma1.

I6. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I6 is 1/(2 pi i) times the oriented integral of G(sigma + 3i) from sigma2 to sigma1.

I5. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I5 is i/(2 pi i) times the oriented integral of G(sigma2 + it) from t = -3 to t = 3.

**Definition 1.3 (LogDerivZetaHasBound).**

Lean statement: `D5/S3/Weil/PrimeNumberTheorem/PntTail.LogDerivZetaHasBound`

*Formalization.* `D5/S3/Weil/PrimeNumberTheorem/PntTail.LogDerivZetaHasBound` (`✓ std3`).

*Citation.* PrimeNumberTheoremAnd contributors (2026). *PrimeNumberTheoremAnd -- Medium prime number theorem*. URL: <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6a380f0c4658c04a420a9eb00b1ed62a1e3fde01>.

*Commentary.*

For every real sigma and t with |t| > 3 and sigma >= 1 - A/(log |t|)^9, the predicate requires |zeta'(sigma + it)/zeta(sigma + it)| <= C (log |t|)^9. The real coordinate sigma has no upper bound.

**Definition 1.4 (LogDerivZetaIsHoloSmall).**

Lean statement: `D5/S3/Weil/PrimeNumberTheorem/PntTail.LogDerivZetaIsHoloSmall`

*Formalization.* `D5/S3/Weil/PrimeNumberTheorem/PntTail.LogDerivZetaIsHoloSmall` (`✓ std3`).

*Citation.* PrimeNumberTheoremAnd contributors (2026). *PrimeNumberTheoremAnd -- Medium prime number theorem*. URL: <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/6a380f0c4658c04a420a9eb00b1ed62a1e3fde01>.

*Commentary.*

The predicate requires the zeta logarithmic derivative to be holomorphic on the small punctured rectangle with imaginary coordinate between minus three and three.

## References

- Truth anchor: `D5/S3/Weil/PrimeNumberTheorem/PntTail.I1Bound`
- Truth anchor: `D5/S3/Weil/PrimeNumberTheorem/PntTail.I2Bound`
- Truth anchor: `D5/S3/Weil/PrimeNumberTheorem/PntTail.LogDerivZetaHasBound`
- Truth anchor: `D5/S3/Weil/PrimeNumberTheorem/PntTail.LogDerivZetaIsHoloSmall`
- Dependency: [D5/S3/Weil/PrimeNumberTheorem/PntSmoothing](PntSmoothing.md)
