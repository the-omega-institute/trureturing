# Riemann Zeta Derivative at Negative Two

## Abstract

The derivative of the Riemann zeta function at negative two is determined by its value at three.

**Theorem 1.1 (The zeta derivative at negative two).**

$$\zeta'(-2) = -\frac{\zeta(3)}{4 \cdot \pi^2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/RiemannZetaDerivativeNegativeTwo.riemann_zeta_derivative_negative_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiate the Riemann zeta functional equation at s = 3. The cosine factor vanishes there, so the derivatives of the amplitude and of zeta(s) contribute zero; only the derivative of the cosine remains.

Using Gamma(3) = 2 and the derivative of cos(pi s/2) at s = 3 gives the coefficient 1/(4 pi squared). The derivative of zeta(1-s) supplies the opposite sign, yielding the displayed identity.

This declaration isolates the analytic identity that supports the source's logarithmic-curvature coefficient. The full four-term asymptotic is not stated because its S, c1, and c2 are not formally defined. Nor is the pointwise formula 1/zeta(1) = 0 asserted: in Mathlib the pole is represented by a finite junk value, while the valid cancellation statement is asymptotic.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/RiemannZetaDerivativeNegativeTwo.riemann_zeta_derivative_negative_two`
