# Visible Gaussian Mass

## Abstract

The odd-double-factorial power series is the visible Gaussian mass below its natural square-root scale.

**Theorem 1.1 (The visible mass has a Gaussian integral form).**

$$\forall x \in \mathbb{R},\\0 < x \Rightarrow \sum_{n=0}^{\infty} \frac{x^{n}}{{2n+1}!!} = \frac{\exp{\frac{x}{2}}}{\sqrt{x}} \cdot \int_{0}^{\sqrt{x}} \exp{\frac{-t^{2}}{2}}\,dt.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/VisibleGaussianMass.visible_gaussian_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real x, the power series with coefficient 1/(2n+1)!! equals exp(x/2)/sqrt(x) times the Gaussian integral from zero to sqrt(x).

The proof differentiates u(1-u^2)^(n+1) to obtain the beta-integral coefficient recurrence, solves that recurrence using Mathlib's double factorial identities, and exchanges the exponential series with the interval integral by dominated convergence.

The final substitution t=sqrt(x)u gives the displayed scale factor. The positivity premise keeps the displayed quotient away from its removable singularity at x=0. The later tail completion and continued-fraction discussion are outside the named theorem.

## References

- Truth anchor: `D5/S3/Analytic/Characterizations/VisibleGaussianMass.visible_gaussian_mass`
