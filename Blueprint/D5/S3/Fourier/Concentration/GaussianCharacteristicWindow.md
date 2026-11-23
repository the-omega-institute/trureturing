# Closed-Window Bounds from Characteristic Functions

## Abstract

Gaussian smoothing bounds closed-window mass through the characteristic function.

Let μ be a finite measure on the real line and write χ for its characteristic function. Write M(b,r) for the measure of |x−b|≤r. At any smoothing scale s>0, let G(b,s) be the integral of exp(−t²)exp(−2itb/s)χ(2t/s) on the real line. Write A(s) for the integral of exp(−t²)|χ(2t/s)|.

**Theorem 1.1 (Gaussian smoothing of the closed-window indicator).**

$$\operatorname{sqrt}\left(\pi\right) \cdot \operatorname{M}\left(b, r\right) \le \operatorname{exp}\left(\frac{r}{s}^{2}\right) \cdot \left|\operatorname{G}\left(b, s\right)\right| \land \left|\operatorname{G}\left(b, s\right)\right| \le \operatorname{A}\left(s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/GaussianCharacteristicWindow.measureReal_closedWindow_le_gaussian_charFun` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inside the window, exp(−((x−b)/s)²) is at least exp(−(r/s)²). The Gaussian is positive everywhere. Multiplying by exp((r/s)²) majorizes the closed-window indicator, including both endpoints.

With the factor exp(itξ), the Gaussian transform at ξ=2(x−b)/s is √π exp(−((x−b)/s)²). The modulus of the product integrand is exp(−t²), which is integrable against Lebesgue measure times μ. Fubini and the definition of χ give the phase-sensitive integral G(b,s). The triangle inequality bounds its modulus by A(s). The first inequality is an equality for a unit atom on the boundary |x−b|=r.

For k>0 and r>0, define Q(k,r)=exp(1/2)√π r/(√2√k). A reciprocal quadratic envelope means |χ(t)|≤1/(1+kt²) for every real t.

**Theorem 1.2 (A bound linear in the radius).**

$$\operatorname{M}\left(b, r\right) \le \operatorname{Q}\left(k, r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/GaussianCharacteristicWindow.measureReal_closedWindow_le_of_quadratic_charFun` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the envelope, A(s) is at most the integral of 1/(1+(2√k t/s)²), since the Gaussian weight is at most one. The latter integral is π s/(2√k). Choose s=√2 r. Then the indicator multiplier is exp(1/2), and dividing the mass estimate by √π yields Q(k,r).

## References

- Truth anchor: `D5/S3/Fourier/Concentration/GaussianCharacteristicWindow.measureReal_closedWindow_le_gaussian_charFun`
- Truth anchor: `D5/S3/Fourier/Concentration/GaussianCharacteristicWindow.measureReal_closedWindow_le_of_quadratic_charFun`
