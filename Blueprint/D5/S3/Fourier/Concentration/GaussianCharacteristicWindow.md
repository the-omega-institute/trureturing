# Closed-Window Bounds from Characteristic Functions

## Abstract

Gaussian smoothing bounds closed-window mass through the characteristic function.

Let μ be a finite measure on the real line and write χ for its characteristic function. For a center b and positive radius r, write M(b,r) for the mass of the closed interval with endpoints b−r and b+r. The Gaussian average G(r) is the integral of exp(−t²)|χ(2t/r)| on the real line.

**Theorem 1.1 (Gaussian smoothing of the closed-window indicator).**

$$\operatorname{sqrt}\left(\pi\right) \cdot \operatorname{M}\left(b, r\right) \le e \cdot \operatorname{G}\left(r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/GaussianCharacteristicWindow.measureReal_closedWindow_le_gaussian_charFun` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inside the window, exp(−((x−b)/r)²) is at least exp(−1). It is positive everywhere. Thus e times this Gaussian majorizes the closed-window indicator, including both endpoints.

The Fourier transform of exp(−t²) at frequency 2(x−b)/r is √π exp(−((x−b)/r)²). The modulus of the product integrand is exp(−t²), which is integrable against Lebesgue measure times μ. Fubini and the definition of χ give an average of χ(2t/r) with the Gaussian weight and the phase from b. Taking the modulus removes the phase and gives the bound.

For k>0, define Q(k,r)=e√π r/(2√k). A reciprocal quadratic envelope means |χ(t)|≤1/(1+kt²) for every real t.

**Theorem 1.2 (A bound linear in the radius).**

$$\operatorname{M}\left(b, r\right) \le \operatorname{Q}\left(k, r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/GaussianCharacteristicWindow.measureReal_closedWindow_le_of_quadratic_charFun` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the envelope, G(r) is at most the integral of 1/(1+(2√k t/r)²), since the Gaussian weight is at most one. The latter integral is π r/(2√k). Dividing the Gaussian mass estimate by √π yields Q(k,r). The reciprocal quadratic estimate requires positive k, and the Gaussian rescaling requires positive r.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/GaussianCharacteristicWindow.measureReal_closedWindow_le_gaussian_charFun`
- Truth anchor: `D5/S3/Fourier/Concentration/GaussianCharacteristicWindow.measureReal_closedWindow_le_of_quadratic_charFun`
