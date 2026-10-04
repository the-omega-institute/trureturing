# Gaussian Polynomial Totality

## Abstract

Gaussian-polynomial tests determine a complex Lebesgue square-integrable function.

**Theorem 1.1 (Every positive Gaussian width gives a total polynomial test family).**

$$\forall b \in \mathbb{R}, g \in \mathbb{R} \to \mathbb{C},\; (0 < b \land \operatorname{MemLp}\left(g, 2, \mathrm{volume}\right) \land \forall q \in \mathbb{R}[X],\; \int_{x: \mathbb{R}} q\left(x\right) \cdot \exp(-\frac{b \cdot x^{2}}{2}) \cdot g\left(x\right) dx = 0) \Rightarrow \forall q \in \mathbb{R}[X],\; \operatorname{Integrable}\left((x: \mathbb{R} \mapsto q\left(x\right) \cdot \exp(-\frac{b \cdot x^{2}}{2}) \cdot g\left(x\right)), \mathrm{volume}\right) \land g =_{\operatorname{ae}, dx} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/Hermite/GaussianPolynomialTotality.gaussian_polynomial_totality` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Rémy Degenne (2026). *Gaussian-polynomial totality through exponential-moment determinacy*. URL: <https://github.com/TauCetiProject/TauCeti/tree/f749c1bb6b118c898f8d152e8ff9ad3d2b339dfd>.

*Commentary.*

Let b be strictly positive and let g be a complex square-integrable function on the real line with Lebesgue volume. If the integral of q(x) exp(-b x squared / 2) g(x) vanishes for every real polynomial q, then every such pairing is integrable and g vanishes almost everywhere.

No exponential decay is assumed for g. Gaussian domination and Cauchy-Schwarz give an exponential moment for the weighted function. Its vanishing monomial moments identify its positive and negative density measures through their analytic moment-generating functions. The argument applies to the real and imaginary parts.

For positive physical parameters hbar, mass and frequency, the width b equals mass times frequency divided by hbar. Normalized Hermite functions, product spaces and differential operator domains require their own correspondence statements.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/Hermite/GaussianPolynomialTotality.gaussian_polynomial_totality`
