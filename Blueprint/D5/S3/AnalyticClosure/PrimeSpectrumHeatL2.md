# Quantitative Prime-Spectrum Heat Bounds

## Abstract

Linear prime-spectrum growth gives an explicit geometric heat-trace bound and a quantitative L2 norm estimate.

**Definition 1.1 (The logarithmic prime spectrum).**

$$\forall beta: \mathbb{N}\to\mathbb{R}, \forall pk: (\operatorname{Nat.Primes}\times \mathbb{N}), \operatorname{primeSpectrum}(beta)(pk)=beta(pk_{2}+1)\times \log(pk_{1})$$

*Formalization.* `D5/S3/AnalyticClosure/PrimeSpectrumHeatL2.primeSpectrum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The length indexed by a prime p and a natural layer k is beta(k+1) log p.

**Theorem 1.2 (An explicit geometric heat-trace bound).**

$$\forall beta: \mathbb{N}\to\mathbb{R}, \forall b0: \mathbb{R}, 0<b0\Rightarrow (\forall k: \mathbb{N}, b0+k\leq beta(k+1))\Rightarrow\forall sigma: \mathbb{R}, \frac{1}{b0}<sigma\Rightarrow \sum_{pk\in(\operatorname{Nat.Primes}\times \mathbb{N})}\operatorname{exp}(-sigma\times \operatorname{primeSpectrum}(beta)(pk))\leq \frac{\sum_{p\in\operatorname{Nat.Primes}}p^{-sigma\times b0}}{1-2^{-sigma}}$$

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/PrimeSpectrumHeatL2.prime_spectrum_heat_trace_geometric_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume b0>0 and beta(k+1)>=b0+k. For sigma>1/b0, every prime p>=2 gives a geometric majorant in k. Summing that majorant bounds the real heat trace by the convergent prime series divided by 1-2^(-sigma); beta(1) need not equal b0.

**Theorem 1.3 (The exact square-summability domain).**

$$\forall beta: \mathbb{N}\to\mathbb{R}, \forall b0: \mathbb{R}, beta(1)=b0\Rightarrow 0<b0\Rightarrow (\forall k: \mathbb{N}, b0+k\leq beta(k+1))\Rightarrow\forall s: \mathbb{C}, \operatorname{MemLp}(\operatorname{heatCoefficient}(\operatorname{primeSpectrum}(beta), s), 2)\Leftrightarrow \frac{1}{2\times b0}<\operatorname{Re}(s)$$

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/PrimeSpectrumHeatL2.prime_spectrum_heat_l2_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing boundary-divergent heat abscissa gives the exact L2 half-plane. This auxiliary result supplies the coefficient vector used in the norm bound.

**Theorem 1.4 (A quantitative coefficient norm bound).**

$$\forall beta: \mathbb{N}\to\mathbb{R}, \forall b0: \mathbb{R}, beta(1)=b0\Rightarrow 0<b0\Rightarrow (\forall k: \mathbb{N}, b0+k\leq beta(k+1))\Rightarrow\forall sigma: \mathbb{R}, \forall t: \mathbb{R}, \frac{1}{2\times b0}<sigma\Rightarrow \operatorname{let} x:\operatorname{lp}((\operatorname{Nat.Primes}\times \mathbb{N}), \mathbb{C}, 2)=\operatorname{heatCoefficient}(\operatorname{primeSpectrum}(beta), sigma+i\times t); \left\lVert x \right\rVert^{2}\leq \frac{\sum_{p\in\operatorname{Nat.Primes}}p^{-(2\times sigma)\times b0}}{1-2^{-(2\times sigma)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/PrimeSpectrumHeatL2.prime_spectrum_heat_l2_norm_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For sigma>1/(2 b0), square summability defines the lp coefficient vector. Its coordinate norm squares are the real heat terms at 2 sigma, so the geometric trace estimate bounds its squared norm uniformly over every imaginary coordinate t.

## References

- Truth anchor: `D5/S3/AnalyticClosure/PrimeSpectrumHeatL2.primeSpectrum`
- Truth anchor: `D5/S3/AnalyticClosure/PrimeSpectrumHeatL2.prime_spectrum_heat_l2_iff`
- Truth anchor: `D5/S3/AnalyticClosure/PrimeSpectrumHeatL2.prime_spectrum_heat_l2_norm_bound`
- Truth anchor: `D5/S3/AnalyticClosure/PrimeSpectrumHeatL2.prime_spectrum_heat_trace_geometric_bound`
