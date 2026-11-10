# Critical Endpoint of the Prime Heat Curve

## Abstract

The actual prime heat trace diverges at its critical endpoint, and normalization gives an infinite-variation Hilbert curve.

**Definition 1.1 (The actual square-summable prime heat vector).**

$$\forall beta: \mathbb{N}\to \mathbb{R}, \forall b0: \mathbb{R}, 0<b0\Rightarrow \operatorname{beta}(1)=b0\Rightarrow (\forall k: \mathbb{N}, b0+k\leq \operatorname{beta}(k+1))\Rightarrow \forall sigma: \mathbb{R}, \operatorname{primeHeatVector}(beta, b0, sigma)=\operatorname{if}(\frac{1}{b0}<sigma, \operatorname{heatCoefficient}(\operatorname{primeSpectrum}(beta), \frac{sigma}{2}), 0)$$

*Formalization.* `D5/S3/AnalyticClosure/PrimeSpectrumBoundaryEscape.primeHeatVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under the prime-spectrum hypotheses, x(sigma) has coordinates exp(-(sigma/2) beta(k+1) log p) for sigma>alpha=1/b0. It is an element of the actual lp space over Nat.Primes times Nat; its value outside that open domain is the zero vector. No artificial zero spectral index is added.

**Theorem 1.2 (Heat-trace divergence from the right).**

$$\forall beta: \mathbb{N}\to \mathbb{R}, \forall b0: \mathbb{R}, 0<b0\Rightarrow \operatorname{beta}(1)=b0\Rightarrow (\forall k: \mathbb{N}, b0+k\leq \operatorname{beta}(k+1))\Rightarrow \operatorname{Tendsto}((sigma \mapsto \sum_{a\in(\operatorname{Nat.Primes}\times \mathbb{N})}\operatorname{exp}(-sigma\times \operatorname{primeSpectrum}(beta, a))), \operatorname{nhdsRight}(\frac{1}{b0}), \operatorname{atTop}())$$

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/PrimeSpectrumBoundaryEscape.prime_spectrum_heat_trace_tendsto_atTop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The boundary prime-reciprocal layer is not summable. Consequently its nonnegative finite partial sums are unbounded. Each such finite heat sum is continuous in sigma, and right-side summability bounds it by the actual heat trace. Thus the real heat trace tends to positive infinity from the right. The total tsum at the divergent endpoint is not interpreted as an infinite real value.

**Theorem 1.3 (Divergence of the actual Hilbert norm).**

$$\forall beta: \mathbb{N}\to \mathbb{R}, \forall b0: \mathbb{R}, 0<b0\Rightarrow \operatorname{beta}(1)=b0\Rightarrow (\forall k: \mathbb{N}, b0+k\leq \operatorname{beta}(k+1))\Rightarrow \operatorname{Tendsto}((sigma \mapsto \left\lVert \operatorname{primeHeatVector}(beta, b0, sigma) \right\rVert), \operatorname{nhdsRight}(\frac{1}{b0}), \operatorname{atTop}())$$

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/PrimeSpectrumBoundaryEscape.prime_spectrum_heat_norm_tendsto_atTop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The squared lp norm equals the real heat trace at sigma. The norm therefore tends to positive infinity at alpha from the right.

**Theorem 1.4 (No strong endpoint limit).**

$$\forall beta: \mathbb{N}\to \mathbb{R}, \forall b0: \mathbb{R}, 0<b0\Rightarrow \operatorname{beta}(1)=b0\Rightarrow (\forall k: \mathbb{N}, b0+k\leq \operatorname{beta}(k+1))\Rightarrow \forall x: \operatorname{lp}((\operatorname{Nat.Primes}\times \mathbb{N}), \mathbb{C}, 2), \neg \operatorname{Tendsto}((sigma \mapsto \operatorname{normalize}(\operatorname{primeHeatVector}(beta, b0, sigma))), \operatorname{nhdsRight}(\frac{1}{b0}), \operatorname{nhds}(x))$$

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/PrimeSpectrumBoundaryEscape.prime_spectrum_normalized_heat_not_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every fixed coordinate of the normalized vector tends to zero, since its unnormalized coefficient has a finite endpoint value and its norm diverges. The actual vector is nonzero, so normalization has norm one. Any strong lp limit would have every coordinate zero, contradicting convergence of norms to one.

**Theorem 1.5 (Infinite metric variation at the critical endpoint).**

$$\forall beta: \mathbb{N}\to \mathbb{R}, \forall b0: \mathbb{R}, 0<b0\Rightarrow \operatorname{beta}(1)=b0\Rightarrow (\forall k: \mathbb{N}, b0+k\leq \operatorname{beta}(k+1))\Rightarrow \forall c: \mathbb{R}, \frac{1}{b0}<c\Rightarrow \operatorname{eVariationOn}((sigma \mapsto \operatorname{normalize}(\operatorname{primeHeatVector}(beta, b0, sigma))), \operatorname{Ioo}(\frac{1}{b0}, c))=\infty$$

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/PrimeSpectrumBoundaryEscape.prime_spectrum_normalized_heat_eVariationOn_eq_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every c>alpha the normalized Hilbert curve has infinite total metric variation on (alpha,c). Finite variation would give a strong right limit in the complete lp space, contradicting the preceding theorem. This establishes metric length of the actual curve; no Fisher-information derivative identity, Riemannian metric identification, global manifold completeness, or RH conclusion is asserted.

## References

- Truth anchor: `D5/S3/AnalyticClosure/PrimeSpectrumBoundaryEscape.primeHeatVector`
- Truth anchor: `D5/S3/AnalyticClosure/PrimeSpectrumBoundaryEscape.prime_spectrum_heat_norm_tendsto_atTop`
- Truth anchor: `D5/S3/AnalyticClosure/PrimeSpectrumBoundaryEscape.prime_spectrum_heat_trace_tendsto_atTop`
- Truth anchor: `D5/S3/AnalyticClosure/PrimeSpectrumBoundaryEscape.prime_spectrum_normalized_heat_eVariationOn_eq_top`
- Truth anchor: `D5/S3/AnalyticClosure/PrimeSpectrumBoundaryEscape.prime_spectrum_normalized_heat_not_tendsto`
- Dependency: [D5/S3/AnalyticClosure/PrimeSpectrumHeatL2](PrimeSpectrumHeatL2.md)
