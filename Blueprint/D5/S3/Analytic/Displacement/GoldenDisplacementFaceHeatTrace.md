# Golden Displacement Face Heat Trace

## Abstract

The expansion face supplies the golden germ heat trace, with its heat abscissa honestly bracketed in the golden window; the contraction face has no summable heat coefficient.

**Theorem 1.1 (Prime-power face lengths are the golden spectrum).**

$$\forall p \text{prime}, \forall k\in \mathbb{N}, \operatorname{lambdaPlus}(p^{k+1}) = \operatorname{goldenSpectrum}(p, k)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.lambdaPlus_prime_pow_eq_goldenSpectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prime-power hidden-product formula turns the expansion-face closed form into a substitution-start exponent. The conjugate correction is exactly o5Beta, so the resulting logarithmic length is the corresponding golden-spectrum coordinate.

**Theorem 1.2 (Positive germ terms are face heat coefficients).**

$$\forall s\in \mathbb{C}, \forall k\in \mathbb{N}, \operatorname{dTermC}(s, -\psi \cdot s, k+1) = \operatorname{heatCoefficient}(faceLength, s, k)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.dTermC_germ_eq_heatCoefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive natural base, Mathlib's cpow definition rewrites both displacement powers as complex exponentials of real logarithms. The expansion-face closed form combines their exponents into minus s times faceLength k.

**Theorem 1.3 (The face heat trace is the complex germ product).**

$$\forall s\in \mathbb{C}, 1 < \varphi \cdot \operatorname{Re}{s} \Rightarrow \operatorname{heatTrace}(faceLength, s) = \prod_{p \text{prime}}(\sum_{e\in \mathbb{N}}p^{-s \cdot o5Beta{e}})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.heat_trace_eq_complex_displacement_germ_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient identity rewrites the heat trace as the positive-index displacement sum. The zero displacement term vanishes, so the shifted sum is the frozen complex germ section and hence its convergent prime product.

**Theorem 1.4 (Face heat converges above the golden window).**

$$\forall \sigma\in \mathbb{R}, \frac{1}{\varphi} < \sigma \Rightarrow \operatorname{Summable}(k\mapsto e^{-\sigma \operatorname{faceLength}(k)})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.summable_faceLength_heat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Beyond one over phi, the conjugate displacement section lies in the absolute-convergence half-plane. Restricting its summable norm series to positive indices and using the exact coefficient norm gives the face heat series.

**Theorem 1.5 (Face heat diverges below the golden window).**

$$\forall \sigma\in \mathbb{R}, \sigma \leq \frac{1}{\varphi^{2}} \Rightarrow \neg \operatorname{Summable}(k\mapsto e^{-\sigma \operatorname{faceLength}(k)})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.not_summable_faceLength_heat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A summable face series would remain summable on the injectively embedded prime indices. Their exact face lengths reduce the subseries to the prime rpow series with exponent at least minus one, contradicting Mathlib's sharp prime-series criterion, including at the boundary.

**Theorem 1.6 (The face heat abscissa is bracketed in the golden window).**

$$\operatorname{IsHeatAbscissa}(faceLength, \alpha) \Rightarrow \frac{1}{\varphi^{2}} \leq \alpha \leq \frac{1}{\varphi}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.faceLength_heat_abscissa_bracket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prime subfamily forces every abscissa to be at least one over phi squared, while displacement-series convergence forces it to be at most one over phi. This is only a bracket: an exact value would require a local-to-global summability lemma not present in the pinned library.

**Theorem 1.7 (Contraction-face heat is never summable).**

$$\forall s\in \mathbb{C}, \neg \operatorname{Summable}(\operatorname{heatCoefficient}(contractionLength, s))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.not_summable_contraction_face_heat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Along the powers of two, the prime radical is fixed at two. The contraction radical bound therefore keeps every selected length in one bounded interval, giving the heat coefficients a uniform positive norm lower bound and contradicting the zero-term condition for a summable series.

## References

- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.dTermC_germ_eq_heatCoefficient`
- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.faceLength_heat_abscissa_bracket`
- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.heat_trace_eq_complex_displacement_germ_product`
- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.lambdaPlus_prime_pow_eq_goldenSpectrum`
- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.not_summable_contraction_face_heat`
- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.not_summable_faceLength_heat`
- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace.summable_faceLength_heat`
- Dependency: [D5/S1/Deficit/Displacement/GoldenContractionRadicalBound](../../../S1/Deficit/Displacement/GoldenContractionRadicalBound.md)
- Dependency: [D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct](GoldenDisplacementComplexEulerProduct.md)
- Dependency: [D5/S3/Midline/GoldenHeatSpectrum](../../Midline/GoldenHeatSpectrum.md)
