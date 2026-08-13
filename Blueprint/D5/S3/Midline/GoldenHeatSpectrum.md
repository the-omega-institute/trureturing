# The Golden Heat Spectrum and Its L2 Midline

## Abstract

The excited golden Euler spectrum has heat abscissa one over phi squared and strict L2 threshold one over twice phi squared.

**Theorem 1.1 (The golden spectrum has abscissa one over phi squared).**

$$\operatorname{IsHeatAbscissa}(goldenSpectrum, \frac{1}{\varphi^{2}}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/GoldenHeatSpectrum.golden_heat_abscissa` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The golden Euler spectrum has convergence strictly to the right of its heat abscissa and divergence strictly to the left; no boundary behavior is asserted.

**Theorem 1.2 (The golden heat coefficient is L2 right of the midline).**

$$\forall s: \mathbb{C}, \frac{1}{2\times\varphi^{2}} < \Re(s) \Rightarrow \operatorname{MemLp}(\operatorname{heatCoefficient}(goldenSpectrum, s), 2).$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/GoldenHeatSpectrum.golden_heat_l2_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Above the strict half-abscissa threshold, the universal heat-trace result gives L2 membership for the golden heat coefficient.

**Theorem 1.3 (The golden heat coefficient is not L2 left of the midline).**

$$\forall s: \mathbb{C}, \Re(s) < \frac{1}{2\times\varphi^{2}} \Rightarrow \neg\operatorname{MemLp}(\operatorname{heatCoefficient}(goldenSpectrum, s), 2).$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/GoldenHeatSpectrum.golden_heat_l2_not_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Below the strict half-abscissa threshold, the universal heat-trace result excludes L2 membership for the golden heat coefficient.

## References

- Truth anchor: `D5/S3/Midline/GoldenHeatSpectrum.golden_heat_abscissa`
- Truth anchor: `D5/S3/Midline/GoldenHeatSpectrum.golden_heat_l2_mem`
- Truth anchor: `D5/S3/Midline/GoldenHeatSpectrum.golden_heat_l2_not_mem`
- Dependency: [D5/S3/Midline/UniversalHeatTrace](UniversalHeatTrace.md)
