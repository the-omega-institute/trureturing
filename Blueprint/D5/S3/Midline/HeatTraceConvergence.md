# Ordinary Heat-Coefficient Convergence

## Abstract

Boundary-divergent heat abscissas give exact ordinary complex summability thresholds, with golden and prime-axis specializations.

**Theorem 1.1 (Boundary divergence gives the ordinary summability threshold).**

$$\operatorname{BoundaryDivergentAbscissa}(M, \alpha) \Rightarrow [\operatorname{Summable}(\operatorname{heatCoefficient}(M, s)) \Leftrightarrow \alpha < \Re(s)].$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/HeatTraceConvergence.heat_coefficient_summable_iff_of_boundary_divergent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Norm summability reduces ordinary complex summability to the real heat series. The two strict abscissa clauses and boundary divergence then give the exact right-half-plane criterion.

**Theorem 1.2 (Golden heat coefficients have the golden-abscissa threshold).**

$$\forall s: \mathbb{C}, \operatorname{Summable}(\operatorname{heatCoefficient}(goldenSpectrum, s)) \Leftrightarrow \frac{1}{\varphi^{2}} < \Re(s).$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/HeatTraceConvergence.golden_heat_coefficient_summable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The universal criterion specializes at the boundary-divergent golden heat abscissa one over phi squared.

**Theorem 1.3 (Prime-axis heat coefficients have threshold one).**

$$\forall s: \mathbb{C}, \operatorname{Summable}(\operatorname{heatCoefficient}(primeAxisLogLength, s)) \Leftrightarrow 1 < \Re(s).$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/HeatTraceConvergence.prime_axis_heat_coefficient_summable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same criterion specializes at the boundary-divergent prime-axis logarithmic abscissa one.

## References

- Truth anchor: `D5/S3/Midline/HeatTraceConvergence.golden_heat_coefficient_summable_iff`
- Truth anchor: `D5/S3/Midline/HeatTraceConvergence.heat_coefficient_summable_iff_of_boundary_divergent`
- Truth anchor: `D5/S3/Midline/HeatTraceConvergence.prime_axis_heat_coefficient_summable_iff`
- Dependency: [D5/S3/Midline/ZetaHeatTraceBridge](ZetaHeatTraceBridge.md)
