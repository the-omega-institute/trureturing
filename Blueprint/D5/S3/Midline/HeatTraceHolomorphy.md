# Heat-Trace Holomorphy

## Abstract

A heat trace is analytic throughout the open half-plane to the right of its heat abscissa.

**Theorem 1.1 (The heat trace is analytic on its convergence half-plane).**

$$\operatorname{IsHeatAbscissa}(M, \alpha) \land (\forall a, 0 \le M(a)) \Rightarrow \operatorname{AnalyticOnNhd}_{\mathbb{C}}(\operatorname{heatTrace}(M), \{s\in \mathbb{C}\mid \alpha < \Re(s)\}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/HeatTraceHolomorphy.heat_trace_analyticOnNhd_of_abscissa` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each point in the convergence half-plane, choose a strictly intermediate real abscissa. The heat-abscissa hypothesis supplies a summable exponential majorant on that smaller right half-plane, so the Weierstrass M-test gives differentiability there and hence analyticity at the chosen point.

## References

- Truth anchor: `D5/S3/Midline/HeatTraceHolomorphy.heat_trace_analyticOnNhd_of_abscissa`
- Dependency: [D5/S3/Midline/UniversalHeatTrace](UniversalHeatTrace.md)
