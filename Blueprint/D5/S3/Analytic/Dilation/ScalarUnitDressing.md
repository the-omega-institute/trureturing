# Scalar Unit Dressing

## Abstract

A nonvanishing analytic scalar dressing preserves zeros and their multiplicities.

**Theorem 1.1 (A scalar unit does not move a zero).**

$$\forall f \in \mathbb{C} \to \mathbb{C}, g \in \mathbb{C} \to \mathbb{C}, s \in \mathbb{C},\; \left(\operatorname{AnalyticAt}\left(\mathbb{C}, f, s\right) \land \left(\operatorname{AnalyticAt}\left(\mathbb{C}, g, s\right) \land \left(\neg g\left(s\right) = 0\right)\right)\right) \Rightarrow \left(\left(g\left(s\right) \cdot f\left(s\right) = 0 \Leftrightarrow f\left(s\right) = 0\right) \land \operatorname{analyticOrderAt}\left(g \cdot f, s\right) = \operatorname{analyticOrderAt}\left(f, s\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Dilation/ScalarUnitDressing.nonzero_scalar_dressing_preserves_zero_and_analytic_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f and g be complex-valued functions analytic at s, with g(s) nonzero. Then multiplying f by g neither creates nor removes a zero at s, and the analytic order at s is unchanged.

The nonvanishing assumption is the scalar-unit hypothesis. Analyticity of both factors is stated explicitly because pointwise nonvanishing alone does not define or preserve analytic zero order.

The proof uses Mathlib's zero-product criterion and additive formula for analytic orders. The order of g is zero because it is analytic and nonzero at the chosen point.

## References

- Truth anchor: `D5/S3/Analytic/Dilation/ScalarUnitDressing.nonzero_scalar_dressing_preserves_zero_and_analytic_order`
