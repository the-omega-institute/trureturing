# Golden Displacement Series Log-Convexity

## Abstract

The logarithm of the golden displacement sum is convex on its exact convergence region.

**Theorem 1.1 (The displacement sum is log-convex on its convergence region).**

$$\operatorname{ConvexOn}(\mathbb{R}, \left\{p : \mathbb{R} \times \mathbb{R} \mid \operatorname{Summable}(\operatorname{dTerm}(p.1, p.2))\right\}, p : \mathbb{R} \times \mathbb{R} \mapsto \log(\sum_{n=0}^{\infty} \operatorname{dTerm}(p.1, p.2, n)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/GoldenDisplacementSeriesLogConvexity.golden_displacement_series_log_convex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public theorem uses the standard ConvexOn formulation: the domain is exactly the set of parameter pairs for which dTerm is summable, and the function is the real logarithm of the corresponding sum.

For positive weights a and b with a+b=1, each mixed dTerm is exactly the product of the endpoint dTerms raised to a and b. At index zero, both positive real powers vanish. At a positive index, n and nS(n) are positive, so Real.mul_rpow, Real.rpow_mul, and Real.rpow_add combine the two endpoint factors without an inequality.

The public countable weighted Holder interpolation theorem bounds the mixed sum by the product of the endpoint sums raised to a and b. Its nonnegativity hypotheses come from dTerm_nonneg, and its endpoint summability hypotheses come from the two parameter pairs lying in the convergence region, since dTerm is not summable for arbitrary parameters. This node is the first consumer of the extracted general series inequality.

The frozen convexity theorem keeps the mixed parameter pair inside the exact summability region. Every convergent displacement sum is positive because all terms are nonnegative and the term at index one is one. Monotonicity of the real logarithm and its product and real-power identities therefore turn the Holder bound into the weighted additive inequality required by ConvexOn.

The theorem does not claim strict log-convexity, an equality characterization, antitonicity in either parameter, convexity of the unlogged sum, convergence or a finite value on the boundary, or any extension outside the exact summability region.

## References

- Truth anchor: `D5/S3/Analytic/Convexity/GoldenDisplacementSeriesLogConvexity.golden_displacement_series_log_convex`
- Dependency: [D5/S3/Analytic/SeriesInequalities/CountableWeightedHolderInterpolation](../SeriesInequalities/CountableWeightedHolderInterpolation.md)
