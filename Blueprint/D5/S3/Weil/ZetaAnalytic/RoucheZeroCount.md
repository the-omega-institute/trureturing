# Rouche Zero-Count Stability

## Abstract

A strict boundary perturbation preserves the rectangle zero count with analytic multiplicity.

**Theorem 1.1 (The straight-line homotopy is nonvanishing on the boundary).**

$$\forall f \in \operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right), g \in \operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right), z \in \operatorname{Complex}\left(\right), w \in \operatorname{Complex}\left(\right),\; \left(\forall s \in \operatorname{Complex}\left(\right),\; s \in \operatorname{RectangleBorder}\left(z, w\right) \Rightarrow \left\lVert f\left(s\right) - g\left(s\right) \right\rVert < \left\lVert g\left(s\right) \right\rVert\right) \Rightarrow \left(\forall t \in \operatorname{Real}\left(\right),\; t \in \operatorname{Icc}\left(0, 1\right) \Rightarrow \left(\forall s \in \operatorname{Complex}\left(\right),\; s \in \operatorname{RectangleBorder}\left(z, w\right) \Rightarrow g\left(s\right) + \operatorname{ofReal}\left(t\right) \cdot \left(f\left(s\right) - g\left(s\right)\right) \ne 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaAnalytic/RoucheZeroCount.homotopy_nonvanishing_on_rectangleBorder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strict boundary estimate and the interval bound on the homotopy parameter force the perturbation term to have norm strictly below the base value, so their sum cannot vanish.

**Theorem 1.2 (The normalized logarithmic-derivative contour integral is continuous).**

$$\forall f \in \operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right), g \in \operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right), z \in \operatorname{Complex}\left(\right), w \in \operatorname{Complex}\left(\right),\; \left(\operatorname{re}\left(z\right) < \operatorname{re}\left(w\right) \land \left(\operatorname{im}\left(z\right) < \operatorname{im}\left(w\right) \land \left(\operatorname{AnalyticOnNhd}\left(\operatorname{Complex}\left(\right), f, \operatorname{Rectangle}\left(z, w\right)\right) \land \left(\operatorname{AnalyticOnNhd}\left(\operatorname{Complex}\left(\right), g, \operatorname{Rectangle}\left(z, w\right)\right) \land \left(\forall s \in \operatorname{Complex}\left(\right),\; s \in \operatorname{RectangleBorder}\left(z, w\right) \Rightarrow \left\lVert f\left(s\right) - g\left(s\right) \right\rVert < \left\lVert g\left(s\right) \right\rVert\right)\right)\right)\right)\right) \Rightarrow \operatorname{ContinuousOn}\left((t: \operatorname{Real}\left(\right) \mapsto \operatorname{RectangleIntegral}'\left((s: \operatorname{Complex}\left(\right) \mapsto \operatorname{logDeriv}\left((u: \operatorname{Complex}\left(\right) \mapsto g\left(u\right) + \operatorname{ofReal}\left(t\right) \cdot \left(f\left(u\right) - g\left(u\right)\right)), s\right)), z, w\right)), \operatorname{Icc}\left(0, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaAnalytic/RoucheZeroCount.continuousOn_rectangleIntegral_logDeriv_straightLine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projection to the closed parameter interval extends the boundary integrand continuously. Mathlib's parametric interval-integral continuity theorem applies to each of the four rectangle sides, and the normalized contour combination remains continuous.

**Theorem 1.3 (Rectangle Rouche zero-count stability).**

$$\forall f \in \operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right), g \in \operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right), z \in \operatorname{Complex}\left(\right), w \in \operatorname{Complex}\left(\right), Zf \in \operatorname{Finset}\left(\operatorname{Complex}\left(\right)\right), Zg \in \operatorname{Finset}\left(\operatorname{Complex}\left(\right)\right),\; \left(\left(\operatorname{re}\left(z\right) < \operatorname{re}\left(w\right) \land \left(\operatorname{im}\left(z\right) < \operatorname{im}\left(w\right) \land \left(\operatorname{AnalyticOnNhd}\left(\operatorname{Complex}\left(\right), f, \operatorname{Rectangle}\left(z, w\right)\right) \land \left(\operatorname{AnalyticOnNhd}\left(\operatorname{Complex}\left(\right), g, \operatorname{Rectangle}\left(z, w\right)\right) \land \left(\forall s \in \operatorname{Complex}\left(\right),\; s \in \operatorname{RectangleBorder}\left(z, w\right) \Rightarrow \left\lVert f\left(s\right) - g\left(s\right) \right\rVert < \left\lVert g\left(s\right) \right\rVert\right)\right)\right)\right)\right) \land \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; s \in \operatorname{Rectangle}\left(z, w\right) \Rightarrow \left(f\left(s\right) = 0 \Leftrightarrow s \in Zf\right)\right) \land \left(\operatorname{toSet}\left(Zf\right) \subseteq \operatorname{Rectangle}\left(z, w\right) \land \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; s \in \operatorname{Rectangle}\left(z, w\right) \Rightarrow \left(g\left(s\right) = 0 \Leftrightarrow s \in Zg\right)\right) \land \operatorname{toSet}\left(Zg\right) \subseteq \operatorname{Rectangle}\left(z, w\right)\right)\right)\right)\right) \Rightarrow \sum_{rho \in Zf} \operatorname{analyticOrderNatAt}\left(f, rho\right) = \sum_{rho \in Zg} \operatorname{analyticOrderNatAt}\left(g, rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaAnalytic/RoucheZeroCount.rectangle_zero_count_eq_of_norm_sub_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Boundary nonvanishing and contour-integral continuity put the normalized logarithmic-derivative integral in the discrete range of integer casts throughout the connected parameter interval. It is therefore constant, and the rectangle argument principle identifies its two endpoint values with the stated multiplicity sums.

## References

- Truth anchor: `D5/S3/Weil/ZetaAnalytic/RoucheZeroCount.continuousOn_rectangleIntegral_logDeriv_straightLine`
- Truth anchor: `D5/S3/Weil/ZetaAnalytic/RoucheZeroCount.homotopy_nonvanishing_on_rectangleBorder`
- Truth anchor: `D5/S3/Weil/ZetaAnalytic/RoucheZeroCount.rectangle_zero_count_eq_of_norm_sub_lt`
