# Unattained Infima of the Golden Displacement Series

## Abstract

Each fixed-w golden series has one as its unattained greatest lower bound.

Fixing the second real parameter still leaves enough convergent values to approach one, while every convergent value remains strictly greater than one. The corresponding conclusions for the full two-parameter family follow as corollaries.

**Theorem 1.1 (Every fixed-parameter slice has greatest lower bound one).**

$$\forall w \in \mathbb{R},\\\operatorname{IsGLB}(\left\{x : \mathbb{R} \mid \exists s \in \mathbb{R}, \operatorname{Summable}(\operatorname{dTerm}(s, w)) \land\\\sum_{n=0}^{\infty} \operatorname{dTerm}(s, w, n) = x\right\}, 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Extrema/GoldenDisplacementSeriesInfimum.golden_displacement_series_slice_isGLB` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each real w, consider exactly the values attained as s varies over parameters for which dTerm(s,w) is summable. One is the greatest lower bound of this slice.

The strict series bound supplies the lower-bound half. For greatestness, take s eventually above max(0,2-w). This ensures both hypotheses of dTerm_summable, and the fixed-w limit theorem makes the resulting series values tend to one.

**Theorem 1.2 (No fixed-parameter slice attains one).**

$$\forall w \in \mathbb{R},\\\neg{1 \in \left\{x : \mathbb{R} \mid \exists s \in \mathbb{R}, \operatorname{Summable}(\operatorname{dTerm}(s, w)) \land\\\sum_{n=0}^{\infty} \operatorname{dTerm}(s, w, n) = x\right\}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Extrema/GoldenDisplacementSeriesInfimum.one_not_mem_golden_displacement_series_slice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real w, one is absent from the corresponding value set. This is the direct strict consequence of every summable golden displacement series having value greater than one.

**Theorem 1.3 (The full value set has greatest lower bound one).**

$$\operatorname{IsGLB}(\left\{x : \mathbb{R} \mid \exists s, w \in \mathbb{R}, \operatorname{Summable}(\operatorname{dTerm}(s, w)) \land\\\sum_{n=0}^{\infty} \operatorname{dTerm}(s, w, n) = x\right\}, 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Extrema/GoldenDisplacementSeriesInfimum.golden_displacement_series_isGLB` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Allowing both real parameters to vary preserves the strict lower bound. Greatestness follows already from the w=0 slice.

**Theorem 1.4 (The full value set does not attain one).**

$$\neg{1 \in \left\{x : \mathbb{R} \mid \exists s, w \in \mathbb{R}, \operatorname{Summable}(\operatorname{dTerm}(s, w)) \land\\\sum_{n=0}^{\infty} \operatorname{dTerm}(s, w, n) = x\right\}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Extrema/GoldenDisplacementSeriesInfimum.one_not_mem_golden_displacement_series_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No summable parameter pair has series value one, so the greatest lower bound of the full two-parameter value set is also unattained.

These declarations do not identify either value set with the open ray above one, prove that every value greater than one occurs, give a convergence rate, or assert bounds outside the summability region.

## References

- Truth anchor: `D5/S3/Analytic/Extrema/GoldenDisplacementSeriesInfimum.golden_displacement_series_isGLB`
- Truth anchor: `D5/S3/Analytic/Extrema/GoldenDisplacementSeriesInfimum.golden_displacement_series_slice_isGLB`
- Truth anchor: `D5/S3/Analytic/Extrema/GoldenDisplacementSeriesInfimum.one_not_mem_golden_displacement_series_slice`
- Truth anchor: `D5/S3/Analytic/Extrema/GoldenDisplacementSeriesInfimum.one_not_mem_golden_displacement_series_values`
- Dependency: [D5/S3/Analytic/Asymptotics/GoldenDisplacementSeriesTendstoOne](../Asymptotics/GoldenDisplacementSeriesTendstoOne.md)
- Dependency: [D5/S3/Analytic/SeriesInequalities/GoldenDisplacementSeriesStrictLowerBound](../SeriesInequalities/GoldenDisplacementSeriesStrictLowerBound.md)
