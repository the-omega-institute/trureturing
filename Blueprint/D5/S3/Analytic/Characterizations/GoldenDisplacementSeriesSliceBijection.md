# Fixed-Parameter Golden Displacement Slice Bijection

## Abstract

Every fixed-second-parameter golden displacement slice is classified by an exact summability ray and a bijection onto the open ray above one.

For a fixed real w, both affine convergence constraints can be solved for s. Their intersection is the open ray strictly above the larger boundary. On this exact domain, increasing s strictly lowers the series value.

**Theorem 1.1 (The fixed-w summability domain is an open ray).**

$$\forall s, w \in \mathbb{R},\\\operatorname{Summable}(\operatorname{dTerm}(s, w)) \Leftrightarrow \operatorname{max}(\frac{1-w}{2}, \frac{1-2w}{3}) < s.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/GoldenDisplacementSeriesSliceBijection.golden_displacement_slice_summable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real s and w, dTerm(s,w) is summable exactly when s is strictly greater than both (1-w)/2 and (1-2w)/3, equivalently strictly greater than their maximum.

**Theorem 1.2 (Each fixed-w slice bijects with the open ray above one).**

$$\forall w \in \mathbb{R},\\\operatorname{BijOn}((s \mapsto \sum_{n=0}^{\infty} \operatorname{dTerm}(s, w, n)), \left\{s \in \mathbb{R} \mid \operatorname{Summable}(\operatorname{dTerm}(s, w))\right\}, \operatorname{Ioi}(1)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/GoldenDisplacementSeriesSliceBijection.golden_displacement_series_slice_bijOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real w, restrict the map sending s to the infinite sum of dTerm(s,w) to exactly those s for which the series is summable. This restricted map is a bijection onto the real values strictly greater than one.

At the excluded lower boundary, nonnegative partial sums tend to positive infinity. Continuity of a finite partial sum therefore gives a nearby convergent full sum strictly above any target greater than one. Farther along the ray, the full sum tends down to one and is strictly below the target. Continuity attains the target between those points, and strict antitonicity makes that point unique.

The codomain excludes the boundary value one, while the summability theorem above shows that the lower parameter boundary is not summable. The bijection gives neither an inverse formula nor quantitative convergence rates.

## References

- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenDisplacementSeriesSliceBijection.golden_displacement_series_slice_bijOn`
- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenDisplacementSeriesSliceBijection.golden_displacement_slice_summable_iff`
- Dependency: [D5/S3/Analytic/Asymptotics/GoldenDisplacementSeriesTendstoOne](../Asymptotics/GoldenDisplacementSeriesTendstoOne.md)
- Dependency: [D5/S3/Analytic/Boundary/GoldenDisplacementSeriesContinuity](../Boundary/GoldenDisplacementSeriesContinuity.md)
- Dependency: [D5/S3/Analytic/SeriesInequalities/GoldenDisplacementSeriesStrictLowerBound](../SeriesInequalities/GoldenDisplacementSeriesStrictLowerBound.md)
