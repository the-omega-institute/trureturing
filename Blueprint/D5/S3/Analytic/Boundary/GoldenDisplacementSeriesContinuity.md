# Golden Displacement Series Continuity

## Abstract

The golden displacement sum is continuous at every point of its exact convergence region.

**Theorem 1.1 (The displacement sum is continuous on its convergence region).**

$$\operatorname{ContinuousOn}(p : \mathbb{R} \times \mathbb{R} \mapsto \sum_{n=0}^{\infty} \operatorname{dTerm}(p.1, p.2, n), \left\{p : \mathbb{R} \times \mathbb{R} \mid \operatorname{Summable}(\operatorname{dTerm}(p.1, p.2))\right\})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Boundary/GoldenDisplacementSeriesContinuity.golden_displacement_series_continuousOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a convergent parameter pair, the two strict affine constraints leave room to lower both coordinates while remaining in the convergence region. The series evaluated at the lowered corner is summable, and its terms provide a majorant.

The zero-index term vanishes identically. For every positive index both natural bases are at least one, so increasing either parameter does not increase its real-power factor. On the coordinatewise up-set from that corner the corner series therefore dominates every term uniformly on this neighborhood.

Pinned Mathlib's continuousOn_tsum applies on that local up-set. Since the original parameter lies in its interior, the resulting local continuity gives continuity at the chosen point, and hence continuity on the whole convergence region. No majorant uniform over the entire region is asserted.

## References

- Truth anchor: `D5/S3/Analytic/Boundary/GoldenDisplacementSeriesContinuity.golden_displacement_series_continuousOn`
