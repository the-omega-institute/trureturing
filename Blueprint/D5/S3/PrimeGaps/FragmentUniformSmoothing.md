# Uniform Smoothing for the Fragment Mass Law

## Abstract

Construct the independent uniform scale mixture and derive its volume domination without assuming a density bound.

**Definition 1.1 (An actual product-measure construction).**

Lean statement: `D5/S3/PrimeGaps/FragmentUniformSmoothing.uniformScaleMixture`

*Formalization.* `D5/S3/PrimeGaps/FragmentUniformSmoothing.uniformScaleMixture` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any real zeta and real measure nu, push nu times Lebesgue measure restricted to (0,1] forward by (s,u) mapped to u times (zeta+s). The coordinate order is residual first and uniform second. Independence is supplied by the product measure.

**Theorem 1.2 (Probability normalization).**

Lean statement: `D5/S3/PrimeGaps/FragmentUniformSmoothing.uniformScaleMixture_isProbabilityMeasure`

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/FragmentUniformSmoothing.uniformScaleMixture_isProbabilityMeasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real zeta and every probability measure nu, the constructed mixture is a probability measure. This assertion requires neither positive zeta nor nonnegative residual support. The unit interval has volume exactly one and the product map is measurable.

**Theorem 1.3 (Volume domination on every measurable set).**

Lean statement: `D5/S3/PrimeGaps/FragmentUniformSmoothing.uniformScaleMixture_apply_le`

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/FragmentUniformSmoothing.uniformScaleMixture_apply_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive zeta, a probability measure nu supported almost surely on nonnegative reals, and any measurable set A, the mixture probability of A is at most ofReal(1/zeta) times volume(A). Condition on s. Restriction can only decrease measure, and the existing Lebesgue scaling theorem gives volume of the multiplication preimage as volume(A)/(zeta+s). Integrate the bound 1/(zeta+s) at most 1/zeta. No density, interval estimate or fixed-point identity is a premise.

**Theorem 1.4 (An explicit interval probability).**

Lean statement: `D5/S3/PrimeGaps/FragmentUniformSmoothing.uniformScaleMixture_Ico_le`

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/FragmentUniformSmoothing.uniformScaleMixture_Ico_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same positivity, probability and nonnegative-support conditions, every real x and delta satisfy mixture([x,x+delta)) at most ofReal(delta/zeta). The theorem includes empty intervals when delta is nonpositive. This consumes the volume-domination theorem and the existing interval-volume formula.

**Theorem 1.5 (Transfer to a law with a proved fixed-point identity).**

Lean statement: `D5/S3/PrimeGaps/FragmentUniformSmoothing.uniform_scale_fixedPoint_Ico_le`

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/FragmentUniformSmoothing.uniform_scale_fixedPoint_Ico_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The additional equality nu=uniformScaleMixture(zeta,nu) transfers the preceding interval bound to nu itself. This companion does not establish that equality for fragmentLaw. Its named downstream consumer is the fixed-mesh fragment estimate. The canonical dyadic-Poisson-to-perpetuity identity remains a separate Lean obligation.

The fixed-point characterization is classical Dickman theory, as discussed by Bhattacharjee and Goldstein (arXiv:1706.08192); the scale-invariant Poisson interpretation is discussed by Bhattacharjee and Molchanov (arXiv:1911.06229). These papers provide mathematical context. This source makes no new-distribution or first-formalization claim. No kernel or emitter success is inferred from source authorship.

## References

- Truth anchor: `D5/S3/PrimeGaps/FragmentUniformSmoothing.uniformScaleMixture`
- Truth anchor: `D5/S3/PrimeGaps/FragmentUniformSmoothing.uniformScaleMixture_Ico_le`
- Truth anchor: `D5/S3/PrimeGaps/FragmentUniformSmoothing.uniformScaleMixture_apply_le`
- Truth anchor: `D5/S3/PrimeGaps/FragmentUniformSmoothing.uniformScaleMixture_isProbabilityMeasure`
- Truth anchor: `D5/S3/PrimeGaps/FragmentUniformSmoothing.uniform_scale_fixedPoint_Ico_le`
