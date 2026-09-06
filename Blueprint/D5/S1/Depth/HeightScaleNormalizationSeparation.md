# Height-Scale Normalization Separation

## Abstract

Polynomial denominator depth and golden continued-fraction depth admit separate but no common positive normalization.

**Definition 1.1 (Positive-level denominator error scale).**

Lean statement: `D5/S1/Depth/HeightScaleNormalizationSeparation.denominatorErrorScale`

*Formalization.* `D5/S1/Depth/HeightScaleNormalizationSeparation.denominatorErrorScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At level Q this scale is the inverse square of Q plus one. The shift keeps the denominator positive at every natural input and avoids the totalized division-by-zero branch.

**Definition 1.2 (Positive-level continued-fraction error scale).**

Lean statement: `D5/S1/Depth/HeightScaleNormalizationSeparation.continuedFractionErrorScale`

*Formalization.* `D5/S1/Depth/HeightScaleNormalizationSeparation.continuedFractionErrorScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the Q-plus-one power of the inverse golden ratio squared, the exponential error scale supplied by all-one continued-fraction depth.

**Theorem 1.3 (Separate normalizers exist but a common positive normalizer does not).**

$$\left(\exists wDen \in \operatorname{Seq}\left(R\right),\; \operatorname{Normalizes}\left(\mathit{wDen}, \mathit{dDen}, 1\right)\right) \land \left(\left(\exists wCf \in \operatorname{Seq}\left(R\right),\; \operatorname{Normalizes}\left(\mathit{wCf}, \mathit{dCf}, 1\right)\right) \land \left(\forall w \in \operatorname{Seq}\left(R\right), a \in R, b \in R,\; \left(0 < a \land 0 < b\right) \Rightarrow \left(\neg \left(\operatorname{Normalizes}\left(w, \mathit{dDen}, a\right) \land \operatorname{Normalizes}\left(w, \mathit{dCf}, b\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/HeightScaleNormalizationSeparation.height_scale_normalization_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write Normalizes(w,d,L) for convergence of w(Q) times d(Q) to L as Q tends to infinity. Both scales have explicit exact normalizers: the denominator square and the reciprocal exponential scale.

For an arbitrary weight, finite convergence on the inverse-square scale forces the exponentially normalized sequence to converge to zero. The proof uses the strict inequalities zero less than the inverse golden square less than one and polynomial-versus-geometric decay.

Consequently the same weight cannot give both scales finite positive limits. Positivity is essential: without it the shared zero limit would make the obstruction false.

## References

- Truth anchor: `D5/S1/Depth/HeightScaleNormalizationSeparation.continuedFractionErrorScale`
- Truth anchor: `D5/S1/Depth/HeightScaleNormalizationSeparation.denominatorErrorScale`
- Truth anchor: `D5/S1/Depth/HeightScaleNormalizationSeparation.height_scale_normalization_separation`
