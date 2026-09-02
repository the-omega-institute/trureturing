# Cut-and-Project Schemes

## Abstract

The algebraic core of a cut-and-project construction selects physical model sets from internal windows and preserves window intersections.

**Theorem 1.1 (Model sets preserve binary window intersections).**

$$\forall Physical \in Type, Internal \in Type,\; \left(\operatorname{AddGroup}\left(Physical\right) \land \operatorname{AddGroup}\left(Internal\right)\right) \Rightarrow \left(\forall scheme \in \operatorname{Scheme}\left(Physical, Internal\right), left \in \operatorname{Set}\left(Internal\right), right \in \operatorname{Set}\left(Internal\right),\; \operatorname{modelSet}\left(scheme, \operatorname{inter}\left(left, right\right)\right) = \operatorname{inter}\left(\operatorname{modelSet}\left(scheme, left\right), \operatorname{modelSet}\left(scheme, right\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CutProjectScheme.modelSet_inter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A scheme stores an additive subgroup of physical times internal space and requires physical projection to be injective on its lattice carrier.

An internal window selects lattice points, whose physical projections form the model set.

Physical injectivity identifies the two lattice witnesses arising from membership in two model sets. Their shared internal coordinate then lies in the window intersection.

## References

- Truth anchor: `D5/S3/Fourier/CutProjectScheme.modelSet_inter`
