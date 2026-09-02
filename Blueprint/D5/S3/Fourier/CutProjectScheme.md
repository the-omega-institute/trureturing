# Cut-and-Project Schemes

## Abstract

The algebraic core of a cut-and-project scheme produces model sets functorially from internal windows.

**Theorem 1.1 (Model sets are monotone in the internal window).**

$$W_{1} \subseteq W_{2} \implies \operatorname{modelSet}(S, W_{1}) \subseteq \operatorname{modelSet}(S, W_{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CutProjectScheme.scheme_modelSet_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A scheme stores an additive subgroup of physical times internal space and requires physical projection to be injective on its lattice carrier.

An internal window selects lattice points, whose physical projections form the model set.

Enlarging the window can only enlarge the selection, so the model-set construction is monotone; the same injectivity also makes it preserve binary window intersections.

## References

- Truth anchor: `D5/S3/Fourier/CutProjectScheme.scheme_modelSet_mono`
