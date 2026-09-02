# Golden Cut-and-Project Adapter

## Abstract

The existing golden Minkowski lattice instantiates the generic cut-and-project carrier without changing its model sets.

**Theorem 1.1 (The generic and existing golden model sets coincide).**

$$\operatorname{modelSet}(\operatorname{goldenScheme}(), W) = \operatorname{modelSet}_{\mathrm{golden}}(W)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/GoldenCutProjectSchemeAdapter.goldenScheme_modelSet_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lattice carrier is the existing range of the two real golden embeddings.

Injectivity of physical projection follows from injectivity of the distinguished real embedding on GoldenInt.

Unfolding a lattice-range witness identifies the generic internal-window selection with the repository's established modelSet predicate. The existing object therefore becomes the consumer of the shared cut-and-project API.

## References

- Truth anchor: `D5/S3/Fourier/GoldenCutProjectSchemeAdapter.goldenScheme_modelSet_eq`
- Dependency: [D5/S1/Scale/MinkowskiModelSet](../../S1/Scale/MinkowskiModelSet.md)
- Dependency: [D5/S3/Fourier/CutProjectScheme](CutProjectScheme.md)
