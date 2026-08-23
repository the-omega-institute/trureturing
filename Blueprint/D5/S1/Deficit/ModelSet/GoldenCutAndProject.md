# Golden Cut-and-Project Inclusion

## Abstract

The physical golden beta range lies in the golden-lattice cut-and-project set.

**Theorem 1.1 (The physical golden model set lies in the cut-and-project set).**

$$\left\{\operatorname{embedding}\left(x\right) \mid x \in goldenModelSet\right\} \subseteq goldenCutAndProjectSet$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/ModelSet/GoldenCutAndProject.golden_model_set_subset_cut_and_project` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each point of the golden model set is a canonical natural-number golden beta value. Its Minkowski embedding is a point of the golden lattice, and its physical coordinate is the original real embedding.

The internal coordinate of that lattice point is the beta contraction. The public contraction bound places it in the closed golden window, so the physical value is selected by the cut-and-project construction. This proves only the displayed inclusion, not the reverse one.

## References

- Truth anchor: `D5/S1/Deficit/ModelSet/GoldenCutAndProject.golden_model_set_subset_cut_and_project`
- Dependency: [D5/S1/Deficit/ModelSet/GoldenModelSetSelfSimilar](GoldenModelSetSelfSimilar.md)
- Dependency: [D5/S1/Scale/MinkowskiModelSet](../../Scale/MinkowskiModelSet.md)
