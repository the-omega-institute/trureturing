# Algebraic Cut-and-Project Data

## Abstract

Additive physical and internal projections define reusable model sets with exact window translation laws.

**Definition 1.1 (Cut-and-project projection data).**

Lean statement: `D5/S3/Aperiodic/AlgebraicCutProjectData.CutProjectData`

*Formalization.* `D5/S3/Aperiodic/AlgebraicCutProjectData.CutProjectData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An additive lattice carrier is equipped with physical and internal additive projections.

**Definition 1.2 (Internal window translation).**

Lean statement: `D5/S3/Aperiodic/AlgebraicCutProjectData.translateSet`

*Formalization.* `D5/S3/Aperiodic/AlgebraicCutProjectData.translateSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A translated window contains a point when shifting it back reaches the original window.

**Definition 1.3 (Window-selected model set).**

Lean statement: `D5/S3/Aperiodic/AlgebraicCutProjectData.modelSet`

*Formalization.* `D5/S3/Aperiodic/AlgebraicCutProjectData.modelSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Physical projections are selected by membership of the corresponding internal projections in a window.

**Theorem 1.4 (Window monotonicity).**

Lean statement: `D5/S3/Aperiodic/AlgebraicCutProjectData.modelSet_mono`

*Formalization.* `D5/S3/Aperiodic/AlgebraicCutProjectData.modelSet_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Enlarging the internal window enlarges the physical model set.

**Theorem 1.5 (Model sets preserve window unions).**

Lean statement: `D5/S3/Aperiodic/AlgebraicCutProjectData.modelSet_iUnion`

*Formalization.* `D5/S3/Aperiodic/AlgebraicCutProjectData.modelSet_iUnion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An arbitrary union of internal windows becomes the union of their model sets.

**Theorem 1.6 (Exact lattice translation law).**

Lean statement: `D5/S3/Aperiodic/AlgebraicCutProjectData.modelSet_translate_lattice`

*Formalization.* `D5/S3/Aperiodic/AlgebraicCutProjectData.modelSet_translate_lattice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translation of a window by an internal lattice image translates the model set by the corresponding physical image.

**Theorem 1.7 (Injective physical projection preserves intersections).**

Lean statement: `D5/S3/Aperiodic/AlgebraicCutProjectData.modelSet_inter_of_physical_injective`

*Formalization.* `D5/S3/Aperiodic/AlgebraicCutProjectData.modelSet_inter_of_physical_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When physical projection is injective, one physical point cannot hide distinct lattice witnesses, so binary intersections are exact.

**Theorem 1.8 (Full window gives the physical range).**

Lean statement: `D5/S3/Aperiodic/AlgebraicCutProjectData.modelSet_univ`

*Formalization.* `D5/S3/Aperiodic/AlgebraicCutProjectData.modelSet_univ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Selecting every internal point leaves exactly the range of the physical projection.

## References

- Truth anchor: `D5/S3/Aperiodic/AlgebraicCutProjectData.CutProjectData`
- Truth anchor: `D5/S3/Aperiodic/AlgebraicCutProjectData.translateSet`
- Truth anchor: `D5/S3/Aperiodic/AlgebraicCutProjectData.modelSet`
- Truth anchor: `D5/S3/Aperiodic/AlgebraicCutProjectData.modelSet_mono`
- Truth anchor: `D5/S3/Aperiodic/AlgebraicCutProjectData.modelSet_iUnion`
- Truth anchor: `D5/S3/Aperiodic/AlgebraicCutProjectData.modelSet_translate_lattice`
- Truth anchor: `D5/S3/Aperiodic/AlgebraicCutProjectData.modelSet_inter_of_physical_injective`
- Truth anchor: `D5/S3/Aperiodic/AlgebraicCutProjectData.modelSet_univ`
