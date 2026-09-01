# Golden Cut-and-Project Specialization

## Abstract

The existing golden lattice-window set is an accepted model set for generic physical and internal projections.

**Definition 1.1 (Golden ambient projection data).**

Lean statement: `D5/S3/Aperiodic/GoldenCutProjectSpecialization.goldenAmbientCutProjectData`

*Formalization.* `D5/S3/Aperiodic/GoldenCutProjectSpecialization.goldenAmbientCutProjectData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first and second Minkowski coordinates become the physical and internal additive projections.

**Definition 1.2 (Golden lattice acceptance).**

Lean statement: `D5/S3/Aperiodic/GoldenCutProjectSpecialization.IsGoldenLatticePoint`

*Formalization.* `D5/S3/Aperiodic/GoldenCutProjectSpecialization.IsGoldenLatticePoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The acceptance predicate selects exactly the already defined golden lattice points.

**Theorem 1.3 (Generic accepted set equals the existing golden set).**

Lean statement: `D5/S3/Aperiodic/GoldenCutProjectSpecialization.golden_accepted_model_set_eq_existing`

*Formalization.* `D5/S3/Aperiodic/GoldenCutProjectSpecialization.golden_accepted_model_set_eq_existing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic window-and-acceptance definition is extensionally identical to the frozen golden cut-and-project set.

**Theorem 1.4 (Canonical golden values lie in the accepted set).**

Lean statement: `D5/S3/Aperiodic/GoldenCutProjectSpecialization.golden_model_set_subset_generic_accepted`

*Formalization.* `D5/S3/Aperiodic/GoldenCutProjectSpecialization.golden_model_set_subset_generic_accepted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing one-way inclusion from natural-number golden expansions is transported to the generic interface.

**Theorem 1.5 (Dropping lattice acceptance enlarges the set).**

Lean statement: `D5/S3/Aperiodic/GoldenCutProjectSpecialization.golden_accepted_subset_unrestricted`

*Formalization.* `D5/S3/Aperiodic/GoldenCutProjectSpecialization.golden_accepted_subset_unrestricted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The golden accepted model set lies in the unrestricted ambient-plane window model set.

**Theorem 1.6 (Physical projection compatibility).**

Lean statement: `D5/S3/Aperiodic/GoldenCutProjectSpecialization.golden_physical_projection_eq`

*Formalization.* `D5/S3/Aperiodic/GoldenCutProjectSpecialization.golden_physical_projection_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic physical map is exactly the existing first-coordinate projection.

**Theorem 1.7 (Internal projection compatibility).**

Lean statement: `D5/S3/Aperiodic/GoldenCutProjectSpecialization.golden_internal_projection_eq`

*Formalization.* `D5/S3/Aperiodic/GoldenCutProjectSpecialization.golden_internal_projection_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic internal map is exactly the existing conjugate-coordinate projection.

## References

- Truth anchor: `D5/S3/Aperiodic/GoldenCutProjectSpecialization.goldenAmbientCutProjectData`
- Truth anchor: `D5/S3/Aperiodic/GoldenCutProjectSpecialization.IsGoldenLatticePoint`
- Truth anchor: `D5/S3/Aperiodic/GoldenCutProjectSpecialization.golden_accepted_model_set_eq_existing`
- Truth anchor: `D5/S3/Aperiodic/GoldenCutProjectSpecialization.golden_model_set_subset_generic_accepted`
- Truth anchor: `D5/S3/Aperiodic/GoldenCutProjectSpecialization.golden_accepted_subset_unrestricted`
- Truth anchor: `D5/S3/Aperiodic/GoldenCutProjectSpecialization.golden_physical_projection_eq`
- Truth anchor: `D5/S3/Aperiodic/GoldenCutProjectSpecialization.golden_internal_projection_eq`
- Dependency: [D5/S3/Aperiodic/AcceptedModelSet](AcceptedModelSet.md)
- Dependency: [D5/S1/Deficit/ModelSet/GoldenCutAndProject](../../S1/Deficit/ModelSet/GoldenCutAndProject.md)
