# Admissibility-Selected Model Sets

## Abstract

Admissibility predicates separate language-selected model sets from unrestricted lattice-window model sets.

**Definition 1.1 (Accepted model set).**

Lean statement: `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet`

*Formalization.* `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A physical point is selected by a lattice witness satisfying both an internal window condition and an acceptance predicate.

**Theorem 1.2 (Accepted sets lie in unrestricted model sets).**

Lean statement: `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet_subset_modelSet`

*Formalization.* `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet_subset_modelSet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Dropping the language or cone predicate leaves the ordinary window-selected model set.

**Theorem 1.3 (Window monotonicity).**

Lean statement: `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet_window_mono`

*Formalization.* `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet_window_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Enlarging the internal window enlarges the accepted model set.

**Theorem 1.4 (Acceptance monotonicity).**

Lean statement: `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet_predicate_mono`

*Formalization.* `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet_predicate_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weakening the lattice acceptance rule enlarges the selected physical set.

**Theorem 1.5 (Universal acceptance recovers the model set).**

Lean statement: `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet_true`

*Formalization.* `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet_true` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unrestricted model set is the special case in which every lattice point is accepted.

**Theorem 1.6 (Conjunctive acceptance gives intersection).**

Lean statement: `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet_and_of_physical_injective`

*Formalization.* `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet_and_of_physical_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With injective physical projection, conjunction of two acceptance predicates is physical-set intersection.

**Theorem 1.7 (Shift-invariant acceptance preserves translation).**

Lean statement: `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet_translate_lattice`

*Formalization.* `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet_translate_lattice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A lattice-shift invariant language or cone retains the exact cut-and-project translation law.

## References

- Truth anchor: `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet`
- Truth anchor: `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet_subset_modelSet`
- Truth anchor: `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet_window_mono`
- Truth anchor: `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet_predicate_mono`
- Truth anchor: `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet_true`
- Truth anchor: `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet_and_of_physical_injective`
- Truth anchor: `D5/S3/Aperiodic/AcceptedModelSet.acceptedModelSet_translate_lattice`
- Dependency: [D5/S3/Aperiodic/AlgebraicCutProjectData](AlgebraicCutProjectData.md)
