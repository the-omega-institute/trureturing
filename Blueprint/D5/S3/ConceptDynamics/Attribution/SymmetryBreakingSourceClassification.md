# Fixed Symmetry and Its Declared Breaking Sources

## Abstract

Fixed symmetry obstructs equivariant selection, and the declared source taxonomy has four exhaustive classes.

**Theorem 1.1 (Fixed symmetry obstructs selection and sources have a declared class).**

$$\operatorname{FixedSymmetry}\left(admissible\right) \land \operatorname{Nonempty}\left(sources\right) \Rightarrow\\{}\neg \operatorname{ExistsAdmissibleEquivariantSelector}\left(admissible\right) \land \exists source \in sources, \operatorname{IsDeclaredSymmetryBreakingSource}\left(source\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/SymmetryBreakingSourceClassification.fixed_symmetry_obstruction_and_source_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selector obstruction is inherited directly from the existing common-fixed-symmetry theorem. A nonempty set of source tags then supplies a tag, and constructor elimination places it in one of the four declared classes.

The source type is a closed formal taxonomy. This statement does not claim that an unmodeled real-world mechanism has already been mapped into that taxonomy.

**Lemma 1.2 (The common fixed-symmetry premise is necessary).**

$$\operatorname{ExistsAdmissibleEquivariantSelector}\left(Unit, Unit\right) \land \neg \operatorname{FixedPointFreeSymmetry}\left(Unit, Unit\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/SymmetryBreakingSourceClassification.common_fixed_symmetry_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On singleton state and action spaces, the constant selector is admissible and equivariant for the trivial action. Every action is fixed, so the fixed-point-free symmetry premise is false.

**Lemma 1.3 (A source set must be nonempty).**

$$\neg \exists source \in \operatorname{emptySet}\left(SymmetryBreakingSource\right), \operatorname{IsDeclaredSymmetryBreakingSource}\left(source\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/SymmetryBreakingSourceClassification.nonempty_source_hypothesis_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty source set contains no tag, hence it cannot witness any of the four declared source classes.

**Lemma 1.4 (An empty state space supplies no obstruction witness).**

$$\neg \operatorname{Nonempty}\left(Empty\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/SymmetryBreakingSourceClassification.empty_state_cannot_supply_fixed_symmetry_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The obstruction starts with a state. The empty type has no inhabitant, so this degenerate state space cannot satisfy that premise.

**Lemma 1.5 (A singleton internal source is classified).**

$$\exists source \in \operatorname{singleton}\left(observerInternal\right), \operatorname{IsDeclaredSymmetryBreakingSource}\left(source\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/SymmetryBreakingSourceClassification.singleton_source_is_classified` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The singleton containing the observer-internal source tag gives a concrete nonempty classification witness.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/SymmetryBreakingSourceClassification.common_fixed_symmetry_hypothesis_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/SymmetryBreakingSourceClassification.empty_state_cannot_supply_fixed_symmetry_witness`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/SymmetryBreakingSourceClassification.fixed_symmetry_obstruction_and_source_classification`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/SymmetryBreakingSourceClassification.nonempty_source_hypothesis_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/SymmetryBreakingSourceClassification.singleton_source_is_classified`
- Dependency: [D5/S3/ConceptDynamics/Attribution/FixedSymmetrySelectorObstruction](FixedSymmetrySelectorObstruction.md)
