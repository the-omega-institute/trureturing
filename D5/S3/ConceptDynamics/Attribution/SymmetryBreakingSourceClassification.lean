/- GID: D5/S3/ConceptDynamics/Attribution/SymmetryBreakingSourceClassification
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/SymmetryBreakingSourceClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed symmetry blocks selection; nonempty source sets contain a listed class. -/

import D5.S3.ConceptDynamics.Attribution.FixedSymmetrySelectorObstruction

/- Library-search audit trail (2026-08-31):
   * Exact object-name and history searches found no symmetry-breaking source
     classification in the repository or pinned Mathlib.
   * Digest and nearby-family searches found the imported fixed-symmetry
     obstruction, but no declaration covering the corollary's four sources.
   * Loogle query `?x = ?a ∨ ?x = ?b ∨ ?x = ?c ∨ ?x = ?d`
     returned unrelated four-way facts such as `Char.utf8Size_eq`.
   * LeanSearch for four-constructor exhaustiveness failed at the API boundary;
     no LeanSearch hit is claimed. Constructor elimination is used directly. -/

namespace D5.S3.ConceptDynamics.Attribution.SymmetryBreakingSourceClassification

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.ConceptDynamics.Attribution.FixedSymmetrySelectorObstruction

/-- The four source classes declared for an actual symmetry-breaking addition.
The type records the source taxonomy, not an external completeness claim about
unmodeled mechanisms. -/
inductive SymmetryBreakingSource where
  | observerInternal
  | externalOrHidden
  | randomIndex
  | explicitTieBreaker
  deriving DecidableEq

/-- Membership in one of the four declared symmetry-breaking source classes. -/
def IsDeclaredSymmetryBreakingSource (source : SymmetryBreakingSource) : Prop :=
  source = .observerInternal ∨
    source = .externalOrHidden ∨
      source = .randomIndex ∨
        source = .explicitTieBreaker

/-- A common fixed-state symmetry rules out an admissible equivariant selector.
Any nonempty set of declared symmetry-breaking sources contains at least one of
the four source classes from the corollary. -/
theorem fixed_symmetry_obstruction_and_source_classification
    {G X A : Type*} [Group G] [MulAction G X] [MulAction G A]
    (admissible : X -> Set A)
    (fixedSymmetry : ∃ x : X, ∃ g : G,
      g • x = x ∧ ∀ a ∈ admissible x, g • a ≠ a)
    (sources : Set SymmetryBreakingSource) (sourcePresent : sources.Nonempty) :
    (¬ ∃ selector : X -> A,
      (∀ y, selector y ∈ admissible y) ∧
        ∀ (g : G) (y : X), selector (g • y) = g • selector y) ∧
      ∃ source ∈ sources, IsDeclaredSymmetryBreakingSource source := by
  constructor
  · exact no_equivariant_selector_of_common_fixed_symmetry admissible fixedSymmetry
  · rcases sourcePresent with ⟨source, sourceInSources⟩
    refine ⟨source, sourceInSources, ?_⟩
    cases source <;> simp [IsDeclaredSymmetryBreakingSource]

#print axioms fixed_symmetry_obstruction_and_source_classification

/-- On singleton state and action spaces, the constant selector is admissible
and equivariant under the trivial action, while the fixed-point-free symmetry
premise is false. Thus that premise is necessary for the obstruction. -/
theorem common_fixed_symmetry_hypothesis_is_necessary :
    let act : Unit -> Unit -> Unit := fun _ _ => ()
    let admissible : Unit -> Set Unit := fun _ => Set.univ
    (∃ selector : Unit -> Unit,
      (∀ state, selector state ∈ admissible state) ∧
        ∀ (symmetry : Unit) (state : Unit),
          selector (act symmetry state) = act symmetry (selector state)) ∧
      ¬ ∃ state : Unit, ∃ symmetry : Unit,
        act symmetry state = state ∧
          ∀ action ∈ admissible state, act symmetry action ≠ action := by
  dsimp only
  constructor
  · exact ⟨fun _ => (), by simp, by simp⟩
  · rintro ⟨state, symmetry, _fixesState, movesActions⟩
    exact movesActions () (by simp) (by simp)

#print axioms common_fixed_symmetry_hypothesis_is_necessary

/-- The nonemptiness hypothesis on a source set is necessary: the empty set
contains no witness from any declared class. -/
theorem nonempty_source_hypothesis_is_necessary :
    ¬ ∃ source ∈ (∅ : Set SymmetryBreakingSource),
      IsDeclaredSymmetryBreakingSource source := by
  simp

#print axioms nonempty_source_hypothesis_is_necessary

/-- An empty state type cannot supply the state required by the obstruction. -/
theorem empty_state_cannot_supply_fixed_symmetry_witness : ¬ Nonempty Empty := by
  rintro ⟨state⟩
  exact state.elim

#print axioms empty_state_cannot_supply_fixed_symmetry_witness

/-- A singleton source set realizes the classification nonvacuously. -/
theorem singleton_source_is_classified :
    ∃ source ∈ ({.observerInternal} : Set SymmetryBreakingSource),
      IsDeclaredSymmetryBreakingSource source := by
  exact ⟨.observerInternal, by simp, Or.inl rfl⟩

#print axioms singleton_source_is_classified

end D5.S3.ConceptDynamics.Attribution.SymmetryBreakingSourceClassification
