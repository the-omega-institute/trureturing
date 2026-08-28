/- GID: D5/S3/ConceptDynamics/RefinementGeometry/LocalGlobalAtlasExactness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementGeometry/LocalGlobalAtlasExactness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical state-thread exactness splits into separation and gluing. -/

import D5.S3.ConceptDynamics.RefinementGeometry.InverseLimitCompletion
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-28):
   * Exact family hit `stateThread` is the canonical map from global states to
     compatible inverse-limit threads; it is imported rather than redeclared.
   * `stateThread_bijective_iff_complete_and_separates` is related but does not
     publicly expose the kernel-diagonal and range-full clauses or their logical
     independence.
   * Pinned Mathlib's `Set.range_eq_univ` supplies the surjectivity/range bridge;
     no exact packaged theorem combines all public clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementGeometry.LocalGlobalAtlasExactness

open D5.S3.ConceptDynamics.RefinementGeometry.InverseLimitCompletion

/-- For every refinement atlas, global-to-local exactness is precisely the
conjunction of uniqueness (diagonal kernel) and existence (full compatible
thread range). Constant towers over `Option Bool` and `Unit` show that neither
clause implies the other. -/
theorem local_global_atlas_exactness :
    (∀ {X : Type*} (system : RefinementSystem X),
      Function.Bijective (stateThread system) ↔
        Setoid.ker (stateThread system) = (⊥ : Setoid X) ∧
          Set.range (stateThread system) = Set.univ) ∧
      (∃ system : RefinementSystem.{0, 0} Bool,
        Setoid.ker (stateThread system) = (⊥ : Setoid Bool) ∧
          Set.range (stateThread system) ≠ Set.univ) ∧
      ∃ system : RefinementSystem.{0, 0} Bool,
        Set.range (stateThread system) = Set.univ ∧
          Setoid.ker (stateThread system) ≠ (⊥ : Setoid Bool) := by
  constructor
  · intro X system
    constructor
    · rintro ⟨injective, surjective⟩
      constructor
      · apply Setoid.ext
        intro left right
        change
          (stateThread system left = stateThread system right) ↔ left = right
        exact injective.eq_iff
      · exact Set.range_eq_univ.2 surjective
    · rintro ⟨kernelDiagonal, rangeFull⟩
      constructor
      · intro left right sameThread
        have related : Setoid.ker (stateThread system) left right := sameThread
        rw [kernelDiagonal] at related
        exact related
      · exact Set.range_eq_univ.1 rangeFull
  constructor
  · let injectiveSystem : RefinementSystem Bool :=
      { Coordinate := fun _ => Option Bool
        readout := fun _ state => some state
        restrict := fun _ => id
        compatible := by
          intro level state
          rfl }
    refine ⟨injectiveSystem, ?_, ?_⟩
    · apply Setoid.ext
      intro left right
      change
        (stateThread injectiveSystem left =
          stateThread injectiveSystem right) ↔ left = right
      constructor
      · intro sameThread
        have sameAtZero := congrArg
          (fun thread => thread.value 0) sameThread
        exact Option.some.inj sameAtZero
      · intro equal
        rw [equal]
    · let missing : InverseThread injectiveSystem :=
        { value := fun _ => none
          compatible := by
            intro level
            rfl }
      intro rangeFull
      have missingInRange : missing ∈ Set.range (stateThread injectiveSystem) := by
        rw [rangeFull]
        exact Set.mem_univ missing
      rcases missingInRange with ⟨state, stateProducesMissing⟩
      have sameAtZero := congrArg
        (fun thread => thread.value 0) stateProducesMissing
      change some state = none at sameAtZero
      cases sameAtZero
  · let surjectiveSystem : RefinementSystem Bool :=
      { Coordinate := fun _ => Unit
        readout := fun _ _ => ()
        restrict := fun _ => id
        compatible := by
          intro level state
          rfl }
    refine ⟨surjectiveSystem, ?_, ?_⟩
    · apply Set.range_eq_univ.2
      intro thread
      refine ⟨false, ?_⟩
      apply InverseThread.ext
      funext level
      exact Subsingleton.elim _ _
    · intro kernelDiagonal
      have falseRelatedTrue :
          Setoid.ker (stateThread surjectiveSystem) false true := by
        rfl
      rw [kernelDiagonal] at falseRelatedTrue
      exact Bool.false_ne_true falseRelatedTrue

#print axioms local_global_atlas_exactness

end D5.S3.ConceptDynamics.RefinementGeometry.LocalGlobalAtlasExactness
