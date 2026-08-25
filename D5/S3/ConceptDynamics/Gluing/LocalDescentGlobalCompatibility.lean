/- GID: D5/S3/ConceptDynamics/Gluing/LocalDescentGlobalCompatibility
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Gluing/LocalDescentGlobalCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Local descent, inverse-limit realization, and cocycle compatibility are distinct. -/

import D5.S3.ConceptDynamics.Gluing.GlobalFrameCoboundaryCriterion
import D5.S3.ConceptDynamics.RefinementGeometry.InverseLimitCompletion
import D5.S3.QuantumContext.PublicLedgerDescent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Gluing.LocalDescentGlobalCompatibility

open D5.S3.ConceptDynamics.Gluing.GlobalFrameCoboundaryCriterion
open D5.S3.ConceptDynamics.RefinementGeometry.InverseLimitCompletion
open D5.S3.QuantumContext.PublicLedgerDescent

/-- Natural numbers observed through their truncations at every finite level. -/
def truncatedNaturalSystem : RefinementSystem ℕ where
  Coordinate level := Fin (level + 1)
  readout level state := ⟨min state level, by omega⟩
  restrict level value := ⟨min value.1 level, by omega⟩
  compatible level state := by
    apply Fin.ext
    change min (min state (level + 1)) level = min state level
    omega

/-- The compatible thread that takes the largest coordinate at every finite level. -/
def escapingThread : InverseThread truncatedNaturalSystem where
  value level := ⟨level, by omega⟩
  compatible level := by
    apply Fin.ext
    simp [truncatedNaturalSystem]

/-- Every finite truncation is realized by a natural number. -/
theorem every_finite_readout_is_surjective :
    ∀ level, Function.Surjective (truncatedNaturalSystem.readout level) := by
  intro level coordinate
  refine ⟨coordinate.1, ?_⟩
  apply Fin.ext
  simp only [truncatedNaturalSystem, Fin.val_mk]
  omega

/-- The maximal compatible thread is not the thread of any natural number. -/
theorem escaping_thread_not_in_global_image :
    escapingThread ∉ Set.range (stateThread truncatedNaturalSystem) := by
  rintro ⟨state, hState⟩
  have hAtNextLevel := congrArg
    (fun thread => (thread.value (state + 1)).1) hState
  change min state (state + 1) = state + 1 at hAtNextLevel
  omega

/-- Local closure does not supply global closure by itself. Two locally additive charts can fail
to glue; levelwise-surjective finite readouts can miss a compatible inverse-limit thread; and
unit-valued transition data glue to a global frame exactly when their cocycle is a coboundary. -/
theorem local_descent_requires_global_gluing_checks :
    ((∀ c, incompatibleWitnessLocalValue c (witnessAtomSupport c) = 1) ∧
      IsContextwiseAdditive witnessEventSupport IsDisjointUnion
        incompatibleWitnessLocalValue ∧
      ¬ ∃ globalValue : CoveredEvent witnessEventSupport → ℝ,
        RestrictsToContexts witnessEventSupport incompatibleWitnessLocalValue globalValue) ∧
    ((∀ level, Function.Surjective (truncatedNaturalSystem.readout level)) ∧
      escapingThread ∉ Set.range (stateThread truncatedNaturalSystem)) ∧
    (∀ (Index Base UnitGroup : Type*) [Group UnitGroup]
      (overlap : Index → Index → Base → Prop)
      (transition : Index → Index → Base → UnitGroup),
      (∃ globalFrameCoefficients : Index → Base → UnitGroup,
        ∀ i j x, overlap i j x →
          globalFrameCoefficients i x =
            transition i j x * globalFrameCoefficients j x) ↔
      ∃ localUnit : Index → Base → UnitGroup,
        ∀ i j x, overlap i j x →
          transition i j x = (localUnit i x)⁻¹ * localUnit j x) := by
  refine ⟨incompatible_overlapping_contexts_do_not_descend, ?_, ?_⟩
  · exact ⟨every_finite_readout_is_surjective,
      escaping_thread_not_in_global_image⟩
  · intro Index Base UnitGroup _ overlap transition
    exact global_frame_iff_transition_coboundary overlap transition

#print axioms truncatedNaturalSystem
#print axioms escapingThread
#print axioms every_finite_readout_is_surjective
#print axioms escaping_thread_not_in_global_image
#print axioms local_descent_requires_global_gluing_checks

end D5.S3.ConceptDynamics.Gluing.LocalDescentGlobalCompatibility
