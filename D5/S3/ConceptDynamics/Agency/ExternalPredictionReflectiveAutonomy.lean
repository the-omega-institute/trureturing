/- GID: D5/S3/ConceptDynamics/Agency/ExternalPredictionReflectiveAutonomy
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Agency/ExternalPredictionReflectiveAutonomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: External prediction and reflective autonomy are compatible. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Data.Set.Insert

/- Library-search audit trail (2026-08-27):
   * Exact current-tree hits `Concept` and `Refines` are the canonical concept
     carrier and factorization order; both are imported instead of redeclared.
   * Searches for external prediction together with availability, approval, and
     reflection-stable action found no exact D5 theorem.
   * `SelfFormationFreeWillBoundary` uses external-input insensitivity rather
     than reason factorization and reflective approval, so it is not an exact hit.
   * Pinned Mathlib supplies function composition and `Function.comp_assoc`, but
     no theorem packages the factor construction and shared autonomy model. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Agency.ExternalPredictionReflectiveAutonomy

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- A reason concept factored through an external readout makes every policy on
reasons externally predictable. This predictability coexists with availability,
present approval, and approval-preserving reflective action stability. -/
theorem external_prediction_compatible_with_reflective_autonomy :
    (forall {State Reason External Action : Type*}
      (reason : Concept State Reason) (external : Concept State External)
      (policy : Reason -> Action),
      Refines reason external ->
        exists factor : External -> Reason,
          reason = factor ∘ external /\
            policy ∘ reason = (policy ∘ factor) ∘ external) /\
      exists (reason external : Concept Bool Bool)
        (factor policy action : Bool -> Bool)
        (available : Bool -> Set Bool)
        (approves : Bool -> Bool -> Prop)
        (reflect : Bool -> Bool) (actual : Bool),
        reason = factor ∘ external /\
          action = policy ∘ reason /\
          action = (policy ∘ factor) ∘ external /\
          action actual ∈ available actual /\
          approves actual (action actual) /\
          action (reflect actual) = action actual /\
          approves (reflect actual) (action actual) := by
  constructor
  · intro State Reason External Action reason external policy refinement
    rcases refinement with ⟨factor, reason_factors⟩
    refine ⟨factor, reason_factors, ?_⟩
    rw [reason_factors]
    exact (Function.comp_assoc policy factor external).symm
  · refine ⟨id, id, id, id, id, (fun state => {state}),
      (fun state selected => selected = state), id, false, ?_⟩
    refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
    exact Set.mem_singleton false

#print axioms external_prediction_compatible_with_reflective_autonomy

end D5.S3.ConceptDynamics.Agency.ExternalPredictionReflectiveAutonomy
