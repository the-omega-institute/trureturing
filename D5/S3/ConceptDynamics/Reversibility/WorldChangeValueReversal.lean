/- GID: D5/S3/ConceptDynamics/Reversibility/WorldChangeValueReversal
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Reversibility/WorldChangeValueReversal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A changed world can make waiting strictly worse despite preserving every action. -/

import D5.S3.ConceptDynamics.DecisionValue.FreeInformationValue

/- Library-search audit trail (2026-08-27):
   * Repository searches found the canonical `uninformedExpectedValue`,
     `informedExpectedValue`, and `admissiblePolicies` primitives in
     `DecisionValue.FreeInformationValue`; they are imported rather than redeclared.
   * The adjacent frozen `opportunity_loss_can_reverse_waiting_value` theorem keeps
     the world unchanged and reverses value by removing an action, so it does not
     cover this changed-world countermodel.
   * Pinned-Mathlib searches found generic `IsGreatest` and image-membership lemmas,
     but no theorem packaging a changed-world value-of-waiting countermodel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Reversibility.WorldChangeValueReversal

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.DecisionValue.FreeInformationValue

/-- A world transition can strictly reverse the value of waiting even when
information is free, every constant policy is available, and no action is lost.
Every public clause is witnessed by the same decision model. -/
theorem world_change_can_reverse_waiting_value :
    ∃ (expectation : Concept (Bool -> Real) Real)
      (observe : Concept Bool Unit)
      (worldAfterObservation : Unit -> Bool -> Bool)
      (utility : Concept Bool (Unit -> Real))
      (actionsBeforeObservation : Set Unit)
      (actionsAfterObservation : Unit -> Set Unit)
      (candidatePolicies : Set (Unit -> Unit))
      (uninformedValue informedValue : Real),
      (∃ evidence state,
        worldAfterObservation evidence state ≠ state) ∧
      (∀ action ∈ actionsBeforeObservation,
        (fun _ : Unit => action) ∈ candidatePolicies) ∧
      (∀ evidence, actionsBeforeObservation ⊆
        actionsAfterObservation evidence) ∧
      IsGreatest
        ((uninformedExpectedValue expectation utility) ''
          actionsBeforeObservation)
        uninformedValue ∧
      IsGreatest
        ((informedExpectedValue expectation observe worldAfterObservation utility 0) ''
          admissiblePolicies candidatePolicies actionsAfterObservation)
        informedValue ∧
      informedValue < uninformedValue := by
  refine ⟨
    (fun payoff => payoff false),
    (fun _ => ()),
    (fun _ _ => true),
    (fun state _ => if state then 0 else 1),
    Set.univ,
    (fun _ => Set.univ),
    Set.univ,
    1,
    0,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(), false, by simp⟩
  · intro _ _
    exact Set.mem_univ _
  · intro _ _ _
    exact Set.mem_univ _
  · constructor
    · refine ⟨(), Set.mem_univ _, ?_⟩
      simp [uninformedExpectedValue]
    · intro value hValue
      rcases hValue with ⟨action, _, rfl⟩
      cases action
      norm_num [uninformedExpectedValue]
  · constructor
    · refine ⟨fun _ => (), ?_, ?_⟩
      · exact ⟨Set.mem_univ _, fun _ => Set.mem_univ _⟩
      · simp [informedExpectedValue]
    · intro value hValue
      rcases hValue with ⟨policy, _, rfl⟩
      simp [informedExpectedValue]
  · norm_num

#print axioms world_change_can_reverse_waiting_value

end D5.S3.ConceptDynamics.Reversibility.WorldChangeValueReversal
