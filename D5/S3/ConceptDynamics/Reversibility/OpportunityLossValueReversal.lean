/- GID: D5/S3/ConceptDynamics/Reversibility/OpportunityLossValueReversal
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Reversibility/OpportunityLossValueReversal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Losing an available action while waiting can strictly lower optimal value. -/

import D5.S3.ConceptDynamics.DecisionValue.FreeInformationValue

/- Library-search audit trail (2026-08-27):
   * Repository searches found the canonical `uninformedExpectedValue`,
     `informedExpectedValue`, and `admissiblePolicies` primitives in
     `DecisionValue.FreeInformationValue`; they are imported rather than redeclared.
   * The frozen nonnegative-value theorem assumes that observation does not reduce the
     action set, so it does not cover the present opportunity-loss countermodel.
   * Pinned-Mathlib searches for greatest image values, strict expected-value comparisons,
     and opportunity loss found generic `IsGreatest` image lemmas but no theorem packaging
     this source countermodel. The `loogle` and `leansearch` executables were unavailable. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Reversibility.OpportunityLossValueReversal

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.DecisionValue.FreeInformationValue

/-- Even with zero information cost, an unchanged world, and all constant policies
available as candidates, waiting can strictly lower optimal value when it removes an
action. Every public clause is witnessed by the same decision model. -/
theorem opportunity_loss_can_reverse_waiting_value :
    ∃ (expectation : Concept (Unit -> Real) Real)
      (observe : Concept Unit Unit)
      (worldAfterObservation : Unit -> Unit -> Unit)
      (utility : Concept Unit (Bool -> Real))
      (actionsBeforeObservation : Set Bool)
      (actionsAfterObservation : Unit -> Set Bool)
      (candidatePolicies : Set (Unit -> Bool))
      (uninformedValue informedValue : Real),
      (∀ evidence state, worldAfterObservation evidence state = state) ∧
      (∀ action ∈ actionsBeforeObservation,
        (fun _ : Unit => action) ∈ candidatePolicies) ∧
      (∃ evidence action,
        action ∈ actionsBeforeObservation ∧
          action ∉ actionsAfterObservation evidence) ∧
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
    (fun payoff => payoff ()),
    (fun _ => ()),
    (fun _ state => state),
    (fun _ action => match action with | false => 0 | true => 1),
    Set.univ,
    (fun _ => {false}),
    Set.univ,
    1,
    0,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ state
    rfl
  · intro _ _
    exact Set.mem_univ _
  · exact ⟨(), true, Set.mem_univ _, by simp⟩
  · constructor
    · refine ⟨true, Set.mem_univ _, ?_⟩
      simp [uninformedExpectedValue]
    · intro value hValue
      rcases hValue with ⟨action, _, rfl⟩
      cases action <;> norm_num [uninformedExpectedValue]
  · constructor
    · refine ⟨fun _ => false, ?_, ?_⟩
      · exact ⟨Set.mem_univ _, by simp⟩
      · simp [informedExpectedValue]
    · intro value hValue
      rcases hValue with ⟨policy, hPolicy, rfl⟩
      rcases hPolicy with ⟨_, hAvailable⟩
      have selectedFalse : policy () = false := by
        simpa using hAvailable ()
      simp [informedExpectedValue, selectedFalse]
  · norm_num

#print axioms opportunity_loss_can_reverse_waiting_value

end D5.S3.ConceptDynamics.Reversibility.OpportunityLossValueReversal
