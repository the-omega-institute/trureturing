/- GID: D5/S3/ConceptDynamics/Reversibility/WaitingCostValueReversal
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Reversibility/WaitingCostValueReversal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive waiting cost alone can make delayed optimal value strictly lower. -/

import D5.S3.ConceptDynamics.DecisionValue.FreeInformationValue

/- Library-search audit trail (2026-08-27):
   * Body-shape searches for `informationCost = 0`, waiting cost, and strict
     value reversal found the canonical `uninformedExpectedValue`,
     `informedExpectedValue`, and `admissiblePolicies` primitives in
     `DecisionValue.FreeInformationValue`; they are imported rather than
     redeclared.
   * `OpportunityLossValueReversal` is the adjacent action-loss countermodel,
     but it fixes cost at zero and therefore does not cover this clause.
   * Pinned-Mathlib searches for value of information, passive protocols,
     adaptive experiments, and waiting cost found no exact theorem. The
     `loogle` and `leansearch` executables were unavailable. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Reversibility.WaitingCostValueReversal

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.DecisionValue.FreeInformationValue

/-- A positive waiting cost can strictly reverse the value comparison even
when observation leaves the world unchanged, every immediate action remains
available, and every constant policy can ignore the observation. All clauses
use the same decision model. -/
theorem positive_waiting_cost_can_reverse_value :
    ∃ (expectation : Concept (Unit -> Real) Real)
      (observe : Concept Unit Unit)
      (worldAfterObservation : Unit -> Unit -> Unit)
      (utility : Concept Unit (Unit -> Real))
      (actionsBeforeObservation : Set Unit)
      (actionsAfterObservation : Unit -> Set Unit)
      (candidatePolicies : Set (Unit -> Unit))
      (waitingCost uninformedValue informedValue : Real),
      0 < waitingCost ∧
      (∀ evidence state, worldAfterObservation evidence state = state) ∧
      (∀ action ∈ actionsBeforeObservation,
        (fun _ : Unit => action) ∈ candidatePolicies) ∧
      (∀ evidence,
        actionsAfterObservation evidence = actionsBeforeObservation) ∧
      IsGreatest
        ((uninformedExpectedValue expectation utility) ''
          actionsBeforeObservation)
        uninformedValue ∧
      IsGreatest
        ((informedExpectedValue expectation observe worldAfterObservation utility
            waitingCost) ''
          admissiblePolicies candidatePolicies actionsAfterObservation)
        informedValue ∧
      informedValue < uninformedValue := by
  refine ⟨
    (fun payoff => payoff ()),
    (fun _ => ()),
    (fun _ state => state),
    (fun _ _ => 1),
    Set.univ,
    (fun _ => Set.univ),
    Set.univ,
    1,
    1,
    0,
    by norm_num,
    ?_, ?_, ?_, ?_, ?_, by norm_num⟩
  · intro _ state
    rfl
  · intro _ _
    exact Set.mem_univ _
  · intro _
    rfl
  · constructor
    · exact Set.mem_image_of_mem _ (Set.mem_univ ())
    · intro value hValue
      rcases hValue with ⟨action, _, rfl⟩
      exact le_rfl
  · constructor
    · refine ⟨fun _ => (), ?_, ?_⟩
      · exact ⟨Set.mem_univ _, fun _ => Set.mem_univ _⟩
      · norm_num [informedExpectedValue]
    · intro value hValue
      rcases hValue with ⟨policy, _, rfl⟩
      norm_num [informedExpectedValue]

#print axioms positive_waiting_cost_can_reverse_value

end D5.S3.ConceptDynamics.Reversibility.WaitingCostValueReversal
