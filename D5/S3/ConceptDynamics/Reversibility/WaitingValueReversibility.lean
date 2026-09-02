/- GID: D5/S3/ConceptDynamics/Reversibility/WaitingValueReversibility
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Reversibility/WaitingValueReversibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Preserved information and options explain when waiting retains value. -/

import D5.S3.ConceptDynamics.Reversibility.OpportunityLossValueReversal
import D5.S3.ConceptDynamics.Reversibility.WaitingCostValueReversal
import D5.S3.ConceptDynamics.Reversibility.WorldChangeValueReversal

/- Library-search audit trail (2026-09-02):
   * Repository name and body-shape searches found the canonical
     `uninformedExpectedValue`, `informedExpectedValue`, and
     `admissiblePolicies` primitives in `DecisionValue.FreeInformationValue`.
   * Exact D5 support hits for the opportunity-loss, positive-cost, and
     world-change clauses are imported above and applied below.
   * Repository searches found no waiting-value countermodel with a public
     disclosure penalty or a distinct triggered third-party response carrier.
   * Pinned-Mathlib searches found generic `Set.image`, `Set.mem_image_of_mem`,
     and `IsGreatest` support, but no theorem combining the source clauses.
   * Searches of every installed non-Mathlib Lake package found no matching
     waiting-value, information-exposure, or third-party-response theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Reversibility.WaitingValueReversibility

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.DecisionValue.FreeInformationValue
open D5.S3.ConceptDynamics.Reversibility.OpportunityLossValueReversal
open D5.S3.ConceptDynamics.Reversibility.WaitingCostValueReversal
open D5.S3.ConceptDynamics.Reversibility.WorldChangeValueReversal

/-- Constant-policy simulation and nonnegative value follow from free,
world-preserving, ignorable information and retained actions. Opportunity
loss, positive cost, world change, public disclosure, and a triggered
third-party response each have a same-model counterexample in which waiting
is strictly worse. -/
theorem waiting_value_from_information_and_option_preservation
    :
    (∀ {Evidence Action : Type*}
      (actionsBeforeObservation : Set Action)
      (actionsAfterObservation : Evidence -> Set Action)
      (candidatePolicies : Set (Evidence -> Action)),
      (((∀ action ∈ actionsBeforeObservation,
            (fun _ : Evidence => action) ∈ candidatePolicies) ∧
          (∀ evidence, actionsBeforeObservation ⊆
            actionsAfterObservation evidence)) ->
        ∀ action ∈ actionsBeforeObservation,
          (fun _ : Evidence => action) ∈
            admissiblePolicies candidatePolicies actionsAfterObservation)) ∧
    (∀ {State Evidence Action : Type*}
      (expectation : Concept (State -> Real) Real)
      (observe : Concept State Evidence)
      (worldAfterObservation : Evidence -> State -> State)
      (utility : Concept State (Action -> Real))
      (informationCost : Real)
      (actionsBeforeObservation : Set Action)
      (actionsAfterObservation : Evidence -> Set Action)
      (candidatePolicies : Set (Evidence -> Action))
      (uninformedValue informedValue : Real)
      (uninformedOptimal : IsGreatest
        ((uninformedExpectedValue expectation utility) ''
          actionsBeforeObservation)
        uninformedValue)
      (informedOptimal : IsGreatest
        ((informedExpectedValue expectation observe worldAfterObservation utility
            informationCost) ''
          admissiblePolicies candidatePolicies actionsAfterObservation)
        informedValue),
      ((((informationCost = 0) ∧
          (∀ evidence state,
            worldAfterObservation evidence state = state)) ∧
        ((∀ action ∈ actionsBeforeObservation,
            (fun _ : Evidence => action) ∈ candidatePolicies) ∧
          (∀ evidence, actionsBeforeObservation ⊆
            actionsAfterObservation evidence))) ->
        uninformedValue ≤ informedValue)) ∧
    (∃ (expectation : Concept (Unit -> Real) Real)
      (observe : Concept Unit Unit)
      (worldAfterObservation : Unit -> Unit -> Unit)
      (utility : Concept Unit (Bool -> Real))
      (actionsBeforeObservation : Set Bool)
      (actionsAfterObservation : Unit -> Set Bool)
      (candidatePolicies : Set (Unit -> Bool))
      (uninformedValue informedValue : Real),
      (∀ evidence state,
        worldAfterObservation evidence state = state) ∧
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
        ((informedExpectedValue expectation observe worldAfterObservation
            utility 0) ''
          admissiblePolicies candidatePolicies actionsAfterObservation)
        informedValue ∧
      informedValue < uninformedValue) ∧
    (∃ (expectation : Concept (Unit -> Real) Real)
      (observe : Concept Unit Unit)
      (worldAfterObservation : Unit -> Unit -> Unit)
      (utility : Concept Unit (Unit -> Real))
      (actionsBeforeObservation : Set Unit)
      (actionsAfterObservation : Unit -> Set Unit)
      (candidatePolicies : Set (Unit -> Unit))
      (waitingCost uninformedValue informedValue : Real),
      0 < waitingCost ∧
      (∀ evidence state,
        worldAfterObservation evidence state = state) ∧
      (∀ action ∈ actionsBeforeObservation,
        (fun _ : Unit => action) ∈ candidatePolicies) ∧
      (∀ evidence,
        actionsAfterObservation evidence = actionsBeforeObservation) ∧
      IsGreatest
        ((uninformedExpectedValue expectation utility) ''
          actionsBeforeObservation)
        uninformedValue ∧
      IsGreatest
        ((informedExpectedValue expectation observe worldAfterObservation
            utility waitingCost) ''
          admissiblePolicies candidatePolicies actionsAfterObservation)
        informedValue ∧
      informedValue < uninformedValue) ∧
    (∃ (expectation : Concept (Bool -> Real) Real)
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
        ((informedExpectedValue expectation observe worldAfterObservation
            utility 0) ''
          admissiblePolicies candidatePolicies actionsAfterObservation)
        informedValue ∧
      informedValue < uninformedValue) ∧
    (∃ (expectation : Concept (Unit -> Real) Real)
      (observe : Concept Unit Unit)
      (worldAfterObservation : Unit -> Unit -> Unit)
      (utility : Concept Unit (Unit -> Real))
      (publicDisclosure : Concept Unit Unit)
      (exposurePenalty : Unit -> Real)
      (actionsBeforeObservation : Set Unit)
      (actionsAfterObservation : Unit -> Set Unit)
      (candidatePolicies : Set (Unit -> Unit))
      (uninformedValue exposedValue : Real),
      (∀ evidence state,
        worldAfterObservation evidence state = state) ∧
      (∀ action ∈ actionsBeforeObservation,
        (fun _ : Unit => action) ∈ candidatePolicies) ∧
      (∀ evidence, actionsBeforeObservation ⊆
        actionsAfterObservation evidence) ∧
      (∃ state,
        0 < exposurePenalty (publicDisclosure (observe state))) ∧
      IsGreatest
        ((uninformedExpectedValue expectation utility) ''
          actionsBeforeObservation)
        uninformedValue ∧
      IsGreatest
        ((fun policy => expectation (fun state =>
            utility (worldAfterObservation (observe state) state)
                (policy (observe state)) -
              exposurePenalty (publicDisclosure (observe state)))) ''
          admissiblePolicies candidatePolicies actionsAfterObservation)
        exposedValue ∧
      exposedValue < uninformedValue) ∧
    (∃ (expectation : Concept (Bool -> Real) Real)
      (observe : Concept Bool Unit)
      (worldWithoutResponse : Unit -> Bool -> Bool)
      (thirdPartyResponse : Unit -> Bool -> Bool)
      (utility : Concept Bool (Unit -> Real))
      (actionsBeforeObservation : Set Unit)
      (actionsAfterObservation : Unit -> Set Unit)
      (candidatePolicies : Set (Unit -> Unit))
      (uninformedValue informedValue : Real),
      (∀ evidence state,
        worldWithoutResponse evidence state = state) ∧
      (∃ evidence state,
        thirdPartyResponse evidence
            (worldWithoutResponse evidence state) ≠
          worldWithoutResponse evidence state) ∧
      (∀ action ∈ actionsBeforeObservation,
        (fun _ : Unit => action) ∈ candidatePolicies) ∧
      (∀ evidence, actionsBeforeObservation ⊆
        actionsAfterObservation evidence) ∧
      IsGreatest
        ((uninformedExpectedValue expectation utility) ''
          actionsBeforeObservation)
        uninformedValue ∧
      IsGreatest
        ((informedExpectedValue expectation observe
            (fun evidence state =>
              thirdPartyResponse evidence
                (worldWithoutResponse evidence state)) utility 0) ''
          admissiblePolicies candidatePolicies actionsAfterObservation)
        informedValue ∧
      informedValue < uninformedValue) := by
  refine ⟨?_, ?_, opportunity_loss_can_reverse_waiting_value,
    positive_waiting_cost_can_reverse_value,
    world_change_can_reverse_waiting_value, ?_, ?_⟩
  · rintro Evidence Action actionsBeforeObservation actionsAfterObservation
      candidatePolicies ⟨canIgnoreInformation, actionSetNotReduced⟩
      action actionAvailable
    exact ⟨canIgnoreInformation action actionAvailable,
      fun evidence => actionSetNotReduced evidence actionAvailable⟩
  · rintro State Evidence Action expectation observe worldAfterObservation utility
      informationCost actionsBeforeObservation actionsAfterObservation
      candidatePolicies uninformedValue informedValue uninformedOptimal
      informedOptimal ⟨⟨informationFree, observationDoesNotChangeWorld⟩,
      ⟨canIgnoreInformation, actionSetNotReduced⟩⟩
    exact free_ignorable_information_value_nonnegative
      expectation observe worldAfterObservation utility informationCost
      actionsBeforeObservation actionsAfterObservation candidatePolicies
      uninformedValue informedValue informationFree
      observationDoesNotChangeWorld canIgnoreInformation actionSetNotReduced
      uninformedOptimal informedOptimal
  · refine ⟨
      (fun payoff => payoff ()),
      (fun _ => ()),
      (fun _ state => state),
      (fun _ _ => 1),
      (fun _ => ()),
      (fun _ => 1),
      Set.univ,
      (fun _ => Set.univ),
      Set.univ,
      1,
      0,
      ?_, ?_, ?_, ?_, ?_, ?_, by norm_num⟩
    · intro _ state
      rfl
    · intro _ _
      exact Set.mem_univ _
    · intro _ _ _
      exact Set.mem_univ _
    · exact ⟨(), by norm_num⟩
    · constructor
      · exact Set.mem_image_of_mem _ (Set.mem_univ ())
      · intro value hValue
        rcases hValue with ⟨action, _, rfl⟩
        exact le_rfl
    · constructor
      · refine ⟨fun _ => (), ?_, ?_⟩
        · exact ⟨Set.mem_univ _, fun _ => Set.mem_univ _⟩
        · norm_num
      · intro value hValue
        rcases hValue with ⟨policy, _, rfl⟩
        norm_num
  · refine ⟨
      (fun payoff => payoff false),
      (fun _ => ()),
      (fun _ state => state),
      (fun _ _ => true),
      (fun state _ => if state then 0 else 1),
      Set.univ,
      (fun _ => Set.univ),
      Set.univ,
      1,
      0,
      ?_, ?_, ?_, ?_, ?_, ?_, by norm_num⟩
    · intro _ state
      rfl
    · exact ⟨(), false, by simp⟩
    · intro _ _
      exact Set.mem_univ _
    · intro _ _ _
      exact Set.mem_univ _
    · constructor
      · refine ⟨(), Set.mem_univ _, ?_⟩
        norm_num [uninformedExpectedValue]
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

#print axioms waiting_value_from_information_and_option_preservation

end D5.S3.ConceptDynamics.Reversibility.WaitingValueReversibility
