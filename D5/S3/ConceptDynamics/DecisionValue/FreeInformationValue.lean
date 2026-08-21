/- GID: D5/S3/ConceptDynamics/DecisionValue/FreeInformationValue
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValue/FreeInformationValue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A free ignorable observation cannot lower optimal expected value. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Basic

/- Library-search audit trail (2026-08-21):
   * Repository searches for value-of-information, free observations, constant
     policies, and expected-value maxima found no exact theorem or family type
     beyond the canonical imported `Concept` function carrier.
   * Pinned Mathlib's exact `Set.mem_image` and `Set.mem_image_of_mem` results
     expose and construct the source value sets; both are applied below.
   * The upper-bound component of pinned Mathlib's `IsGreatest` is applied
     directly to the constructed ignore-information policy value.
   * No pinned-Mathlib theorem packages the four source safeguards and the
     resulting expected-value comparison. The `loogle` and `leansearch`
     executables were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DecisionValue.FreeInformationValue

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- Expected utility when one action is selected before observation. -/
def uninformedExpectedValue {State Action : Type*}
    (expectation : Concept (State -> Real) Real)
    (utility : Concept State (Action -> Real)) (action : Action) : Real :=
  expectation fun state => utility state action

/-- Expected utility of an observation-dependent policy, evaluated in the
post-observation world and net of the information cost. -/
def informedExpectedValue {State Evidence Action : Type*}
    (expectation : Concept (State -> Real) Real)
    (observe : Concept State Evidence)
    (worldAfterObservation : Evidence -> State -> State)
    (utility : Concept State (Action -> Real))
    (informationCost : Real) (policy : Evidence -> Action) : Real :=
  expectation (fun state =>
    utility (worldAfterObservation (observe state) state)
      (policy (observe state))) - informationCost

/-- Candidate policies whose selected action remains available after every
possible observation. -/
def admissiblePolicies {Evidence Action : Type*}
    (candidatePolicies : Set (Evidence -> Action))
    (actionsAfterObservation : Evidence -> Set Action) :
    Set (Evidence -> Action) :=
  {policy | policy ∈ candidatePolicies ∧
    ∀ evidence, policy evidence ∈ actionsAfterObservation evidence}

/-- Free information that leaves the world unchanged, can be ignored, and
does not remove actions has optimal value at least the uninformed optimum. -/
theorem free_ignorable_information_value_nonnegative
    {State Evidence Action : Type*}
    (expectation : Concept (State -> Real) Real)
    (observe : Concept State Evidence)
    (worldAfterObservation : Evidence -> State -> State)
    (utility : Concept State (Action -> Real))
    (informationCost : Real)
    (actionsBeforeObservation : Set Action)
    (actionsAfterObservation : Evidence -> Set Action)
    (candidatePolicies : Set (Evidence -> Action))
    (uninformedValue informedValue : Real)
    (informationFree : informationCost = 0)
    (observationDoesNotChangeWorld :
      ∀ evidence state, worldAfterObservation evidence state = state)
    (canIgnoreInformation :
      ∀ action ∈ actionsBeforeObservation,
        (fun _ : Evidence => action) ∈ candidatePolicies)
    (actionSetNotReduced :
      ∀ evidence, actionsBeforeObservation ⊆
        actionsAfterObservation evidence)
    (uninformedOptimal : IsGreatest
      ((uninformedExpectedValue expectation utility) ''
        actionsBeforeObservation)
      uninformedValue)
    (informedOptimal : IsGreatest
      ((informedExpectedValue expectation observe worldAfterObservation utility
          informationCost) ''
        admissiblePolicies candidatePolicies actionsAfterObservation)
      informedValue) :
    uninformedValue ≤ informedValue := by
  rcases (Set.mem_image _ _ _).mp uninformedOptimal.1 with
    ⟨bestAction, bestActionAvailable, bestActionValue⟩
  let ignorePolicy : Evidence -> Action := fun _ => bestAction
  have ignorePolicyAdmissible :
      ignorePolicy ∈
        admissiblePolicies candidatePolicies actionsAfterObservation := by
    refine ⟨canIgnoreInformation bestAction bestActionAvailable, ?_⟩
    intro evidence
    exact actionSetNotReduced evidence bestActionAvailable
  have ignorePolicyValue :
      informedExpectedValue expectation observe worldAfterObservation utility
          informationCost ignorePolicy = uninformedValue := by
    rw [← bestActionValue]
    simp [informedExpectedValue, uninformedExpectedValue, ignorePolicy,
      informationFree, observationDoesNotChangeWorld]
  apply informedOptimal.2
  rw [← ignorePolicyValue]
  exact Set.mem_image_of_mem
    (informedExpectedValue expectation observe worldAfterObservation utility
      informationCost)
    ignorePolicyAdmissible

/-- All source safeguards and both optimization premises have a concrete
one-state, one-observation, one-action model. -/
example : (2 : Real) ≤ 2 := by
  let expectation : Concept (Unit -> Real) Real := fun payoff => payoff ()
  let observe : Concept Unit Unit := fun _ => ()
  let worldAfterObservation : Unit -> Unit -> Unit := fun _ state => state
  let utility : Concept Unit (Unit -> Real) := fun _ _ => 2
  apply free_ignorable_information_value_nonnegative
    expectation observe worldAfterObservation utility 0
    Set.univ (fun _ => Set.univ) Set.univ 2 2
  · rfl
  · intro _ state
    exact rfl
  · intro _ _
    exact Set.mem_univ _
  · intro _ _ _
    exact Set.mem_univ _
  · constructor
    · exact Set.mem_image_of_mem _ (Set.mem_univ ())
    · intro value hValue
      rcases (Set.mem_image _ _ _).mp hValue with ⟨action, _, rfl⟩
      exact le_rfl
  · constructor
    · refine ⟨fun _ => (), ?_, ?_⟩
      · exact ⟨Set.mem_univ _, fun _ => Set.mem_univ _⟩
      · simp [informedExpectedValue, expectation, observe,
          worldAfterObservation, utility]
    · intro value hValue
      rcases (Set.mem_image _ _ _).mp hValue with ⟨policy, _, rfl⟩
      simp [informedExpectedValue, expectation, observe,
        worldAfterObservation, utility]

#print axioms free_ignorable_information_value_nonnegative

end D5.S3.ConceptDynamics.DecisionValue.FreeInformationValue
