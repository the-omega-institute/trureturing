/- GID: D5/S3/ConceptDynamics/DecisionValue/InformationValueMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValue/InformationValueMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Free ignorable refinement with unchanged actions cannot lower optimal value. -/

import D5.S3.ConceptDynamics.DecisionValue.FreeInformationValue

/- Library-search audit trail (2026-08-24):
   * Exact atom-id search across `D5`, `Blueprint`, digestion formalizations, and accepted
     freezes found no prior receipt or declaration.
   * Repository search found the canonical `informedExpectedValue` and `admissiblePolicies`
     primitives and the special unconditioned-baseline theorem
     `free_ignorable_information_value_nonnegative` in `FreeInformationValue`; this module
     imports and reuses the primitives rather than declaring sibling copies.
   * That existing theorem exactly covers source theorem 296.1, but not this theorem's
     arbitrary coarse concept and concept-conditioned policy, so it is not an exact hit here.
   * Pinned Mathlib's `Set.mem_image`, `Set.mem_image_of_mem`, and the upper-bound component
     of `IsGreatest` are applied directly. No library theorem packages the refinement factor
     with all four operational safeguards; `loogle` and `leansearch` are absent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DecisionValue.InformationValueMonotonicity

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.DecisionValue.FreeInformationValue

/-- Refining a concept cannot lower optimal value when the added information is free,
world-preserving, action-preserving, and ignorable by policy composition. -/
theorem free_information_refinement_value_monotone
    {State Coarse Fine Action : Type*}
    (expectation : Concept (State -> Real) Real)
    (coarseConcept : Concept State Coarse)
    (fineConcept : Concept State Fine)
    (worldAfterInformation : Fine -> State -> State)
    (utility : Concept State (Action -> Real))
    (informationCost : Real)
    (actionsAtCoarse : Coarse -> Set Action)
    (actionsAtFine : Fine -> Set Action)
    (coarseCandidatePolicies : Set (Coarse -> Action))
    (fineCandidatePolicies : Set (Fine -> Action))
    (coarseOptimalValue fineOptimalValue : Real)
    (informationFree : informationCost = 0)
    (informationDoesNotChangeWorld :
      ∀ evidence state, worldAfterInformation evidence state = state)
    (refinementAndSafeguards :
      ∃ forget : Fine -> Coarse,
        coarseConcept = forget ∘ fineConcept ∧
        (∀ evidence,
          actionsAtFine evidence = actionsAtCoarse (forget evidence)) ∧
        (∀ policy ∈ coarseCandidatePolicies,
          policy ∘ forget ∈ fineCandidatePolicies))
    (coarseOptimal : IsGreatest
      ((informedExpectedValue expectation coarseConcept
          (fun _ state => state) utility 0) ''
        admissiblePolicies coarseCandidatePolicies actionsAtCoarse)
      coarseOptimalValue)
    (fineOptimal : IsGreatest
      ((informedExpectedValue expectation fineConcept worldAfterInformation utility
          informationCost) ''
        admissiblePolicies fineCandidatePolicies actionsAtFine)
      fineOptimalValue) :
    coarseOptimalValue ≤ fineOptimalValue := by
  rcases refinementAndSafeguards with
    ⟨forget, coarseFactors, actionSetsUnchanged, canIgnoreInformation⟩
  rcases (Set.mem_image _ _ _).mp coarseOptimal.1 with
    ⟨bestCoarsePolicy, bestCoarseAdmissible, bestCoarseValue⟩
  let ignoredFinePolicy : Fine -> Action := bestCoarsePolicy ∘ forget
  have ignoredFineAdmissible :
      ignoredFinePolicy ∈
        admissiblePolicies fineCandidatePolicies actionsAtFine := by
    refine ⟨canIgnoreInformation bestCoarsePolicy bestCoarseAdmissible.1, ?_⟩
    intro evidence
    rw [actionSetsUnchanged evidence]
    exact bestCoarseAdmissible.2 (forget evidence)
  have ignoredFineValue :
      informedExpectedValue expectation fineConcept worldAfterInformation utility
          informationCost ignoredFinePolicy = coarseOptimalValue := by
    rw [← bestCoarseValue]
    simp [informedExpectedValue, ignoredFinePolicy, informationFree,
      informationDoesNotChangeWorld, coarseFactors] <;>
      (try unfold Function.comp) <;> rfl
  apply fineOptimal.2
  rw [← ignoredFineValue]
  exact Set.mem_image_of_mem
    (informedExpectedValue expectation fineConcept worldAfterInformation utility
      informationCost)
    ignoredFineAdmissible

/-- The public safeguards and optimization premises have a concrete one-state model. -/
example : (2 : Real) ≤ 2 := by
  let expectation : Concept (Unit -> Real) Real := fun payoff => payoff ()
  let coarseConcept : Concept Unit Unit := fun _ => ()
  let fineConcept : Concept Unit Unit := fun _ => ()
  let worldAfterInformation : Unit -> Unit -> Unit := fun _ state => state
  let utility : Concept Unit (Unit -> Real) := fun _ _ => 2
  apply free_information_refinement_value_monotone
    expectation coarseConcept fineConcept worldAfterInformation utility 0
    (fun _ => Set.univ) (fun _ => Set.univ) Set.univ Set.univ 2 2
  · rfl
  · intro _ state
    exact rfl
  · refine ⟨id, rfl, ?_, ?_⟩
    · intro _
      rfl
    · intro _ _
      exact Set.mem_univ _
  · constructor
    · refine ⟨fun _ => (), ?_, ?_⟩
      · exact ⟨Set.mem_univ _, fun _ => Set.mem_univ _⟩
      · simp [informedExpectedValue, expectation, utility]
    · intro value hValue
      rcases (Set.mem_image _ _ _).mp hValue with ⟨policy, _, rfl⟩
      simp [informedExpectedValue, expectation, coarseConcept, utility]
  · constructor
    · refine ⟨fun _ => (), ?_, ?_⟩
      · exact ⟨Set.mem_univ _, fun _ => Set.mem_univ _⟩
      · simp [informedExpectedValue, expectation, fineConcept,
          worldAfterInformation, utility]
    · intro value hValue
      rcases (Set.mem_image _ _ _).mp hValue with ⟨policy, _, rfl⟩
      simp [informedExpectedValue, expectation, fineConcept,
        worldAfterInformation, utility]

#print axioms free_information_refinement_value_monotone

end D5.S3.ConceptDynamics.DecisionValue.InformationValueMonotonicity
