/- GID: D5/S3/ConceptDynamics/Control/InvariantConceptPrecludesOutcomeRemedy
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Control/InvariantConceptPrecludesOutcomeRemedy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Invariant concepts block outcome changes by allowed actions. -/

import Mathlib.Data.Set.Lattice

/- Library-search audit trail (2026-08-27):
   * Body-shape searches for an allowed action preserving a concept and therefore
     its factored outcome found no exact D5 theorem.
   * `EntityStrengthThreeConditions.ProcessStable` is adjacent but requires
     preservation at every state, whereas the source fixes the actual state and
     its allowed-action set.
   * `identity_restoration_implies_value_compensation` is also adjacent but
     concerns a harm-repair composite and has no public different-target remedy
     obstruction.
   * Pinned Mathlib supplies `congrArg` and set membership, but no packaged
     theorem states both the actionwise equality and remedy exclusion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Control.InvariantConceptPrecludesOutcomeRemedy

/-- If every allowed action preserves the concept at the actual state, then the
outcome computed from that concept is invariant and no allowed action can reach
a different desired outcome. -/
theorem invariant_concept_precludes_outcome_remedy
    {State Action ConceptValue Outcome : Type*}
    (allowed : Set Action) (step : Action -> State -> State)
    (concept : State -> ConceptValue) (evaluate : ConceptValue -> Outcome)
    (actual : State)
    (concept_invariant : forall action, action ∈ allowed ->
      concept (step action actual) = concept actual) :
    (forall action, action ∈ allowed ->
      evaluate (concept (step action actual)) = evaluate (concept actual)) /\
      forall desired : Outcome, desired ≠ evaluate (concept actual) ->
        Not (exists action, action ∈ allowed /\
          evaluate (concept (step action actual)) = desired) := by
  have outcome_invariant : forall action, action ∈ allowed ->
      evaluate (concept (step action actual)) = evaluate (concept actual) := by
    intro action action_allowed
    exact congrArg evaluate (concept_invariant action action_allowed)
  refine ⟨outcome_invariant, ?_⟩
  intro desired desired_differs
  rintro ⟨action, action_allowed, reaches_desired⟩
  apply desired_differs
  exact reaches_desired.symm.trans (outcome_invariant action action_allowed)

/-- A nontrivial state/action model satisfies the source hypotheses. -/
example :
    let allowed : Set Bool := Set.univ
    let step : Bool -> (Bool × Bool) -> Bool × Bool :=
      fun action state => (state.1, action)
    let concept : (Bool × Bool) -> Bool := Prod.fst
    let evaluate : Bool -> Bool := Bool.not
    (forall action, action ∈ allowed ->
      concept (step action (false, false)) = concept (false, false)) /\
      (forall action, action ∈ allowed ->
        evaluate (concept (step action (false, false))) =
          evaluate (concept (false, false))) /\
      (forall desired, desired ≠ evaluate (concept (false, false)) ->
        Not (exists action, action ∈ allowed /\
          evaluate (concept (step action (false, false))) = desired)) := by
  dsimp
  have invariant : forall action : Bool, action ∈ (Set.univ : Set Bool) ->
      Prod.fst ((false, action) : Bool × Bool) = Prod.fst (false, false) := by
    intro action _
    rfl
  exact ⟨invariant, invariant_concept_precludes_outcome_remedy
    Set.univ (fun (action : Bool) (state : Bool × Bool) => (state.1, action))
      Prod.fst Bool.not (false, false) invariant⟩

#print axioms invariant_concept_precludes_outcome_remedy

end D5.S3.ConceptDynamics.Control.InvariantConceptPrecludesOutcomeRemedy
