/- GID: D5/S3/ConceptDynamics/DecisionValueScale/StrictPreferenceReversalAlternatives
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValueScale/StrictPreferenceReversalAlternatives
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A strict reversal forces a state change or loss of behavioral fidelity. -/

import D5.S3.ConceptDynamics.DecisionValueScale.StrictPreferenceReversalValueState

/- Library-search audit trail (2026-09-05):
   * Exact D5/body-shape searches found the frozen
     `strict_preference_reversal_changes_value_state` order contradiction, imported
     and applied below, but no theorem classifying all five source alternatives.
   * Nearby identity, context-refinement, waiting-value, and behavioral-channel
     modules use different carriers and do not state changes in the four determinants
     of one preference reversal.
   * Pinned Mathlib searches for preference reversal, strict preference, revealed
     preference, and faithful utility representation found no packaged theorem;
     Mathlib supplies the strict real order used by the frozen prerequisite.
   * Searches across every installed non-Mathlib Lake package found no matching
     preference-reversal classification theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DecisionValueScale.StrictPreferenceReversalAlternatives

open D5.S3.ConceptDynamics.DecisionValueScale.StrictPreferenceReversalValueState

/-- On one option carrier and one shared fact, opposite observed strict rankings
cannot both be represented by one scalar value function. If both rankings are
instead represented by a single state-indexed utility rule, then at least one of
the value, self, temporal, or contextual inputs changes, or one of the observed
behavior relations does not faithfully express that rule's strict preference. -/
theorem strict_preference_reversal_forces_state_change_or_behavioral_unfaithfulness
    {Choice Fact ValueState SelfConcept TimePreference ContextConcept : Type*}
    (a b : Choice) (facts : Fact)
    (valueAtFirst valueAtSecond : ValueState)
    (selfAtFirst selfAtSecond : SelfConcept)
    (timeAtFirst timeAtSecond : TimePreference)
    (contextAtFirst contextAtSecond : Fact -> ContextConcept)
    (behaviorAtFirst behaviorAtSecond : Choice -> Choice -> Prop)
    (utility :
      ValueState -> SelfConcept -> TimePreference -> ContextConcept ->
        Choice -> Real)
    (firstReversal : behaviorAtFirst a b)
    (secondReversal : behaviorAtSecond b a) :
    (Not (Exists fun commonValue : Choice -> Real =>
      (forall x y, behaviorAtFirst x y -> commonValue x > commonValue y) /\
      (forall x y, behaviorAtSecond x y -> commonValue x > commonValue y))) /\
    (Not (valueAtFirst = valueAtSecond) \/
      Not (selfAtFirst = selfAtSecond) \/
      Not (timeAtFirst = timeAtSecond) \/
      Not (contextAtFirst = contextAtSecond) \/
      Not (
        (forall x y, behaviorAtFirst x y ->
          utility valueAtFirst selfAtFirst timeAtFirst
              (contextAtFirst facts) x >
            utility valueAtFirst selfAtFirst timeAtFirst
              (contextAtFirst facts) y) /\
        (forall x y, behaviorAtSecond x y ->
          utility valueAtSecond selfAtSecond timeAtSecond
              (contextAtSecond facts) x >
            utility valueAtSecond selfAtSecond timeAtSecond
              (contextAtSecond facts) y))) := by
  constructor
  · rintro ⟨commonValue, representsFirst, representsSecond⟩
    have firstRank := representsFirst a b firstReversal
    have secondRank := representsSecond b a secondReversal
    exact
      (strict_preference_reversal_changes_value_state
        a b commonValue commonValue firstRank secondRank) rfl
  · by_cases valueUnchanged : valueAtFirst = valueAtSecond
    · by_cases selfUnchanged : selfAtFirst = selfAtSecond
      · by_cases timeUnchanged : timeAtFirst = timeAtSecond
        · by_cases contextUnchanged : contextAtFirst = contextAtSecond
          · by_cases behaviorFaithful :
              (forall x y, behaviorAtFirst x y ->
                utility valueAtFirst selfAtFirst timeAtFirst
                    (contextAtFirst facts) x >
                  utility valueAtFirst selfAtFirst timeAtFirst
                    (contextAtFirst facts) y) /\
              (forall x y, behaviorAtSecond x y ->
                utility valueAtSecond selfAtSecond timeAtSecond
                    (contextAtSecond facts) x >
                  utility valueAtSecond selfAtSecond timeAtSecond
                    (contextAtSecond facts) y)
            · rcases behaviorFaithful with
                ⟨representsFirst, representsSecond⟩
              have firstRank := representsFirst a b firstReversal
              have secondRank := representsSecond b a secondReversal
              rw [← valueUnchanged, ← selfUnchanged, ← timeUnchanged,
                ← contextUnchanged] at secondRank
              exfalso
              exact
                (strict_preference_reversal_changes_value_state
                  a b
                  (utility valueAtFirst selfAtFirst timeAtFirst
                    (contextAtFirst facts))
                  (utility valueAtFirst selfAtFirst timeAtFirst
                    (contextAtFirst facts))
                  firstRank secondRank) rfl
            · exact Or.inr (Or.inr (Or.inr (Or.inr behaviorFaithful)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl contextUnchanged)))
        · exact Or.inr (Or.inr (Or.inl timeUnchanged))
      · exact Or.inr (Or.inl selfUnchanged)
    · exact Or.inl valueUnchanged

#print axioms strict_preference_reversal_forces_state_change_or_behavioral_unfaithfulness

end D5.S3.ConceptDynamics.DecisionValueScale.StrictPreferenceReversalAlternatives
