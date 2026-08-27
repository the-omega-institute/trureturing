/- GID: D5/S3/ConceptDynamics/DecisionValueScale/StrictPreferenceReversalValueState
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValueScale/StrictPreferenceReversalValueState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Opposite strict rankings force two temporal scalar value states to differ. -/

import Mathlib.Data.Real.Basic

/- Library-search audit trail (2026-08-27):
   * Repository searches for preference reversal, time-indexed utility, and
     value-state separation found no theorem on this source carrier.
   * `StrictSeparationImpossibility` concerns two actor types and report costs;
     the `NormativeScaleChoiceReversal` family constructs doctrine aggregates.
     Neither states inequality of two temporal value functions on one option set.
   * Pinned Mathlib exact hit `lt_asymm` is applied directly to the two strict
     rankings; no library theorem packages the source interpretation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DecisionValueScale.StrictPreferenceReversalValueState

/-- On one unchanged option carrier, scalar value functions that faithfully
represent opposite strict rankings at two moments cannot be the same function.
Thus a strict preference reversal excludes a single time-invariant scalar value
state for both moments. -/
theorem strict_preference_reversal_changes_value_state
    {Choice : Type*} (a b : Choice)
    (valueAtFirst valueAtSecond : Choice -> Real)
    (firstStrictPreference : valueAtFirst a > valueAtFirst b)
    (secondStrictPreference : valueAtSecond b > valueAtSecond a) :
    Not (valueAtFirst = valueAtSecond) := by
  intro unchangedValueState
  rw [unchangedValueState.symm] at secondStrictPreference
  exact lt_asymm firstStrictPreference secondStrictPreference

#print axioms strict_preference_reversal_changes_value_state

end D5.S3.ConceptDynamics.DecisionValueScale.StrictPreferenceReversalValueState
