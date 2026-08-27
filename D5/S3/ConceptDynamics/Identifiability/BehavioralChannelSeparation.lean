/- GID: D5/S3/ConceptDynamics/Identifiability/BehavioralChannelSeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Identifiability/BehavioralChannelSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Opposite strict reports require a type-dependent behavioral channel. -/

import D5.S3.ConceptDynamics.StrictSeparationImpossibility

/- Library-search audit trail (2026-08-27):
   * Exact D5 hit `strict_separation_impossible` rules out opposite strict
     report preferences when outcome preferences and report costs are common.
   * Body-shape searches found no existing primitive that combines outcome
     preference, verification, type-dependent cost, and external effects.
     The four source channels are therefore composed inline in the theorem.
   * Pinned Mathlib provides linear arithmetic normalization but no theorem
     packaging this four-channel behavioral-identification consequence. The
     `loogle` and `leansearch` executables were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Identifiability.BehavioralChannelSeparation

open D5.S3.ConceptDynamics.StrictSeparationImpossibility

/-- If two types strictly prefer different reports when report scores are
constructed from outcome preference, verification, cost, and external effects,
then at least one of those four channels must distinguish the types. -/
theorem behavioral_identification_requires_channel_difference
    {Theta Report Outcome : Type*}
    (theta theta' : Theta) (reportTheta reportTheta' : Report)
    (mechanismResult : Report -> Outcome)
    (outcomePreference : Theta -> Outcome -> Real)
    (verificationEffect reportCost externalEffect : Theta -> Report -> Real)
    (thetaPrefers :
      outcomePreference theta (mechanismResult reportTheta) +
          verificationEffect theta reportTheta - reportCost theta reportTheta +
          externalEffect theta reportTheta >
        outcomePreference theta (mechanismResult reportTheta') +
          verificationEffect theta reportTheta' - reportCost theta reportTheta' +
          externalEffect theta reportTheta')
    (theta'Prefers :
      outcomePreference theta' (mechanismResult reportTheta') +
          verificationEffect theta' reportTheta' - reportCost theta' reportTheta' +
          externalEffect theta' reportTheta' >
        outcomePreference theta' (mechanismResult reportTheta) +
          verificationEffect theta' reportTheta - reportCost theta' reportTheta +
          externalEffect theta' reportTheta) :
    (∃ outcome,
      outcomePreference theta outcome ≠ outcomePreference theta' outcome) ∨
      (∃ report,
        verificationEffect theta report ≠ verificationEffect theta' report) ∨
      (∃ report, reportCost theta report ≠ reportCost theta' report) ∨
      (∃ report,
        externalEffect theta report ≠ externalEffect theta' report) := by
  by_contra noChannelDifference
  simp only [not_or, not_exists, not_ne_iff] at noChannelDifference
  rcases noChannelDifference with
    ⟨samePreference, sameVerification, sameCost, sameExternal⟩
  apply strict_separation_impossible theta theta' reportTheta reportTheta'
    mechanismResult outcomePreference
      (fun report =>
        -(verificationEffect theta report - reportCost theta report +
          externalEffect theta report))
      samePreference
  constructor
  · simpa only [sub_eq_add_neg, neg_neg, add_assoc] using thetaPrefers
  · rw [← sameVerification reportTheta', ← sameCost reportTheta',
      ← sameExternal reportTheta', ← sameVerification reportTheta,
      ← sameCost reportTheta, ← sameExternal reportTheta] at theta'Prefers
    simpa only [sub_eq_add_neg, neg_neg, add_assoc] using theta'Prefers

/-- Boolean types and reports realize opposite strict preferences through the
outcome-preference channel. -/
example :
    let outcomePreference : Bool -> Bool -> Real :=
      fun actor outcome => if actor = outcome then 1 else 0
    outcomePreference false false > outcomePreference false true ∧
      outcomePreference true true > outcomePreference true false := by
  norm_num

#print axioms behavioral_identification_requires_channel_difference

end D5.S3.ConceptDynamics.Identifiability.BehavioralChannelSeparation
