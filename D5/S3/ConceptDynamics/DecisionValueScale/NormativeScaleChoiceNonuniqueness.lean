/- GID: D5/S3/ConceptDynamics/DecisionValueScale/NormativeScaleChoiceNonuniqueness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValueScale/NormativeScaleChoiceNonuniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive doctrine rescalings preserve rankings but select opposite actions. -/

import D5.S3.ConceptDynamics.DecisionValue.NormativeScaleChoiceReversal

/- Library-search audit trail (2026-08-25):
   * Exact repository primitive `normative_scale_choice_reversal` constructs the
     equiprobable two-doctrine arithmetic and proves ranking invariance and opposite
     aggregate winners; it is imported and applied directly.
   * Body-shape searches for `probability true * utility`, Boolean doctrine/action
     utilities, and positive rescaling found only that frozen primitive and the
     withdrawn metadata wrapper; no second canonical family primitive exists.
   * Pinned Mathlib supplies real ordered-field arithmetic but no source-shaped
     theorem about doctrine-scale choice reversal. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DecisionValueScale.NormativeScaleChoiceNonuniqueness

open D5.S3.ConceptDynamics.DecisionValue.NormativeScaleChoiceReversal

/-- There are two positive utility scale pairs for the same equiprobable doctrines.
Every within-doctrine comparison is invariant between the pairs, while their
probability-weighted aggregate choices are opposite. -/
theorem normative_scale_choice_nonuniqueness :
    ∃ alphaFirst betaFirst alphaSecond betaSecond : Real,
      0 < alphaFirst ∧ 0 < betaFirst ∧
      0 < alphaSecond ∧ 0 < betaSecond ∧
      let probability : Bool -> Real := fun _ => 1 / 2
      let utility : Real -> Real -> Bool -> Bool -> Real :=
        fun alpha beta doctrine action =>
          match doctrine, action with
          | true, true => alpha
          | true, false => 0
          | false, true => 0
          | false, false => beta
      let expectedUtility : Real -> Real -> Bool -> Real :=
        fun alpha beta action =>
          probability true * utility alpha beta true action +
            probability false * utility alpha beta false action
      (utility alphaFirst betaFirst true true >
          utility alphaFirst betaFirst true false ∧
        utility alphaFirst betaFirst false false >
          utility alphaFirst betaFirst false true) ∧
      (∀ doctrine leftAction rightAction,
        (utility alphaFirst betaFirst doctrine leftAction >
            utility alphaFirst betaFirst doctrine rightAction) ↔
          (utility alphaSecond betaSecond doctrine leftAction >
            utility alphaSecond betaSecond doctrine rightAction)) ∧
      expectedUtility alphaFirst betaFirst true >
          expectedUtility alphaFirst betaFirst false ∧
      expectedUtility alphaSecond betaSecond false >
        expectedUtility alphaSecond betaSecond true := by
  refine ⟨2, 1, 1, 2, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have reversal := normative_scale_choice_reversal
    (2 : Real) 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  dsimp at reversal ⊢
  rcases reversal with
    ⟨_probability, _firstCoordinates, _secondCoordinates,
      firstRanking, _secondRanking, rankingInvariance,
      _firstAggregate, _secondAggregate, firstWinner, secondWinner⟩
  exact ⟨firstRanking, rankingInvariance, firstWinner, secondWinner⟩

#print axioms normative_scale_choice_nonuniqueness

end D5.S3.ConceptDynamics.DecisionValueScale.NormativeScaleChoiceNonuniqueness
