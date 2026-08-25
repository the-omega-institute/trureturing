/- GID: D5/S3/ConceptDynamics/DecisionValue/NormativeScaleChoiceReversal
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValue/NormativeScaleChoiceReversal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Uniform doctrine probabilities do not fix choices across utility scales. -/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/- Library-search audit trail (2026-08-25):
   * Repository searches for doctrine probabilities, normative scale reversal,
     and expected-utility choice reversal found no exact declaration.
   * `FreeInformationValue` has adjacent generic expected-value machinery, but
     it does not construct the source's two doctrines or compare their scales.
   * Body-shape searches for a uniform Boolean probability, a doctrine-indexed
     Boolean utility, and its probability-weighted aggregate found no family
     primitive on this carrier. The unrelated probability-law hits do not encode
     actions, doctrines, or normative utility.
   * Pinned Mathlib supplies ordered-field arithmetic and the `linarith`,
     `norm_num`, and `ring` tactics; no theorem packages the source model. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DecisionValue.NormativeScaleChoiceReversal

/-- With two equiprobable doctrines, positive rescaling preserves each
doctrine's strict action ranking while it can reverse the aggregate choice. -/
theorem normative_scale_choice_reversal
    (alphaFirst betaFirst alphaSecond betaSecond : Real)
    (alphaFirstPositive : 0 < alphaFirst)
    (betaFirstPositive : 0 < betaFirst)
    (alphaSecondPositive : 0 < alphaSecond)
    (betaSecondPositive : 0 < betaSecond)
    (firstChoosesA : betaFirst < alphaFirst)
    (secondChoosesB : alphaSecond < betaSecond) :
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
    (forall doctrine, probability doctrine = 1 / 2) ∧
      (utility alphaFirst betaFirst true true = alphaFirst ∧
        utility alphaFirst betaFirst true false = 0 ∧
        utility alphaFirst betaFirst false true = 0 ∧
        utility alphaFirst betaFirst false false = betaFirst) ∧
      (utility alphaSecond betaSecond true true = alphaSecond ∧
        utility alphaSecond betaSecond true false = 0 ∧
        utility alphaSecond betaSecond false true = 0 ∧
        utility alphaSecond betaSecond false false = betaSecond) ∧
      (utility alphaFirst betaFirst true true >
          utility alphaFirst betaFirst true false ∧
        utility alphaFirst betaFirst false false >
          utility alphaFirst betaFirst false true) ∧
      (utility alphaSecond betaSecond true true >
          utility alphaSecond betaSecond true false ∧
        utility alphaSecond betaSecond false false >
          utility alphaSecond betaSecond false true) ∧
      (forall doctrine leftAction rightAction,
        (utility alphaFirst betaFirst doctrine leftAction >
            utility alphaFirst betaFirst doctrine rightAction) ↔
          (utility alphaSecond betaSecond doctrine leftAction >
            utility alphaSecond betaSecond doctrine rightAction)) ∧
      (expectedUtility alphaFirst betaFirst true = alphaFirst / 2 ∧
        expectedUtility alphaFirst betaFirst false = betaFirst / 2) ∧
      (expectedUtility alphaSecond betaSecond true = alphaSecond / 2 ∧
        expectedUtility alphaSecond betaSecond false = betaSecond / 2) ∧
      expectedUtility alphaFirst betaFirst true >
          expectedUtility alphaFirst betaFirst false ∧
      expectedUtility alphaSecond betaSecond false >
        expectedUtility alphaSecond betaSecond true := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro doctrine
    norm_num
  · simp
  · simp
  · exact ⟨alphaFirstPositive, betaFirstPositive⟩
  · exact ⟨alphaSecondPositive, betaSecondPositive⟩
  · intro doctrine leftAction rightAction
    cases doctrine <;> cases leftAction <;> cases rightAction
    · simp
    · exact iff_of_true betaFirstPositive betaSecondPositive
    · constructor <;> intro negative <;> linarith
    · simp
    · simp
    · constructor <;> intro negative <;> linarith
    · exact iff_of_true alphaFirstPositive alphaSecondPositive
    · simp
  · constructor <;> ring
  · constructor <;> ring
  · norm_num
    linarith
  · norm_num
    linarith

#print axioms normative_scale_choice_reversal

end D5.S3.ConceptDynamics.DecisionValue.NormativeScaleChoiceReversal
