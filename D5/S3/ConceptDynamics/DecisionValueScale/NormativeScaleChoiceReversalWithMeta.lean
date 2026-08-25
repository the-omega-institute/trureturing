/- GID: D5/S3/ConceptDynamics/DecisionValueScale/NormativeScaleChoiceReversalWithMeta
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValueScale/NormativeScaleChoiceReversalWithMeta
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Scale reversal and explicit metanormative conflict data. -/

import D5.S3.ConceptDynamics.DecisionValue.NormativeScaleChoiceReversal
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/- Library-search audit trail (2026-08-25):
   * The frozen `NormativeScaleChoiceReversal` theorem is the exact arithmetic
     primitive for the two-doctrine, two-action reversal, but it does not expose
     metanormative inputs or permission intersections.
   * Repository searches for a carrier combining cross-theory scale, rights
     priority, worst-case scores, regret scores, and doctrine permissions found
     no exact declaration. The nearby permission-intersection theorems concern
     least sufficient bundles and do not cover this source model.
   * Body-shape searches for `probability true * utility`, a doctrine-indexed
     Boolean action carrier, and a common permission-set intersection found only
     the frozen arithmetic theorem and unrelated permission reachability.
   * Pinned Mathlib supplies `Set.inter`, extensional membership, and ordered
     real arithmetic; no theorem packages the source's combined clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DecisionValueScale.NormativeScaleChoiceReversalWithMeta

/-- The metanormative inputs named by the source: cross-theory scale,
rights priority, worst-case scores, regret scores, and doctrine permissions. -/
structure MetaNormativeData where
  crossTheoryScale : Bool -> Real
  rightsPriority : Bool -> Prop
  worstCasePrinciple : Bool -> Real
  regretMinimization : Bool -> Real
  permission : Bool -> Bool -> Prop

/-- Equiprobable doctrine probabilities and unchanged internal rankings do not
determine a unique cross-doctrine action. The explicit metanormative data are
carried independently, and an empty intersection of permission sets yields no
action licensed by every doctrine. -/
theorem normative_scale_choice_reversal_with_metanormative_data
    (alphaFirst betaFirst alphaSecond betaSecond : Real)
    (probability : Bool -> Real)
    (utilityFirst utilitySecond : Bool -> Bool -> Real)
    (metaData : MetaNormativeData)
    (alphaFirstPositive : 0 < alphaFirst)
    (betaFirstPositive : 0 < betaFirst)
    (alphaSecondPositive : 0 < alphaSecond)
    (betaSecondPositive : 0 < betaSecond)
    (firstChoosesA : betaFirst < alphaFirst)
    (secondChoosesB : alphaSecond < betaSecond)
    (probabilityHalf : ∀ doctrine, probability doctrine = 1 / 2)
    (firstCoordinates :
      utilityFirst true true = alphaFirst ∧
        utilityFirst true false = 0 ∧
        utilityFirst false true = 0 ∧
        utilityFirst false false = betaFirst)
    (secondCoordinates :
      utilitySecond true true = alphaSecond ∧
        utilitySecond true false = 0 ∧
        utilitySecond false true = 0 ∧
        utilitySecond false false = betaSecond)
    (commonPermissionEmpty :
      (({action : Bool | metaData.permission true action} : Set Bool) ∩
          ({action : Bool | metaData.permission false action} : Set Bool)) = ∅) :
    (∀ doctrine, probability doctrine = 1 / 2) ∧
      (utilityFirst true true = alphaFirst ∧
        utilityFirst true false = 0 ∧
        utilityFirst false true = 0 ∧
        utilityFirst false false = betaFirst) ∧
      (utilitySecond true true = alphaSecond ∧
        utilitySecond true false = 0 ∧
        utilitySecond false true = 0 ∧
        utilitySecond false false = betaSecond) ∧
      (utilityFirst true true > utilityFirst true false ∧
        utilityFirst false false > utilityFirst false true) ∧
      (utilitySecond true true > utilitySecond true false ∧
        utilitySecond false false > utilitySecond false true) ∧
      (∀ doctrine leftAction rightAction,
        (utilityFirst doctrine leftAction > utilityFirst doctrine rightAction) ↔
          (utilitySecond doctrine leftAction > utilitySecond doctrine rightAction)) ∧
      (probability true * utilityFirst true true +
          probability false * utilityFirst false true = alphaFirst / 2 ∧
        probability true * utilityFirst true false +
          probability false * utilityFirst false false = betaFirst / 2) ∧
      (probability true * utilitySecond true true +
          probability false * utilitySecond false true = alphaSecond / 2 ∧
        probability true * utilitySecond true false +
          probability false * utilitySecond false false = betaSecond / 2) ∧
      (probability true * utilityFirst true true +
          probability false * utilityFirst false true >
        probability true * utilityFirst true false +
          probability false * utilityFirst false false) ∧
      (probability true * utilitySecond true false +
          probability false * utilitySecond false false >
        probability true * utilitySecond true true +
          probability false * utilitySecond false true) ∧
      ((({action : Bool | metaData.permission true action} : Set Bool) ∩
          ({action : Bool | metaData.permission false action} : Set Bool)) = ∅ ->
        ¬ ∃ action,
          action ∈ (({action : Bool | metaData.permission true action} : Set Bool) ∩
            ({action : Bool | metaData.permission false action} : Set Bool))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact probabilityHalf
  · exact firstCoordinates
  · exact secondCoordinates
  · constructor
    · rw [firstCoordinates.1, firstCoordinates.2.1]
      exact alphaFirstPositive
    · rw [firstCoordinates.2.2.2, firstCoordinates.2.2.1]
      exact betaFirstPositive
  · constructor
    · rw [secondCoordinates.1, secondCoordinates.2.1]
      exact alphaSecondPositive
    · rw [secondCoordinates.2.2.2, secondCoordinates.2.2.1]
      exact betaSecondPositive
  · intro doctrine leftAction rightAction
    cases doctrine <;> cases leftAction <;> cases rightAction
    all_goals
      simp only [firstCoordinates.1, firstCoordinates.2.1,
        firstCoordinates.2.2.1, firstCoordinates.2.2.2,
        secondCoordinates.1, secondCoordinates.2.1,
        secondCoordinates.2.2.1, secondCoordinates.2.2.2]
    all_goals
      constructor <;> intro h <;>
        linarith [alphaFirstPositive, betaFirstPositive,
          alphaSecondPositive, betaSecondPositive]
  · constructor
    · simp only [probabilityHalf true, probabilityHalf false,
        firstCoordinates.1, firstCoordinates.2.2.1]
      ring
    · simp only [probabilityHalf true, probabilityHalf false,
        firstCoordinates.2.1, firstCoordinates.2.2.2]
      ring
  · constructor
    · simp only [probabilityHalf true, probabilityHalf false,
        secondCoordinates.1, secondCoordinates.2.2.1]
      ring
    · simp only [probabilityHalf true, probabilityHalf false,
        secondCoordinates.2.1, secondCoordinates.2.2.2]
      ring
  · simp only [probabilityHalf true, probabilityHalf false,
      firstCoordinates.1, firstCoordinates.2.1,
      firstCoordinates.2.2.1, firstCoordinates.2.2.2]
    nlinarith [firstChoosesA]
  · simp only [probabilityHalf true, probabilityHalf false,
      secondCoordinates.1, secondCoordinates.2.1,
      secondCoordinates.2.2.1, secondCoordinates.2.2.2]
    nlinarith [secondChoosesB]
  · intro h
    intro hExists
    rcases hExists with ⟨action, hCommon⟩
    rcases hCommon with ⟨hFirst, hSecond⟩
    have hCommon :
        action ∈ ({action : Bool | metaData.permission true action} : Set Bool) ∩
          ({action : Bool | metaData.permission false action} : Set Bool) :=
      ⟨hFirst, hSecond⟩
    rw [commonPermissionEmpty] at hCommon
    exact hCommon

#print axioms normative_scale_choice_reversal_with_metanormative_data

end D5.S3.ConceptDynamics.DecisionValueScale.NormativeScaleChoiceReversalWithMeta
