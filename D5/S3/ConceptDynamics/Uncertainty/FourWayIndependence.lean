/- GID: D5/S3/ConceptDynamics/Uncertainty/FourWayIndependence
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Uncertainty/FourWayIndependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite source models realize every truth profile of four uncertainty kinds. -/

import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-26):
   * Searches for four-way uncertainty independence and for each source predicate
     found no exact D5 theorem or shared predicate definition.
   * `InformationCompleteNormativeDivergence` is adjacent, but concerns equality
     of normative functions and target factorization rather than opposed rankings.
   * Pinned Mathlib's exact `Function.not_injective_iff` converts evidence-fiber
     collisions to noninjectivity and is applied directly below.
   * The four semantic predicates are exposed as local public constructions from
     evidence, support, compatible predictions, and doctrine preferences; no
     uncertainty predicate is defined to equal its requested truth bit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Uncertainty.FourWayIndependence

/-- Every assignment of truth values to epistemic, aleatoric, model, and
normative uncertainty is realized by finite source-semantic primitives. Hence no
one of the four uncertainty predicates generally implies another. -/
theorem four_uncertainties_have_all_truth_profiles (profile : Fin 4 -> Bool) :
    let evidence : Bool -> Bool := fun state =>
      if profile 0 = true then false else state
    let futureSupport : Bool -> Unit -> Bool -> Prop := fun _ _ outcome =>
      profile 1 = true ∨ outcome = false
    let compatible : Bool -> Prop := fun _ => True
    let prediction : Bool -> Unit -> Bool := fun model _ =>
      if profile 2 = true then model else false
    let prefers : Bool -> Bool -> Bool -> Prop := fun doctrine u v =>
      profile 3 = true ∧
        ((doctrine = false ∧ u = true ∧ v = false) ∨
          (doctrine = true ∧ u = false ∧ v = true))
    let epistemicUncertainty : Prop := ¬Function.Injective evidence
    let aleatoricUncertainty : Prop :=
      ∃ state action first second,
        first ≠ second ∧
          futureSupport state action first ∧ futureSupport state action second
    let modelUncertainty : Prop :=
      ∃ first second target,
        first ≠ second ∧ compatible first ∧ compatible second ∧
          prediction first target ≠ prediction second target
    let normativeUncertainty : Prop :=
      ∃ left right u v,
        left ≠ right ∧ u ≠ v ∧ prefers left u v ∧ prefers right v u
    (epistemicUncertainty ↔ profile 0 = true) ∧
      (aleatoricUncertainty ↔ profile 1 = true) ∧
      (modelUncertainty ↔ profile 2 = true) ∧
      (normativeUncertainty ↔ profile 3 = true) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro notInjective
      by_contra profileFalse
      have evidenceInjective : Function.Injective
          (fun state : Bool => if profile 0 = true then false else state) := by
        simp [profileFalse]
      exact notInjective evidenceInjective
    · intro profileTrue
      apply Function.not_injective_iff.mpr
      exact ⟨false, true, by simp [profileTrue], Bool.false_ne_true⟩
  · constructor
    · rintro ⟨state, action, first, second, distinct, firstSupported, secondSupported⟩
      by_contra profileFalse
      have firstFalse : first = false := by simpa [profileFalse] using firstSupported
      have secondFalse : second = false := by simpa [profileFalse] using secondSupported
      exact distinct (firstFalse.trans secondFalse.symm)
    · intro profileTrue
      exact ⟨false, (), false, true, Bool.false_ne_true,
        Or.inr rfl, Or.inl profileTrue⟩
  · constructor
    · rintro ⟨first, second, target, _, _, _, predictionsDiffer⟩
      by_contra profileFalse
      exact predictionsDiffer (by simp [profileFalse])
    · intro profileTrue
      exact ⟨false, true, (), Bool.false_ne_true, trivial, trivial, by simp [profileTrue]⟩
  · constructor
    · rintro ⟨left, right, u, v, _, _, leftPrefers, _⟩
      exact leftPrefers.1
    · intro profileTrue
      refine ⟨false, true, true, false, Bool.false_ne_true,
        by decide, ?_, ?_⟩
      · exact ⟨profileTrue, Or.inl ⟨rfl, rfl, rfl⟩⟩
      · exact ⟨profileTrue, Or.inr ⟨rfl, rfl, rfl⟩⟩

#print axioms four_uncertainties_have_all_truth_profiles

end D5.S3.ConceptDynamics.Uncertainty.FourWayIndependence
