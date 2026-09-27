import D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError
import Reg.Support.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError

open _root_.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory
open scoped Interval NNReal

noncomputable section

local instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

def signature : Signature where
  Params := ℝ≥0
  State _ := AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun (_ : Unit) (_ : ℝ≥0)
      (s : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)) =>
      (∫ x : AddCircle (2 * Real.pi), circle_error s x ∂AddCircle.haarAddCircle : ℝ))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

def lowerArena : Arena where
  signature := signature
  Law R := ∀ (L : ℝ≥0)
    (s : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)),
    LipschitzWith L s → 2 / (2 * (L : ℝ) + 1) ≤ R.readout () L s

def sharpArena : Arena where
  signature := signature
  Law R := ∀ (L : ℝ≥0), (1 / 2 : ℝ) ≤ (L : ℝ) →
    ∃ s : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi),
      LipschitzWith L s ∧ R.readout () L s = 2 / (2 * (L : ℝ) + 1)

theorem lower_rejected : ¬ lowerArena.Law rejected := by
  intro h
  let witness := sharpness (1 : ℝ≥0) (by norm_num)
  let s := Classical.choose witness
  have hs := (Classical.choose_spec witness).1
  have hc := h (1 : ℝ≥0) s hs
  change (2 : ℝ) / (2 * (1 : ℝ) + 1) ≤ 0 at hc
  norm_num at hc

theorem sharp_rejected : ¬ sharpArena.Law rejected := by
  intro h
  obtain ⟨s, _, hs⟩ := h (1 : ℝ≥0) (by norm_num)
  change (0 : ℝ) = 2 / (2 * (1 : ℝ) + 1) at hs
  norm_num at hs

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  let w₁ := sharpness (1 : ℝ≥0) (by norm_num)
  let w₂ := sharpness (2 : ℝ≥0) (by norm_num)
  let s₁ := Classical.choose w₁
  let s₂ := Classical.choose w₂
  have h₁ := (Classical.choose_spec w₁).2
  have h₂ := (Classical.choose_spec w₂).2
  refine ⟨(0 : ℝ≥0), s₁, s₂, ?_⟩
  change (∫ x : AddCircle (2 * Real.pi), circle_error s₁ x ∂AddCircle.haarAddCircle) ≠
    (∫ x : AddCircle (2 * Real.pi), circle_error s₂ x ∂AddCircle.haarAddCircle)
  rw [h₁, h₂]
  norm_num

def lowerRegistration : Registration lowerArena
    (∀ (L : ℝ≥0) (s : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)),
      LipschitzWith L s →
        2 / (2 * (L : ℝ) + 1) ≤
          ∫ x : AddCircle (2 * Real.pi), circle_error s x ∂AddCircle.haarAddCircle) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro L s hs; exact lower_bound L s hs, rejected, lower_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, lower_rejected⟩
      intro j hj
      have hji : j = i := by cases j; cases i; rfl
      exact False.elim (hj hji)
    · intro i
      exact nomatch i
  dependence := actual_dependence

def sharpRegistration : Registration sharpArena
    (∀ (L : ℝ≥0), (1 / 2 : ℝ) ≤ (L : ℝ) →
      ∃ s : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi),
        LipschitzWith L s ∧
        (∫ x : AddCircle (2 * Real.pi), circle_error s x ∂AddCircle.haarAddCircle) =
          2 / (2 * (L : ℝ) + 1)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro L hL; exact sharpness L hL, rejected, sharp_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, sharp_rejected⟩
      intro j hj
      have hji : j = i := by cases j; cases i; rfl
      exact False.elim (hj hji)
    · intro i
      exact nomatch i
  dependence := actual_dependence

register_information_theorem lower_bound in lowerArena
  readout via (realize signature
    (fun (_ : Unit) (_ : ℝ≥0)
      (s : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)) =>
      (∫ x : AddCircle (2 * Real.pi), circle_error s x ∂AddCircle.haarAddCircle : ℝ))
    (fun e => nomatch e))
  realizes lowerRegistration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

register_information_theorem sharpness in sharpArena
  readout via (realize signature
    (fun (_ : Unit) (_ : ℝ≥0)
      (s : AddCircle (2 * Real.pi) → AddCircle (2 * Real.pi)) =>
      (∫ x : AddCircle (2 * Real.pi), circle_error s x ∂AddCircle.haarAddCircle : ℝ))
    (fun e => nomatch e))
  realizes sharpRegistration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 2 }] })
  escape continues (open)

#print axioms lowerRegistration
#print axioms sharpRegistration

end

end Reg.D5.S3.ConceptDynamics.Topology.CircleDoubleCoverLipschitzError
