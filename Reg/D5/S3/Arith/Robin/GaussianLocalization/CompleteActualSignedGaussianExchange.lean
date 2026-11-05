import D5.S3.Arith.Robin.GaussianLocalization.CompleteActualSignedGaussianExchange
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Arith.Robin.GaussianLocalization.CompleteActualSignedGaussianExchange
open _root_.D5.S3.Arith.Robin.CompleteActualSignedGaussianExchange
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    ({m : ℝ // 0 < m} × ℝ) (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ p ρ => ∫ y : ℝ, Complex.exp (ρ * (y : ℂ)) * gaussianW p.1.1 p.2 y)
  (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℂ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m γ : ℝ) (hm : 0 < m) (ρ : ℂ),
    R.readout () (⟨m, hm⟩, γ) ρ =
      -ρ * (ρ - 1) * Complex.exp
        ((m : ℂ) * (ρ - Complex.I * γ) ^ 2 +
          (16 * (m : ℂ)) * (ρ - Complex.I * γ))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h 1 0 (by norm_num) 2
  change (0 : ℂ) = -(2 : ℂ) * (2 - 1) * Complex.exp
    ((1 : ℂ) * (2 - Complex.I * 0) ^ 2 + (16 * (1 : ℂ)) * (2 - Complex.I * 0)) at hz
  exact (mul_ne_zero (by norm_num : -(2 : ℂ) * (2 - 1) ≠ 0)
    (Complex.exp_ne_zero _)) hz.symm

theorem actual_law : arena.Law actual := by
  intro m γ hm ρ
  exact gaussianW_transform m γ hm ρ

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(⟨1, by norm_num⟩, 0), 0, 2, ?_⟩
  change (∫ y : ℝ, Complex.exp ((0 : ℂ) * (y : ℂ)) * gaussianW 1 0 y) ≠
    (∫ y : ℝ, Complex.exp ((2 : ℂ) * (y : ℂ)) * gaussianW 1 0 y)
  rw [gaussianW_transform 1 0 (by norm_num) 0,
    gaussianW_transform 1 0 (by norm_num) 2]
  simp only [neg_zero, zero_mul]
  exact Ne.symm (mul_ne_zero (by norm_num : -(2 : ℂ) * (2 - 1) ≠ 0)
    (Complex.exp_ne_zero _))

def source_registration : Registration arena (type_of% @gaussianW_transform) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gaussianW_transform) (Realization signature) Unit Unit where
  unitName := `GaussianLocalization.gaussianW_transform
  realizationName := `Reg.D5.S3.Arith.Robin.GaussianLocalization.CompleteActualSignedGaussianExchange.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p ρ => ∫ y : ℝ, Complex.exp (ρ * (y : ℂ)) * gaussianW p.1.1 p.2 y)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GaussianLocalization.CompleteActualSignedGaussianExchange
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Arith.Robin.GaussianLocalization.CompleteActualSignedGaussianExchange
