import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ArithmeticMixedCornerResponse
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.ArithmeticMixedCornerResponse

open _root_.D5.S3.Arith.Robin.ArithmeticMixedCornerResponse
open _root_.D5.S3.Arith.Robin.ActualRobinClockCovariance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- The complete arithmetic law observes one kernel on its full real domain. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n r s : ℕ}, 3 ≤ n → 2 ≤ r → 2 ≤ s → Nat.Coprime r s →
    let x := Real.log (n : ℝ)
    let a := Real.log (r : ℝ)
    let b := Real.log (s : ℝ)
    let J := G (n * r * s) + G n - G (n * r) - G (n * s)
    1 < x ∧ 0 < a ∧ 0 < b ∧
    J = (∫ u in 0..a, ∫ v in 0..b, R.readout () () (x + u + v)) ∧
    0 < J ∧ a * b * activationDensity (x + a + b) ≤ J ∧
      J ≤ a * b * activationDensity x

def actual : Realization signature :=
  realize signature (fun _ _ t => activationDensity t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (n := 3) (r := 2) (s := 3) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  dsimp only at hbad
  have hz := hbad.2.2.2.1
  have hp := hbad.2.2.2.2.1
  simp only [rejected, realize, intervalIntegral.integral_zero] at hz
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _i
  refine ⟨(), 2, 3, ?_⟩
  change activationDensity 2 ≠ activationDensity 3
  have hp : 0 < activationDensity 3 := by
    have h := _root_.D5.S3.Arith.Robin.LogLogHigherDerivative.positiveKernel_pos
      1 0 0 (by norm_num : (1 : ℝ) < 3)
    have hl0 : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 3)).ne'
    have he : activationDensity 3 =
        _root_.D5.S3.Arith.Robin.LogLogHigherDerivative.positiveKernel 1 0 0 3 := by
      norm_num [activationDensity,
        _root_.D5.S3.Arith.Robin.LogLogHigherDerivative.positiveKernel]
      field_simp [hl0]
    exact he.symm ▸ h
  have h := _root_.D5.S3.Arith.Robin.MellinWeightedVariation.scaleWeight_antitone
    (x := 2) (y := 1) (a := 2) (b := 3) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  rw [_root_.D5.S3.Arith.Robin.MellinWeightedVariation.scaleWeight_eq,
    _root_.D5.S3.Arith.Robin.MellinWeightedVariation.scaleWeight_eq] at h
  simp only [mul_one] at h
  change 3 * activationDensity 3 ≤ 2 * activationDensity 2 at h
  intro he
  rw [he] at h
  linarith

def family : Registration arena (type_of% (@arithmetic_mixed_response)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@arithmetic_mixed_response, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@arithmetic_mixed_response)
    (type_of% (realize signature (fun _ _ t => activationDensity t) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.Arith.Robin.ArithmeticMixedCornerResponse.arithmetic_mixed_response.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ArithmeticMixedCornerResponse.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => activationDensity t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ArithmeticMixedCornerResponse
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg", "arg",
        "fn", "fn", "fn", "arg", "body", "fn", "fn", "fn", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

end Reg.D5.S3.Arith.Robin.ArithmeticMixedCornerResponse
