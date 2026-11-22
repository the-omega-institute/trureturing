import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.StieltjesEndpointL2
import Reg.Support.SingleDependentReadout

/-! Source-bound bounds for scalar, norm and polynomial Stieltjes readouts. -/

noncomputable section

open LeanInformationAudit MeasureTheory Set
open _root_.D5.S3.Analytic.StieltjesEndpointL2
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Interval Polynomial

namespace Reg.D5.S3.Analytic.StieltjesEndpointL2

universe u

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (show ¬ (1 : ℝ) ≤ 0 by norm_num) ((congrFun h 0).mp le_rfl)

private theorem zero_norm_cap {E : Type u} [NormedAddCommGroup E] :
    ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(0 : E)‖ ≤ 1 / Real.sqrt 1 * l2Norm 1 (fun _ : ℝ => ‖(0 : E)‖) := by
  simp [l2Norm]

namespace ScalarEndpoint

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {b M : ℝ} (_hb : 0 < b) (_hM : 1 ≤ M) {q : ℝ → ℝ}
    (_hq : ContinuousOn q (Icc 0 b)) (_hq0 : ∀ t ∈ Icc 0 b, 0 ≤ q t)
    (_hcap : ∀ t ∈ Icc 0 b, q t ≤ M / Real.sqrt b * l2Norm b q),
    R.readout () () (∫ t in (0 : ℝ)..b, q t / Real.sqrt t)
      ((2 + Real.sqrt (2 * Real.log M)) * l2Norm b q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (b := 1) (M := 1) zero_lt_one le_rfl (q := fun _ => 0)
    continuousOn_const (by simp) (by simpa using zero_norm_cap (E := ℝ))

def family : Registration arena (type_of% @integral_div_sqrt_le_of_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integral_div_sqrt_le_of_pos, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integral_div_sqrt_le_of_pos) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.StieltjesEndpointL2.integral_div_sqrt_le_of_pos.__information_unit
  realizationName := `Reg.D5.S3.Analytic.StieltjesEndpointL2.ScalarEndpoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.StieltjesEndpointL2
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ScalarEndpoint

namespace NormProfile

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] {b M : ℝ} (_hb : 0 < b) (_hM : 1 ≤ M)
    {F : ℝ → E} (_hF : ContinuousOn F (Icc 0 b))
    (_hcap : ∀ t ∈ Icc 0 b, ‖F t‖ ≤ M / Real.sqrt b * l2Norm b (fun r => ‖F r‖)),
    IntervalIntegrable (fun t => stieltjesWeight t * ‖F t‖) volume 0 b ∧
      R.readout () () (∫ t in (0 : ℝ)..b, stieltjesWeight t * ‖F t‖)
        ((2 + Real.sqrt (2 * Real.log M)) * l2Norm b (fun t => ‖F t‖))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact (h (E := ULift.{u} ℝ) (b := 1) (M := 1) zero_lt_one le_rfl (F := fun _ => 0)
    continuousOn_const zero_norm_cap).2

def family : Registration arena.{u} (type_of% @integral_stieltjes_mul_norm_le.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integral_stieltjes_mul_norm_le.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integral_stieltjes_mul_norm_le.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.StieltjesEndpointL2.integral_stieltjes_mul_norm_le.__information_unit
  realizationName := `Reg.D5.S3.Analytic.StieltjesEndpointL2.NormProfile.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.StieltjesEndpointL2
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NormProfile

namespace BochnerIntegral

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {b M : ℝ} (_hb : 0 < b) (_hM : 1 ≤ M) {F : ℝ → E}
    (_hF : ContinuousOn F (Icc 0 b))
    (_hcap : ∀ t ∈ Icc 0 b, ‖F t‖ ≤ M / Real.sqrt b * l2Norm b (fun r => ‖F r‖)),
    IntervalIntegrable (fun t => stieltjesWeight t • F t) volume 0 b ∧
      R.readout () () ‖∫ t in (0 : ℝ)..b, stieltjesWeight t • F t‖
        ((2 + Real.sqrt (2 * Real.log M)) * l2Norm b (fun t => ‖F t‖))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact (h (E := ULift.{u} ℝ) (b := 1) (M := 1) zero_lt_one le_rfl (F := fun _ => 0)
    continuousOn_const zero_norm_cap).2

def family : Registration arena.{u} (type_of% @norm_integral_stieltjes_smul_le.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@norm_integral_stieltjes_smul_le.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@norm_integral_stieltjes_smul_le.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.StieltjesEndpointL2.norm_integral_stieltjes_smul_le.__information_unit
  realizationName := `Reg.D5.S3.Analytic.StieltjesEndpointL2.BochnerIntegral.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.StieltjesEndpointL2
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end BochnerIntegral

namespace PolynomialCap

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) (p : ℂ[X]) (_hp : p.degree < (d : WithBot ℕ))
    {x : ℝ} (_hx : x ∈ Icc (0 : ℝ) 1),
    R.readout () () ‖p.eval (x : ℂ)‖ ((1 + (d : ℝ) ^ 2) * l2Norm 1 (fun t => ‖p.eval (t : ℂ)‖))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 (by simp) (x := 0) ⟨le_rfl, zero_le_one⟩

def family : Registration arena (type_of% @polynomial_norm_le_cap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@polynomial_norm_le_cap, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@polynomial_norm_le_cap) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.StieltjesEndpointL2.polynomial_norm_le_cap.__information_unit
  realizationName := `Reg.D5.S3.Analytic.StieltjesEndpointL2.PolynomialCap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.StieltjesEndpointL2
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PolynomialCap

namespace PolynomialIntegral

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) (p : ℂ[X]) (_hp : p.degree < (d : WithBot ℕ)),
    IntervalIntegrable (fun t : ℝ => stieltjesWeight t * ‖p.eval (t : ℂ)‖) volume 0 1 ∧
      R.readout () () (∫ t in (0 : ℝ)..1, stieltjesWeight t * ‖p.eval (t : ℂ)‖)
        ((2 + Real.sqrt (2 * Real.log (1 + (d : ℝ) ^ 2))) *
          l2Norm 1 (fun t => ‖p.eval (t : ℂ)‖))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h 0 0 (by simp)).2

def family : Registration arena (type_of% @integral_stieltjes_polynomial_norm_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integral_stieltjes_polynomial_norm_le, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integral_stieltjes_polynomial_norm_le) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.StieltjesEndpointL2.integral_stieltjes_polynomial_norm_le.__information_unit
  realizationName := `Reg.D5.S3.Analytic.StieltjesEndpointL2.PolynomialIntegral.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.StieltjesEndpointL2
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PolynomialIntegral

end Reg.D5.S3.Analytic.StieltjesEndpointL2
