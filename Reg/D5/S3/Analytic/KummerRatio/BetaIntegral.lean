import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.KummerRatio.BetaIntegral
import Reg.D5.S3.Analytic.KummerRatio.Series
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-! Registration of beta moments, density integrability, and the Kummer integral formula. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.KummerRatio.Defs
open _root_.D5.S3.Analytic.KummerRatio.Series
open _root_.D5.S3.Analytic.KummerRatio.BetaIntegral
open LeanInformationAudit MeasureTheory
open scoped Real BigOperators
noncomputable section
namespace Reg.D5.S3.Analytic.KummerRatio.BetaIntegral
namespace Moment
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature
  (fun _ p q => ∫ t in (0:ℝ)..1, t^(p-1) * (1-t)^(q-1)) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {p q : ℝ}, 0 < p → 0 < q → R.readout () p q =
    Real.Gamma p * Real.Gamma q / Real.Gamma (p+q)
private theorem gamma_two : Real.Gamma 2 = 1 := by
  simpa using Real.Gamma_nat_eq_factorial 1
private theorem gamma_three : Real.Gamma 3 = 2 := by
  simpa using Real.Gamma_nat_eq_factorial 2
private theorem rejected_law : ¬ arena.Law bad := by
  intro h
  have H := h (p:=1) (q:=1) zero_lt_one zero_lt_one
  norm_num [bad, realize, gamma_two, Real.Gamma_one] at H
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, 2, ?_⟩
  change (∫ t in (0:ℝ)..1, t^((1:ℝ)-1) * (1-t)^((1:ℝ)-1)) ≠
    (∫ t in (0:ℝ)..1, t^((1:ℝ)-1) * (1-t)^((2:ℝ)-1))
  rw [integral_beta zero_lt_one zero_lt_one, integral_beta zero_lt_one (by norm_num)]
  norm_num [gamma_two, gamma_three, Real.Gamma_one]
def family : Registration arena (type_of% (@integral_beta)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integral_beta, bad, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad rejected_law
  dependence := actual_dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integral_beta) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KummerRatio.BetaIntegral.Moment.unit
  realizationName := `Reg.D5.S3.Analytic.KummerRatio.BetaIntegral.Moment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p q => ∫ t in (0:ℝ)..1, t^(p-1) * (1-t)^(q-1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KummerRatio.BetaIntegral
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Moment

namespace Integrability
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature
  (fun _ p t => t^(p.1-1) * (1-t)^(p.2-1)) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ t => t⁻¹) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {p q : ℝ}, 0 < p → 0 < q →
    IntervalIntegrable (fun t => R.readout () ⟨p,q⟩ t) volume 0 1
private theorem rejected_law : ¬ arena.Law bad := by
  intro h
  have H := h (p:=1) (q:=1) zero_lt_one zero_lt_one
  change IntervalIntegrable (fun t : ℝ => t⁻¹) volume 0 1 at H
  norm_num [intervalIntegrable_inv_iff] at H
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2,1⟩, 0, 1, ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% (@intervalIntegrable_beta)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@intervalIntegrable_beta, bad, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad rejected_law
  dependence := actual_dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@intervalIntegrable_beta) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KummerRatio.BetaIntegral.Integrability.unit
  realizationName := `Reg.D5.S3.Analytic.KummerRatio.BetaIntegral.Integrability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p t => t^(p.1-1) * (1-t)^(p.2-1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KummerRatio.BetaIntegral
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn", "fn", "arg", "body"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Integrability

namespace Representation
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature
  (fun _ p x => kummer p.1 p.2 x) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {s c : ℝ}, 0 < s → s < c → ∀ x : ℝ,
    R.readout () ⟨s,c⟩ x = Real.Gamma c / (Real.Gamma s * Real.Gamma (c-s)) *
      ∫ t in (0:ℝ)..1, Real.exp (x*t) * t^(s-1) * (1-t)^(c-s-1)
private theorem rejected_law : ¬ arena.Law bad := by
  intro h
  have H := h (s:=1) (c:=2) zero_lt_one (by norm_num) 0
  have hc := kummer_eq_betaIntegral (s:=1) (c:=2) zero_lt_one (by norm_num) 0
  rw [kummer_zero] at hc
  change (0:ℝ) = _ at H
  rw [← hc] at H
  exact zero_ne_one H
private theorem actual_dependence : ObservationalDependence signature actual :=
  _root_.Reg.D5.S3.Analytic.KummerRatio.Series.Zero.family.dependence

def family : Registration arena (type_of% (@kummer_eq_betaIntegral)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kummer_eq_betaIntegral, bad, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad rejected_law
  dependence := actual_dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kummer_eq_betaIntegral) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KummerRatio.BetaIntegral.Representation.unit
  realizationName := `Reg.D5.S3.Analytic.KummerRatio.BetaIntegral.Representation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p x => kummer p.1 p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KummerRatio.BetaIntegral
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Representation

end Reg.D5.S3.Analytic.KummerRatio.BetaIntegral

end
