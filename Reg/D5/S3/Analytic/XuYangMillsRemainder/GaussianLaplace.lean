import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.XuYangMillsRemainder.GaussianLaplace
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter
open _root_.D5.S3.Analytic.XuYangMillsRemainder.Result
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Real MeasureTheory

namespace Reg.D5.S3.Analytic.XuYangMillsRemainder.GaussianLaplace
noncomputable section

namespace GaussianKernelIdentity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ y => y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ y => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law S := ∀ a t : ℝ, G a (S.readout () a t) = t ^ 3 / 4 * ∫ v in (0 : ℝ)..1,
    (1 + (2 * a - 1) * v ^ 2) * exp (-(1 + v ^ 2) * t ^ 2 / 4)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro H
  have hp : 0 < ∫ v in (0 : ℝ)..1,
      (1 - v ^ 2) * exp (-(1 + v ^ 2) / 4) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (by apply Continuous.intervalIntegrable; fun_prop) _ (by norm_num)
    intro v hv
    apply mul_pos _ (exp_pos _)
    nlinarith [hv.1, hv.2]
  have he : (0 : ℝ) = (1 / 4 : ℝ) * ∫ v in (0 : ℝ)..1,
      (1 - v ^ 2) * exp (-(1 + v ^ 2) / 4) := by
    simpa [rejected, realize, G, sub_eq_add_neg] using H 0 1
  nlinarith

def family : Registration arena (type_of% @gaussian_kernel_identity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@gaussian_kernel_identity, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    exact ⟨0, 0, 1, by norm_num [actual, realize]⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gaussian_kernel_identity) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.GaussianLaplace.GaussianKernelIdentity.unit
  realizationName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.GaussianLaplace.GaussianKernelIdentity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ y => y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.XuYangMillsRemainder.GaussianLaplace
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end GaussianKernelIdentity

namespace GaussianLaplaceIdentity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ y => y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ y => y + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law S := ∀ (a : ℝ) {x : ℝ}, 0 < x →
    Y (S.readout () () a) (a - 2) x - (a - 1) =
      ∫ t in Ioi (0 : ℝ), exp (-x * t) * G a t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro H
  have hi : Integrable (fun t : ℝ => exp (-t ^ 2 / 2)) := by
    convert integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2) using 1
    ext t
    congr 1
    ring
  have hm : 0 < millsRatio 1 := by
    unfold millsRatio
    apply mul_pos (exp_pos _) _
    apply (integral_pos_iff_support_of_nonneg (fun t => (exp_pos _).le)
      (hi.integrableOn (s := Ioi 1))).2
    simp [Function.support, exp_ne_zero]
  have h := H 0 (x := 1) (by norm_num)
  have good := gaussian_laplace_identity 0 (x := 1) (by norm_num)
  change Y (0 + 1) (0 - 2) 1 - (0 - 1) = _ at h
  unfold Y at h good
  nlinarith [sq_pos_of_pos hm]

def family : Registration arena (type_of% @gaussian_laplace_identity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@gaussian_laplace_identity, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gaussian_laplace_identity) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.GaussianLaplace.GaussianLaplaceIdentity.unit
  realizationName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.GaussianLaplace.GaussianLaplaceIdentity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ y => y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.XuYangMillsRemainder.GaussianLaplace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end GaussianLaplaceIdentity

end
end Reg.D5.S3.Analytic.XuYangMillsRemainder.GaussianLaplace
