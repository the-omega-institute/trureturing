import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.XuYangMillsRemainder.NormalizedRemainderOrders
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter
open _root_.D5.S3.Analytic.XuYangMillsRemainder.Result
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Real MeasureTheory

namespace Reg.D5.S3.Analytic.XuYangMillsRemainder.NormalizedRemainderOrders
noncomputable section

namespace ExpRemainderRatioStrictAnti

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ y => y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ y => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law S := ∀ r : ℕ, StrictAntiOn (fun y : ℝ =>
    (-1 : ℝ) ^ (r + 1) * _root_.D5.S3.Analytic.ExpRemainderDifferences.R r (-(S.readout () r y)) /
      y ^ (r + 1)) (Ioi 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro H
  have h := H 0 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Ioi 0 by norm_num) (by norm_num : (1 : ℝ) < 2)
  norm_num [rejected, realize, _root_.D5.S3.Analytic.ExpRemainderDifferences.R] at h

def family : Registration arena (type_of% @exp_remainder_ratio_strict_anti) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exp_remainder_ratio_strict_anti, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    exact ⟨0, 0, 1, by norm_num [actual, realize]⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exp_remainder_ratio_strict_anti) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.NormalizedRemainderOrders.ExpRemainderRatioStrictAnti.unit
  realizationName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.NormalizedRemainderOrders.ExpRemainderRatioStrictAnti.family
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
    owner := `D5.S3.Analytic.XuYangMillsRemainder.NormalizedRemainderOrders
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "body", "fn", "arg", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ExpRemainderRatioStrictAnti

namespace ExpRemainderRatioStrictMono

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ y => y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ y => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law S := ∀ r : ℕ, StrictMonoOn (fun y : ℝ =>
    (-1 : ℝ) ^ (r + 1) * _root_.D5.S3.Analytic.ExpRemainderDifferences.R r (-(S.readout () r y)) /
      y ^ r) (Ioi 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro H
  have h := H 0 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Ioi 0 by norm_num) (by norm_num : (1 : ℝ) < 2)
  norm_num [rejected, realize, _root_.D5.S3.Analytic.ExpRemainderDifferences.R] at h

def family : Registration arena (type_of% @exp_remainder_ratio_strict_mono) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exp_remainder_ratio_strict_mono, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    exact ⟨0, 0, 1, by norm_num [actual, realize]⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exp_remainder_ratio_strict_mono) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.NormalizedRemainderOrders.ExpRemainderRatioStrictMono.unit
  realizationName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.NormalizedRemainderOrders.ExpRemainderRatioStrictMono.family
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
    owner := `D5.S3.Analytic.XuYangMillsRemainder.NormalizedRemainderOrders
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "body", "fn", "arg", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ExpRemainderRatioStrictMono

namespace NormalizedExpRemainder

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ y => y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ y => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law S := ∀ (r : ℕ) {y : ℝ}, 0 < y →
    (-1 : ℝ) ^ (r + 1) * _root_.D5.S3.Analytic.ExpRemainderDifferences.R r (-(S.readout () r y)) /
      y ^ (r + 1) =
      (∫ s in (0 : ℝ)..1, (1 - s) ^ r * exp (-s * y)) / r.factorial

private theorem rejected_law : ¬ arena.Law rejected := by
  intro H
  have hp : 0 < ∫ s in (0 : ℝ)..1, exp (-s) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (by apply Continuous.intervalIntegrable; fun_prop) _ (by norm_num)
    intro s _
    exact exp_pos _
  have he : (0 : ℝ) = ∫ s in (0 : ℝ)..1, exp (-s) := by
    simpa [rejected, realize, _root_.D5.S3.Analytic.ExpRemainderDifferences.R] using H 0 (y := 1) (by norm_num)
  exact (ne_of_gt hp) he.symm

def family : Registration arena (type_of% @normalized_exp_remainder) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalized_exp_remainder, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    exact ⟨0, 0, 1, by norm_num [actual, realize]⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@normalized_exp_remainder) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.NormalizedRemainderOrders.NormalizedExpRemainder.unit
  realizationName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.NormalizedRemainderOrders.NormalizedExpRemainder.family
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
    owner := `D5.S3.Analytic.XuYangMillsRemainder.NormalizedRemainderOrders
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NormalizedExpRemainder

end
end Reg.D5.S3.Analytic.XuYangMillsRemainder.NormalizedRemainderOrders
