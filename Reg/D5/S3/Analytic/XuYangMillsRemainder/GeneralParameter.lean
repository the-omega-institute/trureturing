import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter
import Reg.Support.SingleDependentReadout

/-! Whole-source registration for the complete original Mills classification. -/

namespace Reg.D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter

open _root_.D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter
open _root_.D5.S3.Analytic.XuYangMillsRemainder.Result
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ a => a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ a => a - 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 2 ≤ n → ∀ a : ℝ,
    ((globalNonnegative n a ↔ completelyMonotone n a) ∧
      (completelyMonotone n a ↔ R.readout () () a ≤ theta (n - 2))) ∧
    ((globalNonpositive n a ↔ CompletelyMonotoneOn (fun x => -F n a x)) ∧
      (CompletelyMonotoneOn (fun x => -F n a x) ↔ a ≥ theta (n - 1)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc : completelyMonotone 2 (theta 0 + 1) :=
    ((h 2 (by norm_num) (theta 0 + 1)).1.2).mpr (by
      change theta 0 + 1 - 1 ≤ theta 0
      linarith)
  have hb : theta 0 + 1 ≤ theta 0 := by
    simpa only [Nat.sub_self] using
      ((_root_.D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter.result
        2 (by norm_num) (theta 0 + 1)).1.2).mp hc
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩

def source_registration : Registration arena theorem21 where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter.result,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter.unit
  realizationName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter
    definition := some {
      owner := `D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter
      name := `D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter.theorem21
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter
