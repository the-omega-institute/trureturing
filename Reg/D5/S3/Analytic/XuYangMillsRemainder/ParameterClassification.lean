import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.XuYangMillsRemainder.ParameterClassification
import Reg.D5.S3.Analytic.XuYangMillsRemainder.Result
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.XuYangMillsRemainder.ParameterClassification
open _root_.D5.S3.Analytic.XuYangMillsRemainder.Result
open _root_.D5.S3.Analytic.XuYangMillsRemainder.ParameterClassification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set Real MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def classifications (n : ℕ) (a : ℝ) (f : ℝ → ℝ) : Prop :=
  (((∀ x : ℝ, 0 < x → 0 ≤ f x) ↔ CompletelyMonotoneOn f) ∧
    (CompletelyMonotoneOn f ↔ a ≤ theta (n - 2))) ∧
  (((∀ x : ℝ, 0 < x → 0 ≤ -f x) ↔ CompletelyMonotoneOn (fun x => -f x)) ∧
    (CompletelyMonotoneOn (fun x => -f x) ↔ theta (n - 1) ≤ a))

def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 2 ≤ n → ∀ a : ℝ,
    classifications n a (fun x => (-1 : ℝ) ^ n * D n (R.readout () () x) a)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha : (-1 : ℝ) ≤ theta 1 := by
    have hc := _root_.D5.S3.Analytic.XuYangMillsRemainder.Result.result 3 (by norm_num)
    exact (_root_.D5.S3.Analytic.XuYangMillsRemainder.ParameterClassification.result
      3 (by norm_num) (-1)).1.2.mp hc
  have hc := (h 3 (by norm_num) (-1)).1.2.mpr ha
  have hzero := hc.2 0 1 (by norm_num)
  change 0 ≤ (-1 : ℝ) ^ 0 * iteratedDeriv 0
    (fun _ : ℝ => (-1 : ℝ) ^ 3 * D 3 (-1) (-1)) 1 at hzero
  norm_num only [iteratedDeriv_zero, pow_zero, one_mul, pow_succ] at hzero
  rw [Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.D_three_neg_one] at hzero
  nlinarith [Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.mills_neg_one_pos]

def source_registration : Registration arena
    (type_of% @_root_.D5.S3.Analytic.XuYangMillsRemainder.ParameterClassification.result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.XuYangMillsRemainder.ParameterClassification.result,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 0, 1, by simp [actual, realize]⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Analytic.XuYangMillsRemainder.ParameterClassification.result)
      (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.ParameterClassification.unit
  realizationName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.ParameterClassification.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.XuYangMillsRemainder.ParameterClassification
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "body", "body", "arg", "arg", "fn", "arg"]
        stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg", "body", "arg", "fn", "arg"]
        stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "fn", "arg", "arg", "fn", "arg", "arg", "body", "arg", "fn", "arg"]
        stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "arg", "fn", "arg", "fn", "arg", "body", "body", "arg", "arg", "arg", "fn", "arg"]
        stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "arg", "fn", "arg", "arg", "arg", "body", "arg", "arg", "fn", "arg"]
        stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "arg", "arg", "fn", "arg", "arg", "body", "arg", "arg", "fn", "arg"]
        stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false } ] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.XuYangMillsRemainder.ParameterClassification
