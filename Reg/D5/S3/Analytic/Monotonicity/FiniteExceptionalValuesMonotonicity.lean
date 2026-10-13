import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Monotonicity.FiniteExceptionalValuesMonotonicity
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import Mathlib.Tactic.NormNum

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Monotonicity.FiniteExceptionalValuesMonotonicity
open LeanInformationAudit Set

noncomputable section
namespace Reg.D5.S3.Analytic.Monotonicity.FiniteExceptionalValuesMonotonicity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (ℝ → ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ f t => f t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ t => -t) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {f : ℝ → ℝ} {a b : ℝ} {S : Set ℝ} (hS : S.Finite)
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, f t ∉ S →
      ∃ r : ℝ, HasDerivAt f r t ∧ 0 ≤ r),
    MonotoneOn (R.readout () f) (Icc a b)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, (fun _ : ℝ => (0 : ℝ)) t ∉ (∅ : Set ℝ) →
      ∃ r : ℝ, HasDerivAt (fun _ : ℝ => (0 : ℝ)) r t ∧ 0 ≤ r := by
    intro t _ _
    exact ⟨0, hasDerivAt_const t 0, le_rfl⟩
  have hmono : MonotoneOn (fun t : ℝ => -t) (Icc (0 : ℝ) 1) :=
    h (f := fun _ : ℝ => (0 : ℝ)) (a := 0) (b := 1) (S := ∅)
      Set.finite_empty continuousOn_const hderiv
  have hle := hmono (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) (by norm_num)
  norm_num at hle

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(fun t : ℝ => t), 0, 1, ?_⟩
  change (0 : ℝ) ≠ 1
  exact zero_ne_one

def evidence : Registration arena
    (type_of% (@monotoneOn_Icc_of_hasDerivAt_nonneg_off_finite_values)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@monotoneOn_Icc_of_hasDerivAt_nonneg_off_finite_values,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Monotonicity.FiniteExceptionalValuesMonotonicity.monotoneOn_Icc_of_hasDerivAt_nonneg_off_finite_values)
    (type_of% (realize signature (fun _ f t => f t) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Monotonicity.FiniteExceptionalValuesMonotonicity.monotonicity_unit
  realizationName := `Reg.D5.S3.Analytic.Monotonicity.FiniteExceptionalValuesMonotonicity.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ f t => f t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Monotonicity.FiniteExceptionalValuesMonotonicity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Analytic.Monotonicity.FiniteExceptionalValuesMonotonicity
