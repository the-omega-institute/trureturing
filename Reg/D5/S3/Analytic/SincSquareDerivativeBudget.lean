import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.SincSquareDerivativeBudget
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open SincSquareDerivativeBudget LeanInformationAudit
open scoped Nat

noncomputable section
namespace Reg.D5.S3.Analytic.SincSquareDerivativeBudget

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ η t => endpoint η t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {η : ℝ}, 0 < η →
    ContDiff ℝ ⊤ (endpoint η) ∧ R.readout () η 0 = 1 ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ endpoint η t) ∧
      (∀ t : ℝ, 1 ≤ t → endpoint η t ≤ η / 2) ∧
      (∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
        |iteratedDeriv n (endpoint η) t| / (n ! : ℝ) ≤ (8 / η) ^ n / (2 * n)!)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (η := 1) zero_lt_one).2.1
  norm_num [rejected, realize] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change endpoint 1 0 ≠ endpoint 1 1
  obtain ⟨_, hzero, _, htail, _⟩ := endpoint_budget (η := 1) zero_lt_one
  intro heq
  have hbound := htail 1 le_rfl
  rw [← heq, hzero] at hbound
  norm_num at hbound

def evidence : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨endpoint_budget, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.SincSquareDerivativeBudget.endpoint_budget)
    (type_of% (realize signature (fun _ η t => endpoint η t) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.SincSquareDerivativeBudget.endpoint_normalization_unit
  realizationName := `Reg.D5.S3.Analytic.SincSquareDerivativeBudget.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ η t => endpoint η t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SincSquareDerivativeBudget
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Analytic.SincSquareDerivativeBudget
