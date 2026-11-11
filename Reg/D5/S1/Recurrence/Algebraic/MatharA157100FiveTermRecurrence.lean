import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Algebraic.MatharA157100FiveTermRecurrence
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S1.Recurrence.Algebraic.MatharA157100FiveTermRecurrence
open _root_.D5.S1.Recurrence.Algebraic.MatharA157100FiveTermRecurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℚ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => if n = 4 then 1 else 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) + 1) * R.readout () () n +
      (-5 * (n : ℚ) + 1) * R.readout () () (n - 1) +
      2 * (2 * (n : ℚ) - 1) * R.readout () () (n - 2) +
      2 * (2 * (n : ℚ) - 7) * R.readout () () (n - 3) +
      2 * (-2 * (n : ℚ) + 7) * R.readout () () (n - 4) = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 4 (by decide)
  norm_num [rejected, realize] at hh

private theorem initial_coefficients : a 0 = 1 ∧ a 1 = 2 := by
  have ht : HasSubst (X * (1 - X ^ 2) : PowerSeries ℚ) := HasSubst.X'.mul_left
  have h0 : a 0 = 1 := by
    simp [a, A, coeff_zero_eq_constantCoeff,
      constantCoeff_subst_of_constantCoeff_zero (by simp :
        constantCoeff (X * (1 - X ^ 2) : PowerSeries ℚ) = 0)]
  refine ⟨h0, ?_⟩
  have h : coeff 0 (derivative (R := ℚ) A) = a 1 := by
    simp [a, coeff_derivative]
  rw [← h]
  simp [A, Derivation.leibniz, derivative_subst ht, derivative_pow,
    smul_eq_mul, coeff_zero_eq_constantCoeff,
    constantCoeff_subst_of_constantCoeff_zero (by simp :
      constantCoeff (X * (1 - X ^ 2) : PowerSeries ℚ) = 0),
    ← coeff_zero_eq_constantCoeff, coeff_derivative, coeff_map, catalanSeries_coeff]

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    rw [initial_coefficients.1, initial_coefficients.2]
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    result (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Algebraic.MatharA157100FiveTermRecurrence.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.MatharA157100FiveTermRecurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.MatharA157100FiveTermRecurrence
    definition := some {
      owner := `D5.S1.Recurrence.Algebraic.MatharA157100FiveTermRecurrence
      name := `D5.S1.Recurrence.Algebraic.MatharA157100FiveTermRecurrence.claim
      path := #[] }
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg"]
        stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "arg", "arg"]
        stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S1.Recurrence.Algebraic.MatharA157100FiveTermRecurrence
