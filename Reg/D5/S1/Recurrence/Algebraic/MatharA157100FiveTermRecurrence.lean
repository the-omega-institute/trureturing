import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Algebraic.MatharA157100FiveTermRecurrence
import Reg.Support.DependentFamily
import Mathlib.Tactic.FinCases

/-! Source-bound registration of the complete five-term recurrence. -/

namespace Reg.D5.S1.Recurrence.Algebraic.MatharA157100FiveTermRecurrence
open _root_.D5.S1.Recurrence.Algebraic.MatharA157100FiveTermRecurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Fin 5
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def changed (i : Fin 5) : Realization signature :=
  realize signature (fun j _ n => if j = i then a n + 1 else a n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) + 1) * R.readout 0 () n +
      (-5 * (n : ℚ) + 1) * R.readout 1 () (n - 1) +
      2 * (2 * (n : ℚ) - 1) * R.readout 2 () (n - 2) +
      2 * (2 * (n : ℚ) - 7) * R.readout 3 () (n - 3) +
      2 * (-2 * (n : ℚ) + 7) * R.readout 4 () (n - 4) = 0

private theorem changed_law (i : Fin 5) : ¬ arena.Law (changed i) := by
  intro h
  have hh := h 4 (by decide)
  have ha := result 4 (by decide)
  fin_cases i <;> simp +decide [changed, realize] at hh <;>
    norm_num at ha <;> linarith

private theorem initial_coefficients : a 0 = 1 ∧ a 1 = 2 := by
  have ht : HasSubst (X * (1 - X ^ 2) : PowerSeries ℚ) := HasSubst.X'.mul_left
  have hz : MvPowerSeries.constantCoeff (X * (1 - X ^ 2) : PowerSeries ℚ) = 0 := by
    change constantCoeff (X * (1 - X ^ 2) : PowerSeries ℚ) = 0
    simp
  have hs (f : PowerSeries ℚ) :
      constantCoeff (subst (X * (1 - X ^ 2)) f) = constantCoeff f := by
    exact constantCoeff_subst_of_constantCoeff_zero hz f
  have hd : constantCoeff (derivative (R := ℚ)
      (PowerSeries.catalanSeries.map (Nat.castRingHom ℚ))) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
    simp
  have hc : constantCoeff (PowerSeries.catalanSeries.map (Nat.castRingHom ℚ)) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp
  have h0 : a 0 = 1 := by
    simp [a, A, coeff_zero_eq_constantCoeff, hs, hc]
  refine ⟨h0, ?_⟩
  have h : coeff 0 (derivative (R := ℚ) A) = a 1 := by
    simp [a, coeff_derivative]
  rw [← h]
  norm_num [A, Derivation.leibniz, derivative_subst ht,
    smul_eq_mul, coeff_zero_eq_constantCoeff, hs, hd, hc]

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, changed 0, changed_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨changed i, ?_, ?_, changed_law i⟩
      · intro j hj
        funext p n
        simp [changed, actual, realize, hj]
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    rw [initial_coefficients.1, initial_coefficients.2]
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    result (Realization signature) Type Unit where
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.MatharA157100FiveTermRecurrence
    definition := some {
      owner := `D5.S1.Recurrence.Algebraic.MatharA157100FiveTermRecurrence
      name := `D5.S1.Recurrence.Algebraic.MatharA157100FiveTermRecurrence.claim
      path := #[] }
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg",
          "fn", "arg", "arg"]
        stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "arg", "arg"]
        stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S1.Recurrence.Algebraic.MatharA157100FiveTermRecurrence
