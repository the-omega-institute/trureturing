import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Algebraic.MatharA116387SixTermRecurrence
import Reg.Support.DependentFamily
import Mathlib.Tactic.FinCases

/-! The complete native specification and six ordered coefficient observations. -/

namespace Reg.D5.S1.Recurrence.Algebraic.MatharA116387SixTermRecurrence

open _root_.D5.S1.Recurrence.Algebraic.MatharA116387SixTermRecurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Fin 6
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def changed (i : Fin 6) : Realization signature :=
  realize signature (fun j _ n => if j = i then a n + 1 else a n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := native_spec ∧ ∀ n : ℕ, 5 ≤ n →
    (n : ℚ) * (17 * (n : ℚ) - 142) * R.readout 0 () n +
      (17 * (n : ℚ) ^ 2 + 95 * (n : ℚ) + 138) * R.readout 1 () (n - 1) +
      (-391 * (n : ℚ) ^ 2 + 2488 * (n : ℚ) - 2908) * R.readout 2 () (n - 2) +
      (-17 * (n : ℚ) ^ 2 - 603 * (n : ℚ) + 1892) * R.readout 3 () (n - 3) +
      2 * (697 * (n : ℚ) - 2021) * ((n : ℚ) - 4) * R.readout 4 () (n - 4) +
      60 * (17 * (n : ℚ) - 47) * ((n : ℚ) - 4) * R.readout 5 () (n - 5) = 0

private theorem changed_law (i : Fin 6) : ¬ arena.Law (changed i) := by
  intro h
  have hh := h.2 5 (by decide)
  have ha := result.2 5 (by decide)
  fin_cases i <;> simp +decide [changed, realize] at hh <;>
    norm_num at ha <;> linarith

private theorem initial_coefficients : a 0 = 1 ∧ a 1 = 2 := by
  have hnum (n : ℕ) [Nat.AtLeastTwo n] : derivative (ofNat(n) : PowerSeries ℚ) = 0 :=
    (derivative (R := ℚ)).map_natCast n
  have hm0 := result.1.1.1
  have hm := result.1.1.2
  have hy0 := result.1.2.2.1.1
  have hf := result.1.2.2.2.2
  have hf0 : constantCoeff F = 1 := by
    have h := congrArg constantCoeff hf
    norm_num only [map_mul, map_sub, map_ofNat, hm0, hy0, map_one] at h
    exact h
  have hm1 : constantCoeff (derivative (R := ℚ) M) = 1 := by
    have h := congrArg constantCoeff (congrArg (derivative (R := ℚ)) hm)
    norm_num [Derivation.leibniz, hnum, smul_eq_mul, hm0] at h
    exact h
  have hy1 : constantCoeff (derivative (R := ℚ) y) = -1 := by
    norm_num [y, Derivation.leibniz, hnum, smul_eq_mul, hm0, hm1]
  have hf1 : constantCoeff (derivative (R := ℚ) F) = 2 := by
    have h := congrArg constantCoeff (congrArg (derivative (R := ℚ)) hf)
    norm_num [Derivation.leibniz, hnum, smul_eq_mul, hm0, hm1, hy0, hy1, hf0] at h
    linarith
  constructor
  · simpa only [a, coeff_zero_eq_constantCoeff] using hf0
  · have h : coeff 0 (derivative (R := ℚ) F) = a 1 := by simp [a, coeff_derivative]
    rw [← h, coeff_zero_eq_constantCoeff]
    exact hf1

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
  unitName := `Reg.D5.S1.Recurrence.Algebraic.MatharA116387SixTermRecurrence.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.MatharA116387SixTermRecurrence.family
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
    owner := `D5.S1.Recurrence.Algebraic.MatharA116387SixTermRecurrence
    definition := some {
      owner := `D5.S1.Recurrence.Algebraic.MatharA116387SixTermRecurrence
      name := `D5.S1.Recurrence.Algebraic.MatharA116387SixTermRecurrence.claim
      path := #[] }
    coordinates := #[]
    readouts := #[
      { path := #["arg", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg"]
        stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["arg", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["arg", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["arg", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["arg", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["arg", "body", "body", "fn", "arg", "arg", "arg"]
        stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S1.Recurrence.Algebraic.MatharA116387SixTermRecurrence
