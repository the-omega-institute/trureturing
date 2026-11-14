import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Algebraic.MatharA176605FiveTermRecurrence
import Reg.Support.DependentFamily
import Mathlib.Tactic.FinCases

/-! A complete-family audit retaining the original initial and nonlinear source conditions. -/
namespace Reg.D5.S1.Recurrence.Algebraic.MatharA176605FiveTermRecurrence
open _root_.D5.S1.Recurrence.Algebraic.MatharA176605FiveTermRecurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
noncomputable section

abbrev signature : Signature where
  Params := ℕ → ℕ
  State _ := ℕ
  Role := Fin 5
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a n => a n) (fun e => nomatch e)

def changed (i : Fin 5) : Realization signature :=
  realize signature (fun j a n => if j = i then a n + 1 else a n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ a : ℕ → ℕ, a 0 = 1 → a 1 = 1 →
    (∀ m : ℕ, 1 ≤ m → a (m+1) = ∑ p ∈ range (m+1), a p * a (m-p) + 1) →
    ∀ n : ℕ, 4 ≤ n →
    ((n:ℤ)+1) * (R.readout 0 a n : ℤ) +
      2 * (-3*(n:ℤ)+1) * (R.readout 1 a (n-1) : ℤ) +
      (9*(n:ℤ)-13) * (R.readout 2 a (n-2) : ℤ) +
      8 * (-(n:ℤ)+3) * (R.readout 3 a (n-3) : ℤ) +
      4 * ((n:ℤ)-4) * (R.readout 4 a (n-4) : ℤ) = 0

private theorem source_conditions : source 0 = 1 ∧ source 1 = 1 ∧
    ∀ m : ℕ, 1 ≤ m → source (m+1) =
      ∑ p ∈ range (m+1), source p * source (m-p) + 1 := by
  refine ⟨by rw [source], by rw [source], ?_⟩
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [source]
  rw [Fin.sum_univ_eq_sum_range (fun p => source p * source (k+1-p))]

private theorem changed_law (i : Fin 5) : ¬ arena.Law (changed i) := by
  intro h
  have hs := source_conditions
  have hh := h source hs.1 hs.2.1 hs.2.2 5 (by decide)
  have ha := result source hs.1 hs.2.1 hs.2.2 5 (by decide)
  fin_cases i <;> simp +decide [changed, realize] at hh <;>
    norm_num at ha <;> linarith

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, changed 0, changed_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨changed i, ?_, ?_, changed_law i⟩
      · intro j hj
        funext a n
        simp [changed, actual, realize, hj]
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(fun n => n), 0, 1, by change (0:ℕ) ≠ 1; decide⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    result (Realization signature) Type Unit where
  unitName := `Reg.D5.S1.Recurrence.Algebraic.MatharA176605FiveTermRecurrence.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.MatharA176605FiveTermRecurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.MatharA176605FiveTermRecurrence
    definition := some {
      owner := `D5.S1.Recurrence.Algebraic.MatharA176605FiveTermRecurrence
      name := `D5.S1.Recurrence.Algebraic.MatharA176605FiveTermRecurrence.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S1.Recurrence.Algebraic.MatharA176605FiveTermRecurrence
