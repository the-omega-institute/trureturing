import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Algebraic.MatharA186335FiveTermRecurrence
import Reg.Support.DependentFamily
import Mathlib.Tactic.FinCases

/-! Source-bound registration of the complete five-term recurrence. -/

namespace Reg.D5.S1.Recurrence.Algebraic.MatharA186335FiveTermRecurrence
open _root_.D5.S1.Recurrence.Algebraic.MatharA186335FiveTermRecurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Fin 5
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def changed (i : Fin 5) : Realization signature :=
  realize signature (fun j _ n => if j = i then a n + 1 else a n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 4 ≤ n →
    (n : ℤ) * R.readout 0 () n +
      (1-2*(n : ℤ)) * R.readout 1 () (n-1) +
      5*(1-(n : ℤ)) * R.readout 2 () (n-2) +
      3*(2*(n : ℤ)-3) * R.readout 3 () (n-3) +
      5*((n : ℤ)-2) * R.readout 4 () (n-4) = 0

private theorem changed_law (i : Fin 5) : ¬ arena.Law (changed i) := by
  intro h
  have hh := h 4 (by decide)
  have ha := result 4 (by decide)
  fin_cases i <;> simp +decide [changed, realize] at hh <;>
    norm_num at ha <;> linarith

private theorem actual_nonconstant : a 0 ≠ a 2 := by
  norm_num [a, sourcePairs, legal, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ, Nat.choose]

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
    exact ⟨(), 0, 2, actual_nonconstant⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    result (Realization signature) Type Unit where
  unitName := `Reg.D5.S1.Recurrence.Algebraic.MatharA186335FiveTermRecurrence.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.MatharA186335FiveTermRecurrence.family
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
    owner := `D5.S1.Recurrence.Algebraic.MatharA186335FiveTermRecurrence
    definition := some {
      owner := `D5.S1.Recurrence.Algebraic.MatharA186335FiveTermRecurrence
      name := `D5.S1.Recurrence.Algebraic.MatharA186335FiveTermRecurrence.claim
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
end Reg.D5.S1.Recurrence.Algebraic.MatharA186335FiveTermRecurrence
