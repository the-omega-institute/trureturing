import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Congruence.HannaUniformCorrection
import Reg.Support.DependentFamily

/-! Full-family audit of the uniform Euler-exponent bounds. -/

open _root_.D5.S3.Arith.Congruence.HannaUniformCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.Congruence.HannaUniformCorrection

abbrev signature : Signature where
  Params := ℤ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ s n => c s n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (s : ℤ), 2 ≤ s → ∀ (n : ℕ), 0 < n →
    1 ≤ R.readout () s n ∧ R.readout () s n ≤ (n : ℤ) ^ (s.toNat - 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 2 (by omega) 1 (by omega)).1
  change (1 : ℤ) ≤ 0 at he
  omega

def registration : Registration arena (type_of% @exponent_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exponent_bounds, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨2, 0, 1, ?_⟩
    change c 2 0 ≠ c 2 1
    have h1 : c 2 1 = 1 := by
      have hb := exponent_bounds 2 (by omega) 1 (by omega)
      norm_num at hb
      omega
    have h0 : c 2 0 = 0 := by
      unfold c _root_.D5.S1.Recurrence.Witt.BoundedEulerCorrection.ledger
      rw [Nat.strongRecOn_eq]
      exact Int.ediv_zero _
    omega

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exponent_bounds) (Realization signature) Type Unit where
  unitName := `HannaUniformCorrection.exponent_bounds.audit
  realizationName := `Reg.D5.S3.Arith.Congruence.HannaUniformCorrection.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ s n => c s n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Congruence.HannaUniformCorrection
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "body", "body", "fn", "arg", "arg"]
        stateBinder := 2, functionOperand := false, stateOperand := none,
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "arg", "fn", "arg"]
        stateBinder := 2, functionOperand := false, stateOperand := none,
        booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end Reg.D5.S3.Arith.Congruence.HannaUniformCorrection
