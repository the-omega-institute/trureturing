import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.PisanoMatrixBridge
import Reg.Support.DependentFamily

/-! Source-bound audit of the canonical scalar-period/return equivalence. -/

namespace Reg.D5.S3.Arith.PisanoMatrixBridge

open _root_.D5.S3.Arith.PisanoMatrixBridge
open _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m => Nat.fib m) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n k : ℕ,
    (∀ m, R.readout () () (m + k) % n = R.readout () () m % n) ↔
      Function.IsPeriodicPt (step (A := ZMod n)) k (0, 1)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 2 1).mp (by intro m; rfl)
  have hz : (1 : ZMod 2) = 0 := congrArg Prod.fst hh
  exact one_ne_zero hz

def registration : Registration arena (type_of% @period_iff_return) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨period_iff_return, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change Nat.fib 0 ≠ Nat.fib 1
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@period_iff_return) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PisanoMatrixBridge.period_iff_return.audit
  realizationName := `Reg.D5.S3.Arith.PisanoMatrixBridge.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => Nat.fib m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.PisanoMatrixBridge
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "fn", "arg", "body", "fn", "arg", "fn", "arg", "fn"]
        stateBinder := 2
        functionOperand := true
        stateOperand := none
        booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "body", "arg", "fn", "arg", "fn"]
        stateBinder := 2
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.PisanoMatrixBridge
