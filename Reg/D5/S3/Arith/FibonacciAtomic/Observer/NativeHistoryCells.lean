import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply)
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder
open D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
open D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSeparation
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting
open D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells
open D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells
abbrev signature : Signature where
  Params := Σ C : LiteralRow, Σ d : Nat, Patterns C d
  State p := Variables p.2.2 → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p v => evaluate v (wholeTerm p.2.2)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (C : LiteralRow) (d : Nat) (η : Patterns C d) (H : History)
    (_ : ∀ e ∈ H, e.2.1.length < d),
    feasible η H = true ↔ ∃ v : Variables η → Source,
      Function.Injective (oldValues η v) ∧ Consistent H (R.readout () ⟨C,d,η⟩ v)

theorem bridge : (type_of% (@cell_feasibility_exact)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := @cell_feasibility_exact

def bad : Realization signature := realize signature (fun _ _ _ => .of true) (fun e => nomatch e)

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  let C : LiteralRow := .of (.inl false)
  let η : Patterns C 1 := fun b => False.elim (by have hb := b.property; simp [C,labels] at hb)
  let H : History := [(0,[],Reply.beta)]
  have pass : feasible η H = true := by
    simp [feasible, testHistory, wholeTerm, C, H, Consistent, evaluate,
      _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.readout, syntaxLegal, labels]
  have bound : ∀ e ∈ H, e.2.1.length < 1 := by simp [H]
  obtain ⟨v,inj,hist⟩ := (h C 1 η H bound).mp pass
  have no := hist (0,[],Reply.beta) (by simp [H])
  cases no

def proof : Registration arena (type_of% (@cell_feasibility_exact)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    let C : LiteralRow := .of (.inr 0)
    let η : Patterns C 0 := fun _ => ()
    refine ⟨⟨C,0,η⟩,(fun _ => .of true),(fun _ => .of false),?_⟩
    have h0 : 0 ∈ labels C := by simp [C,labels]
    intro eq
    have no : (FreeMagma.of true : Source) = .of false := by
      simpa [actual,realize,wholeTerm,C,h0,oldTerm,patternTerm,evaluate,η] using eq
    cases no

#print axioms proof

#print axioms bridge
#print axioms actual_law
noncomputable def cell_feasibility_exact_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells.cell_feasibility_exact)
    (Realization signature) ((C : LiteralRow) → (d : Nat) → Patterns C d → Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells.cell_feasibility_exact
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => evaluate v (wholeTerm p.2.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun C d (η : Patterns C d) => Variables η → Source)
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "arg", "body", "arg", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms cell_feasibility_exact_registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells
