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

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting
abbrev signature : Signature where
  Params := Σ X : Type, Term X
  State p := p.1 → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p v => evaluate v p.2) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ p v => match evaluate v p.2 with
  | .of b => .of (!b)
  | .mul l _ => l) (fun e => nomatch e)

abbrev historyArena : Arena where
  signature := signature
  Law R := ∀ (X : Type) (d : Nat) (t : Term X) (_ : DeepAt d [] t) (H : History)
    (_ : ∀ e ∈ H, e.2.1.length < d) (test v : X → Source),
    Consistent H (R.readout () ⟨X,t⟩ test) ↔ Consistent H (R.readout () ⟨X,t⟩ v)

theorem history_bridge : (type_of% (@symbolic_history_constant)) ↔ historyArena.Law actual := Iff.rfl
theorem history_law : historyArena.Law actual := @symbolic_history_constant

private theorem history_bad : ¬ historyArena.Law bad := by
  intro h
  let t : Term Unit := .mul (.of (.inr ())) (.of (.inr ()))
  have deep : DeepAt 1 [] t := by simp [t,DeepAt]
  have bound : ∀ (e : Nat × Address × Reply), e ∈ [(0,[],Reply.alpha)] → e.2.1.length < 1 := by simp
  have eq := h Unit 1 t deep [(0,[],Reply.alpha)] bound (fun _ => .of true) (fun _ => .of false)
  simpa [bad,realize,Consistent,t,evaluate,_root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.readout] using eq

def historyProof : Registration historyArena (type_of% (@symbolic_history_constant)) where
  actual := actual
  bridge := history_bridge
  variation := ⟨history_law,bad,history_bad⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,history_bad⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨Unit,.of (.inr ())⟩,(fun _ => .of true),(fun _ => .of false),?_⟩
    intro eq; cases eq

abbrev recutArena : Arena where
  signature := signature
  Law R := ∀ (X : Type) (d : Nat) (Q : CutSet) (_ : CutPrefixFree Q)
    (_ : ∀ q ∈ Q, q.length < d) (t : Term X) (_ : DeepAt d [] t) (v : X → Source),
    orderedHoles Q (R.readout () ⟨X,t⟩ v) = symbolicOrdered Q t ∧
    cutExterior Q [] (R.readout () ⟨X,t⟩ v) = exteriorFill v (symbolicExterior Q [] t) ∧
    (∀ q ∈ Q, subtree q (R.readout () ⟨X,t⟩ v) = (termAt q t).map (evaluate v)) ∧
    literalRecord Q (R.readout () ⟨X,t⟩ v) = symbolicRecord Q t v

theorem recut_bridge : (type_of% (@symbolic_recut_exact)) ↔ recutArena.Law actual := Iff.rfl
theorem recut_law : recutArena.Law actual := @symbolic_recut_exact

private theorem recut_bad : ¬ recutArena.Law bad := by
  intro h
  have pf : CutPrefixFree (∅ : CutSet) := by intro a ha; simp at ha
  have eq := (h Empty 1 ∅ pf (by simp) (.of (.inl false)) trivial (fun e => nomatch e)).2.1
  cases eq

def recutProof : Registration recutArena (type_of% (@symbolic_recut_exact)) where
  actual := actual
  bridge := recut_bridge
  variation := ⟨recut_law,bad,recut_bad⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,recut_bad⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨Unit,.of (.inr ())⟩,(fun _ => .of true),(fun _ => .of false),?_⟩
    intro eq; cases eq

#print axioms historyProof
#print axioms recutProof
noncomputable def symbolic_history_constant_registration : LeanInformationAudit.Contract.Registration.{1,1,1,0,0,0,1,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting.symbolic_history_constant)
    (Realization signature) (Type → Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting.symbolic_history_constant
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting.historyProof
  realizationSource := none
  generated := false
  arena := .source ⟨historyArena⟩
  objectArena := .source ⟨historyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source historyArena ⟨historyProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => evaluate v p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun X : Type => X → Source)
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting
    definition := none
    coordinates := #[0,2]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms symbolic_history_constant_registration

noncomputable def symbolic_recut_exact_registration : LeanInformationAudit.Contract.Registration.{1,1,1,0,0,0,1,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting.symbolic_recut_exact)
    (Realization signature) (Type → Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting.symbolic_recut_exact
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting.recutProof
  realizationSource := none
  generated := false
  arena := .source ⟨recutArena⟩
  objectArena := .source ⟨recutArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source recutArena ⟨recutProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => evaluate v p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun X : Type => X → Source)
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting
    definition := none
    coordinates := #[0,5]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms symbolic_recut_exact_registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting
