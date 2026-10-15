import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (readout)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceMoore (Controller Run)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Evaluator
universe u v
structure Params where
  Q : Type u
  H : Type v
  machine : Controller Q H
  source : Source
  fuel : Nat
abbrev signature : Signature where
  Params := Params.{u,v}
  State p := p.Q ⊕ p.H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option (p.H × List p.Q)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p k => evaluate (fun s => p.machine.next s (readout (p.machine.addr s) p.source)) p.fuel k)
  (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => none) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p k h tr, R.readout () p k = some (h,tr) ↔
    Run p.machine p.source k tr h ∧ tr.length ≤ p.fuel

private def unitParams : Params.{u,v} where
  Q := ULift Unit
  H := ULift Unit
  machine := {
    addr := fun _ => []
    next := fun _ _ => .inr ⟨()⟩
    out := fun _ => .of (.inl true) }
  source := .of true
  fuel := 0

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have h := (law unitParams (.inr ⟨()⟩) ⟨()⟩ []).mpr ⟨.halt _,Nat.zero_le _⟩
  cases h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨unitParams,.inl ⟨()⟩,.inr ⟨()⟩,?_⟩
  intro h
  cases h

def family : Registration arena (type_of% (@native_evaluate_iff.{u,v})) where
  actual := actual
  bridge := ⟨fun h p => h p.machine p.source p.fuel,
    fun h Q H M t n => h ⟨Q,H,M,t,n⟩⟩
  variation := ⟨fun p => native_evaluate_iff p.machine p.source p.fuel,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_evaluate_iff.{u,v})
    (type_of% (realize signature.{u,v} actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.native_evaluate_iff.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.Evaluator.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
    definition := none
    coordinates := #[0,1,2,3,4]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn","arg","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Evaluator
namespace NoRepeat
universe u v
abbrev signature : Signature where
  Params := Type u
  State Q := List Q
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ tr => tr.Nodup) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Q : Type u} {H : Type v} (step : Q → Q ⊕ H)
    {n : Nat} {k : Q ⊕ H} {h : H} {tr : List Q},
    evaluate step n k = some (h,tr) → R.readout () Q tr

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  exact law (Q := ULift Unit) (H := ULift Unit) (fun _ => .inr ⟨()⟩)
    (n := 0) (k := .inr ⟨()⟩) (h := ⟨()⟩) (tr := []) rfl
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨ULift Unit,[],[⟨()⟩,⟨()⟩],?_⟩
  intro eq
  have no := Eq.mp eq List.nodup_nil
  simpa [actual,realize] using no

def family : Registration arena.{u,v} (type_of% (@terminating_path_nodup.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@terminating_path_nodup,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@terminating_path_nodup.{u,v})
    (type_of% (realize signature.{u} actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.terminating_path_nodup.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.NoRepeat.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end NoRepeat

namespace Checker
structure Params where
  C : _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery.LiteralRow
  a : Nat
  b : Nat
  r : Nat
  q : Nat
abbrev signature : Signature where
  Params := Params
  State p := Candidate p.C p.a p.b
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p A => check A p.r p.q) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p A, R.readout () p A = true ↔ Checked A p.r p.q
private def concrete : Params := ⟨.of (.inr 0),2,1,2,2⟩
private def wrongOutput : Candidate (.of (.inr 0)) 2 1 :=
  { cyclicInput with table := { cyclicInput.table with out := fun _ => .of (.inl true) } }
private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have checked : Checked cyclicInput 2 2 := (check_spec _ _ _).mp (by decide +kernel)
  have impossible := (law concrete cyclicInput).mpr checked
  cases impossible
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨concrete,cyclicInput,wrongOutput,?_⟩
  cases i
  decide +kernel

set_option maxHeartbeats 400000 in
def family : Registration arena (type_of% (@check_spec)) where
  actual := actual
  bridge := ⟨fun h p A => @h _ _ _ A p.r p.q,fun h C a b A r q => h ⟨C,a,b,r,q⟩ A⟩
  variation := by
    refine ⟨?_,bad,bad_law⟩
    change ∀ (p : Params) (A : Candidate p.C p.a p.b), check A p.r p.q = true ↔ Checked A p.r p.q
    exact fun p A => check_spec A p.r p.q
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@check_spec) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.check_spec.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.Checker.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
    definition := none
    coordinates := #[0,1,2,4,5]
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn","fn","arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Checker
namespace ZeroEndpoint
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery (LiteralRow)
abbrev signature : Signature where
  Params := LiteralRow × Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p r => RootFeasible p.1 r p.2 0) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ C r K, R.readout () (C,K) r ↔ targetCount C ≤ r ∧ targetCount C ≤ K
private theorem bad_law : ¬ arena.Law bad := by
  intro law
  exact (law (.of (.inr 0)) 1 1).mpr (by decide +kernel)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(.of (.inr 0),1),0,1,?_⟩
  intro he
  have good : RootFeasible (.of (.inr 0)) 1 1 0 :=
    (zero_call_endpoint _ _ _).mpr (by decide +kernel)
  have impossible : RootFeasible (.of (.inr 0)) 0 1 0 := Eq.mpr he good
  have wrong := ((zero_call_endpoint _ _ _).mp impossible).1
  exact (by decide +kernel : ¬ targetCount (.of (.inr 0)) ≤ 0) wrong

def family : Registration arena (type_of% (@zero_call_endpoint)) where
  actual := actual
  bridge := ⟨fun h => h,fun h => h⟩
  variation := ⟨zero_call_endpoint,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@zero_call_endpoint) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.zero_call_endpoint.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.ZeroEndpoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
    definition := none
    coordinates := #[0,2]
    readouts := #[{
      path := #["body","body","body","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn","fn","arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ZeroEndpoint

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
private theorem rootPrefix : CutPrefixFree {[]} := by
  intro a ha b hb _
  have ea : a = [] := by simpa using ha
  have eb : b = [] := by simpa using hb
  exact ea.trans eb.symm
private theorem rootNative : NativeFeasible {[]}
    (canonicalRow {[]} (substitution (.of true))) 1 1 0 :=
  (shared_moore_feasibility {[]} rootPrefix (.of true) 1 1 0 (by decide) (by decide)).mpr
    ((zero_call_endpoint _ _ _).mpr (by decide +kernel))

namespace Transfer
abbrev signature : Signature where
  Params := CutSet × Source × Nat × Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p r => RootFeasible (canonicalRow p.1 (substitution p.2.1)) r p.2.2.1 p.2.2.2)
  (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ P (_ : CutPrefixFree P) u₀ r K q (_ : 1 ≤ r) (_ : 1 ≤ K),
    NativeFeasible P (canonicalRow P (substitution u₀)) r K q ↔ R.readout () (P,u₀,K,q) r
private theorem bad_law : ¬ arena.Law bad := by
  intro law
  exact (law {[]} rootPrefix (.of true) 1 1 0 (by decide) (by decide)).mp rootNative
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨({[]},.of true,1,0),0,1,?_⟩
  intro he
  have good : RootFeasible (canonicalRow {[]} (substitution (.of true))) 1 1 0 :=
    (zero_call_endpoint _ _ _).mpr (by decide +kernel)
  have impossible : RootFeasible (canonicalRow {[]} (substitution (.of true))) 0 1 0 :=
    Eq.mpr he good
  exact (by decide +kernel : ¬ targetCount (canonicalRow {[]} (substitution (.of true))) ≤ 0)
    ((zero_call_endpoint _ _ _).mp impossible).1

def family : Registration arena (type_of% (@shared_moore_feasibility)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨shared_moore_feasibility,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@shared_moore_feasibility) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.shared_moore_feasibility.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.Transfer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
    definition := none
    coordinates := #[0,2,4,5]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn","fn","arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Transfer
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
