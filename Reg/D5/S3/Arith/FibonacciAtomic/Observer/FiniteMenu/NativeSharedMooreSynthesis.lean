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

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedCandidateData
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteRootMinimax
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
abbrev C : LiteralRow := .of (.inl false)
def good : Candidate C 0 1 where
  table := ⟨Fin.elim0,Fin.elim0,fun _ => .of (.inl true)⟩
  color := fun _ => .inr 0
def wrong : Candidate C 0 1 where
  table := ⟨Fin.elim0,Fin.elim0,fun _ => .of (.inl false)⟩
  color := fun _ => .inr 0
theorem good_mem : good ∈ candidates C 0 1 :=
  candidate_complete good.table good.color (fun _ => by change (.of (.inl true) : LiteralRow) ∈ outputList C; decide +kernel)
theorem candidate_outputs {C : LiteralRow} {a b : Nat} {A : Candidate C a b}
    (mem : A ∈ candidates C a b) (h : Fin b) : A.table.out h ∈ outputList C := by
  obtain ⟨T,ht,hm⟩ := List.mem_flatMap.mp mem
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp hm
  obtain ⟨coord,_,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨next,_,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨out,ho,rfl⟩ := List.mem_map.mp ht
  obtain ⟨g,hg,eq⟩ := List.mem_map.mp ho
  have hv := (List.mem_pi _ _).mp hg h (by simp)
  simpa only [← congrFun eq h] using hv
theorem wrong_not_mem : wrong ∉ candidates C 0 1 := by
  intro mem
  have out := candidate_outputs mem 0
  exact (by decide +kernel : (.of (.inl false) : LiteralRow) ∉ outputList C) out
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedCandidateData

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedEvaluateHalt
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v w
structure Params where
  Q : Type u
  H : Type v
  step : Q → Q ⊕ H
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
def actual : Realization signature := realize signature (fun _ p k => evaluate p.step p.fuel k) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => none) (fun e => nomatch e)
private def unitParams : Params.{u,v} where
  Q := ULift Unit
  H := ULift Unit
  step := fun _ => .inr ⟨()⟩
  fuel := 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨unitParams,.inl ⟨()⟩,.inr ⟨()⟩,?_⟩
  intro h
  cases h

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Q : Type u} {H : Type v} (step : Q → Q ⊕ H) n h,
    R.readout () ⟨Q,H,step,n⟩ (.inr h) = some (h,[])
private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have h := law unitParams.step 0 ⟨()⟩
  cases h
def family : Registration arena (type_of% (@evaluate_halt.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@evaluate_halt,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,fun e => nomatch e⟩
  dependence := dependence

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedEvaluateHalt

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedEvaluateExact
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v w
structure Params where
  Q : Type u
  H : Type v
  step : Q → Q ⊕ H
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
def actual : Realization signature := realize signature (fun _ p k => evaluate p.step p.fuel k) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => none) (fun e => nomatch e)
private def unitParams : Params.{u,v} where
  Q := ULift Unit
  H := ULift Unit
  step := fun _ => .inr ⟨()⟩
  fuel := 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨unitParams,.inl ⟨()⟩,.inr ⟨()⟩,?_⟩
  intro h
  cases h

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Q : Type u} {H : Type v} (step : Q → Q ⊕ H)
    {n : Nat} {k : Q ⊕ H} {h : H} {tr : List Q},
    evaluate step n k = some (h,tr) → R.readout () ⟨Q,H,step,tr.length⟩ k = some (h,tr)
private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have h := law unitParams.step (n := 0) (k := .inr ⟨()⟩) (h := ⟨()⟩) (tr := []) rfl
  cases h
def family : Registration arena (type_of% (@evaluate_exact.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@evaluate_exact,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,fun e => nomatch e⟩
  dependence := dependence

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedEvaluateExact

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedEvaluateReindex
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v w
structure Params where
  Q : Type u
  H : Type v
  step : Q → Q ⊕ H
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
def actual : Realization signature := realize signature (fun _ p k => evaluate p.step p.fuel k) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => none) (fun e => nomatch e)
private def unitParams : Params.{u,v} where
  Q := ULift Unit
  H := ULift Unit
  step := fun _ => .inr ⟨()⟩
  fuel := 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨unitParams,.inl ⟨()⟩,.inr ⟨()⟩,?_⟩
  intro h
  cases h

abbrev arena : Arena where
  signature := signature.{w,0}
  Law R := ∀ {Q : Type u} {H : Type v} {Q' : Type w} {H' : Type}
    (e : Q ≃ Q') (f : H ≃ H') (step : Q → Q ⊕ H) (step' : Q' → Q' ⊕ H')
    (_ : ∀ s, step' (e s) = Sum.map e f (step s)) n k,
    R.readout () ⟨Q',H',step',n⟩ (Sum.map e f k) =
      (evaluate step n k).map (fun p => (f p.1,p.2.map e))
private theorem bad_law : ¬ arena.{u,v,w}.Law bad := by
  intro law
  let e : ULift.{u} Unit ≃ ULift.{w} Unit := Equiv.ulift.trans Equiv.ulift.symm
  let f : ULift.{v} Unit ≃ Unit := Equiv.ulift
  have h := law e f (fun _ => .inr ⟨()⟩) (fun _ => .inr ()) (by intro s; rfl) 0 (.inr ⟨()⟩)
  cases h
def family : Registration arena.{u,v,w} (type_of% (@evaluate_reindex.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@evaluate_reindex,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,fun e => nomatch e⟩
  dependence := dependence

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedEvaluateReindex

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedCandidateComplete
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

open Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedCandidateData
structure Params where
  row : LiteralRow
  a : Nat
  b : Nat
abbrev signature : Signature where
  Params := Params
  State p := Candidate p.row p.a p.b
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ p A => A ∈ candidates p.row p.a p.b) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {C : LiteralRow} {a b : Nat} (T : RootTable C (Fin a) (Fin b)) (c : _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootSimulation.Chart C → Fin a ⊕ Fin b),
    (∀ h, T.out h ∈ outputList C) → R.readout () ⟨C,a,b⟩ ⟨T,c⟩
private theorem bad_law : ¬ arena.Law bad := by
  intro law
  exact law good.table good.color (fun _ => by change (.of (.inl true) : LiteralRow) ∈ outputList C; decide +kernel)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨C,0,1⟩,good,wrong,?_⟩
  intro h
  exact wrong_not_mem (Eq.mp h good_mem)
def family : Registration arena (type_of% (@candidate_complete)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@candidate_complete,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@candidate_complete) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.candidate_complete.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedCandidateComplete.family
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
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","body","body"], stateBinder := 3, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedCandidateComplete

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedBoundedMem
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

open Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedCandidateData
structure Params where
  row : LiteralRow
  a : Nat
  b : Nat
  candidate : Candidate row a b
abbrev signature : Signature where
  Params := Params
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ p K => (⟨p.a,p.b,p.candidate⟩ : Sigma fun a => Sigma fun b => Candidate p.row a b) ∈ boundedCandidates p.row K) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {C : LiteralRow} {K a b : Nat} {A : Candidate C a b},
    1 ≤ a+b → a+b ≤ K → A ∈ candidates C a b → R.readout () ⟨C,a,b,A⟩ K
private theorem bad_law : ¬ arena.Law bad := by
  intro law
  exact law (K := 1) (by decide) (by decide) good_mem
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨C,0,1,good⟩,1,0,?_⟩
  intro h
  have hm := bounded_mem (K := 1) (by decide) (by decide) good_mem
  have impossible := Eq.mp h hm
  simpa [actual,realize,boundedCandidates] using impossible
def family : Registration arena (type_of% (@bounded_mem)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bounded_mem,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bounded_mem) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.bounded_mem.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedBoundedMem.family
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
    coordinates := #[0,2,3,4]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body"], stateBinder := 1, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedBoundedMem

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedBoundedSize
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

open Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedCandidateData
abbrev signature : Signature where
  Params := Nat
  State _ := Nat × Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ K s => 1 ≤ s.1+s.2 ∧ s.1+s.2 ≤ K) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {C : LiteralRow} {K : Nat} {A : Sigma fun a => Sigma fun b => Candidate C a b},
    A ∈ boundedCandidates C K → R.readout () K (A.1,A.2.1)
private theorem bad_law : ¬ arena.Law bad := by
  intro law
  exact law (bounded_mem (K := 1) (by decide) (by decide) good_mem)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1,(0,1),(0,2),?_⟩
  intro h
  have no : 1 ≤ 0+2 ∧ 0+2 ≤ 1 := Eq.mp h ⟨by decide,by decide⟩
  omega
def family : Registration arena (type_of% (@bounded_size)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bounded_size,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bounded_size) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.bounded_size.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedBoundedSize.family
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
    coordinates := #[1]
    readouts := #[{
      path := #["body","body","body","body"], stateBinder := 2, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis.PublishedBoundedSize
