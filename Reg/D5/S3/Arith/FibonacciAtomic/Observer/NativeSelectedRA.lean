import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeIndependentExecution (Op Run Word expand)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA

private theorem returning_control {C : Type} {δ : C → Op C} {c b : C}
    {U : Source} {h : Word} (r : Run δ c U h b) : δ b = .ret := by
  induction r with
  | ret hop => exact hop
  | localStep _ _ ih => exact ih
  | read _ _ _ ih => exact ih
  | update _ ih => exact ih

abbrev cleanupSignature : Signature where
  Params := Bool
  State _ := Work
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := State
  Anchor := Empty
  finiteAnchor := inferInstance

def cleanupActual : Realization cleanupSignature :=
  realize cleanupSignature (fun _ q w => .ready q w.row) (fun i => nomatch i)

def cleanupBad : Realization cleanupSignature :=
  realize cleanupSignature (fun _ _ _ => .entry) (fun i => nomatch i)

abbrev cleanupArena : Arena where
  signature := cleanupSignature
  Law R := ∀ (q : Bool) (w : Work) (σ : Nat → Nat) (U : Source),
    Run step (.active q (go 40 w)) U
      (expand (cleanupTiming (w.operand.length+w.guardPath.length+6) σ))
      (R.readout () q w)

private theorem cleanup_bad : ¬ cleanupArena.Law cleanupBad := by
  intro h
  have r := h true emptyWork (fun _ => 0) (.of true)
  have no := returning_control r
  simp [cleanupBad,realize,step] at no

private theorem cleanup_dependence :
    ObservationalDependence cleanupSignature cleanupActual := by
  intro i
  refine ⟨true,emptyWork,{emptyWork with row := [0]},?_⟩
  simp [cleanupActual,realize,emptyWork]

def cleanupProof : Registration cleanupArena (type_of% (@cleanup_every_schedule)) where
  actual := cleanupActual
  bridge := Iff.rfl
  variation := ⟨@cleanup_every_schedule,cleanupBad,cleanup_bad⟩
  sensitivity := ⟨fun i => ⟨cleanupBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,cleanup_bad⟩,fun i => nomatch i⟩
  dependence := cleanup_dependence

abbrev supportSignature : Signature where
  Params := Unit
  State _ := State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Op State
  Anchor := Empty
  finiteAnchor := inferInstance

def supportActual : Realization supportSignature :=
  realize supportSignature (fun _ _ s => step s) (fun i => nomatch i)

def supportBad : Realization supportSignature :=
  realize supportSignature (fun _ _ _ => .ret) (fun i => nomatch i)

abbrev supportArena : Arena where
  signature := supportSignature
  Law R :=
    (∀ u : Source, (∃ h : Word,
      Run (R.readout () ()) .entry u h (.ready true rootBytes)) ↔ u = .of true) ∧
    (∀ j : Nat, PostSelectionWitness j) ∧
    (∃ h : Word, .update ∉ h ∧
      Run step .entry (.of false) h (.ready false (leafBytes false)) ∧
      _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder.literalRecord
        (cut false) (.of false) = (.of (.inl false), ∅) ∧
      ∀ p ∈ cut false, [].IsPrefix p ∧ p ≠ [] ∧
        _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.subtree
          p (.of false) = none) ∧
    (∀ (h : Word) (row : List Cell),
      ¬ Run step .entry (.of false) h (.ready true row)) ∧
    (∀ (u : Source) (j : Nat),
      _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder.literalRecord
        {[]} (substitution^[j] u) =
          _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber.rootLabel) ∧
    (∀ (u : Source) (h : Word) (row : List Cell),
      Run step .entry u h (.ready true row) →
        ∃ tail : Word, h = .observer (.read [] .alpha) :: tail)

private theorem stopped_only {c b : State} {U : Source} {h : Word}
    (r : Run (fun _ => Op.ret) c U h b) : b = c := by
  induction r with
  | ret _ => rfl
  | localStep h _ _ => cases h
  | read h _ _ _ => cases h
  | update _ ih => exact ih

private theorem support_bad : ¬ supportArena.Law supportBad := by
  intro h
  obtain ⟨w,r⟩ := (h.1 (.of true)).mpr rfl
  have no := stopped_only r
  cases no

private theorem support_dependence :
    ObservationalDependence supportSignature supportActual := by
  intro i
  refine ⟨(),.entry,.ready true rootBytes,?_⟩
  simp [supportActual,realize,step]

def supportProof : Registration supportArena (type_of% (@selected_root_support)) where
  actual := supportActual
  bridge := Iff.rfl
  variation := ⟨selected_root_support,supportBad,support_bad⟩
  sensitivity := ⟨fun i => ⟨supportBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,support_bad⟩,fun i => nomatch i⟩
  dependence := support_dependence

noncomputable def cleanup_every_schedule_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.cleanup_every_schedule)
      (Realization cleanupSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.cleanup_every_schedule
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.cleanupProof
  realizationSource := none
  generated := false
  arena := .source ⟨cleanupArena⟩
  objectArena := .source ⟨cleanupArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cleanupArena ⟨cleanupProof⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize cleanupSignature (fun _ q w => .ready q w.row) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
    definition := none
    coordinates := #[0]
    readouts := #[{path := #["body","body","body","body","arg"], stateBinder := 0,functionOperand := false,stateOperand := some #["arg","arg"], booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def selected_root_support_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.selected_root_support)
      (Realization supportSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.selected_root_support
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.supportProof
  realizationSource := none
  generated := false
  arena := .source ⟨supportArena⟩
  objectArena := .source ⟨supportArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source supportArena ⟨supportProof⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize supportSignature (fun _ _ s => step s) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
    definition := none
    coordinates := #[]
    readouts := #[{path := #["fn","arg","body","fn","arg","arg","body", "fn","fn","fn","fn","arg"],stateBinder := 0,functionOperand := true, stateOperand := none,booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev comparisonArena : Arena where
  signature := supportSignature
  Law R := ∀ (A B : Source), ∃ h : Word, .update ∉ h ∧
    Run (R.readout () ()) .entry (.mul A B) h
      (.ready false (forkPrefix ++ [if A = B then 10 else 9,5])) ∧
      _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder.literalRecord
        (cut false) (.mul A B) = forkRecord (decide (A = B))

private theorem comparison_bad : ¬ comparisonArena.Law supportBad := by
  intro h
  obtain ⟨w,_,r⟩ := h (.of true) (.of false)
  have no := stopped_only r.1
  cases no

def comparisonProof : Registration comparisonArena (type_of% (@quiescent_two_hole)) where
  actual := supportActual
  bridge := Iff.rfl
  variation := ⟨quiescent_two_hole,supportBad,comparison_bad⟩
  sensitivity := ⟨fun i => ⟨supportBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,comparison_bad⟩,fun i => nomatch i⟩
  dependence := support_dependence

noncomputable def quiescent_two_hole_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.quiescent_two_hole)
      (Realization supportSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.quiescent_two_hole
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.comparisonProof
  realizationSource := none
  generated := false
  arena := .source ⟨comparisonArena⟩
  objectArena := .source ⟨comparisonArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source comparisonArena ⟨comparisonProof⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize supportSignature (fun _ _ s => step s) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
    definition := none
    coordinates := #[]
    readouts := #[{path := #["body","body","arg","body","arg","fn","arg","fn","fn","fn","fn","arg"],stateBinder := 0,functionOperand := true,stateOperand := none,booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private theorem world_event_returning (writer : Bool) (a : World)
    (h : a.returned = true → step a.config = .ret) :
    (worldEvent writer a).returned = true → step (worldEvent writer a).config = .ret := by
  rcases a with ⟨c,U,flag⟩
  cases flag with
  | true => simpa [worldEvent] using h
  | false =>
    cases writer with
    | true => simp [worldEvent]
    | false => cases he : step c <;> simp [worldEvent,he]

private theorem trajectory_returning (schedule : Nat → Bool) (c : State)
    (U : Source) (n : Nat) :
    (trajectory schedule ⟨c,U,false⟩ n).returned = true →
      step (trajectory schedule ⟨c,U,false⟩ n).config = .ret := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih => exact world_event_returning _ _ ih

abbrev progressingArena : Arena where
  signature := cleanupSignature
  Law R := ∀ (q : Bool) (w : Work) (schedule : Nat → Bool) (U : Source),
    Progressing schedule ⟨.active q (go 40 w),U,false⟩ → ∃ m : Nat,
      (trajectory schedule ⟨.active q (go 40 w),U,false⟩ m).returned = true ∧
      (trajectory schedule ⟨.active q (go 40 w),U,false⟩ m).config = R.readout () q w

private theorem progressing_bad : ¬ progressingArena.Law cleanupBad := by
  intro h
  obtain ⟨n,hn,he⟩ := h true emptyWork (fun _ => false) (.of true)
    (fun n _ => ⟨n,le_rfl,rfl⟩)
  have no := trajectory_returning (fun _ => false) (.active true (go 40 emptyWork))
    (.of true) n hn
  rw [he] at no
  simp [cleanupBad,realize,step] at no

def progressingProof : Registration progressingArena (type_of% (@cleanup_progressing)) where
  actual := cleanupActual
  bridge := Iff.rfl
  variation := ⟨@cleanup_progressing,cleanupBad,progressing_bad⟩
  sensitivity := ⟨fun i => ⟨cleanupBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,progressing_bad⟩,fun i => nomatch i⟩
  dependence := cleanup_dependence

noncomputable def cleanup_progressing_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.cleanup_progressing)
      (Realization cleanupSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.cleanup_progressing
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.progressingProof
  realizationSource := none
  generated := false
  arena := .source ⟨progressingArena⟩
  objectArena := .source ⟨progressingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source progressingArena ⟨progressingProof⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize cleanupSignature (fun _ q w => .ready q w.row) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
    definition := none
    coordinates := #[0]
    readouts := #[{path := #["body","body","body","body","body","arg","body","arg","arg"],stateBinder := 0,functionOperand := false,stateOperand := some #["arg","arg"],booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
