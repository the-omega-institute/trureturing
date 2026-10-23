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

/-- The same continuation law with the actual transition family explicit. -/
def scanContinues (δ : State → Op State) (U : Source) (c d : State) : Prop :=
  ∀ (h : Word) (b : State), Run δ d U h b →
    ∃ t : Word, .update ∉ t ∧ Run δ c U (t ++ h) b

abbrev equalScanArena : Arena where
  signature := supportSignature
  Law R := ∀ (U T : Source) (w : Work) (z : Address),
    (∀ a : Address, _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.readout
      (false :: (z ++ a)) U = _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.readout a T) →
    (∀ a : Address, _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.readout
      (true :: (z ++ a)) U = _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.readout a T) →
    scanContinues (R.readout () ()) U (.active false (pairStart w z))
      (.active false (pairDone w z (rightLeafReply T)))

private theorem equal_scan_bad : ¬ equalScanArena.Law supportBad := by
  intro h
  let U : Source := .mul (.of true) (.of true)
  let d : State := .active false (pairDone emptyWork [] .alpha)
  have tail : Run (supportBad.readout () ()) d U [.observer .ret] d := Run.ret rfl
  obtain ⟨t,_,run⟩ := h U (.of true) emptyWork [] (fun _ => rfl) (fun _ => rfl)
    [.observer .ret] d tail
  have same := stopped_only run
  have no := congrArg (fun s : State => match s with
    | .active _ w => w.pc.val | _ => 0) same
  norm_num [d,pairDone,pairStart,emptyWork] at no

abbrev unequalScanArena : Arena where
  signature := supportSignature
  Law R := ∀ (U A B : Source) (w : Work) (z : Address),
    (∀ a : Address, _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.readout
      (false :: (z ++ a)) U = _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.readout a A) →
    (∀ a : Address, _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.readout
      (true :: (z ++ a)) U = _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.readout a B) →
    A ≠ B → ∃ v : Work, v.pc = 29 ∧ v.row = w.row ∧ v.guardPath = w.guardPath ∧
      v.guardReply = w.guardReply ∧
      scanContinues (R.readout () ()) U (.active false (pairStart w z)) (.active false v)

private theorem unequal_scan_bad : ¬ unequalScanArena.Law supportBad := by
  intro h
  let U : Source := .mul (.of true) (.of false)
  obtain ⟨v,hv,_,_,_,cont⟩ := h U (.of true) (.of false) emptyWork []
    (fun _ => rfl) (fun _ => rfl) (by decide)
  have tail : Run (supportBad.readout () ()) (.active false v) U
      [.observer .ret] (.active false v) := Run.ret rfl
  obtain ⟨t,_,run⟩ := cont [.observer .ret] (.active false v) tail
  have same := stopped_only run
  have no := congrArg (fun s : State => match s with
    | .active _ w => w.pc.val | _ => 0) same
  norm_num [pairStart,hv] at no

abbrev completeScanArena : Arena where
  signature := supportSignature
  Law R := ∀ (U A B : Source) (w : Work),
    (∀ a : Address, _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.readout
      (false :: a) U = _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.readout a A) →
    (∀ a : Address, _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.readout
      (true :: a) U = _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.readout a B) →
    ∃ v : Work, v.pc = 8 ∧ v.row = w.row ++ [if A = B then 10 else 9] ∧
      v.guardPath = w.guardPath ∧ v.guardReply = w.guardReply ∧
      scanContinues (R.readout () ()) U (.active false (pairStart w [])) (.active false v)

private theorem complete_scan_bad : ¬ completeScanArena.Law supportBad := by
  intro h
  let U : Source := .mul (.of true) (.of false)
  obtain ⟨v,hv,_,_,_,cont⟩ := h U (.of true) (.of false) emptyWork
    (fun _ => rfl) (fun _ => rfl)
  have tail : Run (supportBad.readout () ()) (.active false v) U
      [.observer .ret] (.active false v) := Run.ret rfl
  obtain ⟨t,_,run⟩ := cont [.observer .ret] (.active false v) tail
  have same := stopped_only run
  have no := congrArg (fun s : State => match s with
    | .active _ w => w.pc.val | _ => 0) same
  norm_num [pairStart,hv] at no

def pair_equal_scanProof : Registration equalScanArena (type_of% (@pair_equal_scan)) where
  actual := supportActual
  bridge := Iff.rfl
  variation := ⟨@pair_equal_scan,supportBad,equal_scan_bad⟩
  sensitivity := ⟨fun i => ⟨supportBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,equal_scan_bad⟩,fun i => nomatch i⟩
  dependence := support_dependence

noncomputable def pair_equal_scan_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.pair_equal_scan)
      (Realization supportSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.pair_equal_scan
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.pair_equal_scanProof
  realizationSource := none
  generated := false
  arena := .source ⟨equalScanArena⟩
  objectArena := .source ⟨equalScanArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source equalScanArena ⟨pair_equal_scanProof⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize supportSignature (fun _ _ s => step s) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
    definition := some {
      owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
      name := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.Continues
      path := #[]}
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","domain","fn","fn","fn","fn","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def pair_unequal_scanProof : Registration unequalScanArena (type_of% (@pair_unequal_scan)) where
  actual := supportActual
  bridge := Iff.rfl
  variation := ⟨@pair_unequal_scan,supportBad,unequal_scan_bad⟩
  sensitivity := ⟨fun i => ⟨supportBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,unequal_scan_bad⟩,fun i => nomatch i⟩
  dependence := support_dependence

noncomputable def pair_unequal_scan_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.pair_unequal_scan)
      (Realization supportSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.pair_unequal_scan
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.pair_unequal_scanProof
  realizationSource := none
  generated := false
  arena := .source ⟨unequalScanArena⟩
  objectArena := .source ⟨unequalScanArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source unequalScanArena ⟨pair_unequal_scanProof⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize supportSignature (fun _ _ s => step s) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
    definition := some {
      owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
      name := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.Continues
      path := #[]}
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","domain","fn","fn","fn","fn","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def pair_completeProof : Registration completeScanArena (type_of% (@pair_complete)) where
  actual := supportActual
  bridge := Iff.rfl
  variation := ⟨@pair_complete,supportBad,complete_scan_bad⟩
  sensitivity := ⟨fun i => ⟨supportBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,complete_scan_bad⟩,fun i => nomatch i⟩
  dependence := support_dependence

noncomputable def pair_complete_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.pair_complete)
      (Realization supportSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.pair_complete
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.pair_completeProof
  realizationSource := none
  generated := false
  arena := .source ⟨completeScanArena⟩
  objectArena := .source ⟨completeScanArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source completeScanArena ⟨pair_completeProof⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize supportSignature (fun _ _ s => step s) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
    definition := some {
      owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
      name := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.Continues
      path := #[]}
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","domain","fn","fn","fn","fn","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]


abbrev guardArena : Arena where
  signature := supportSignature
  Law R := ∀ (U T : Source) (q : Bool) (p : Address),
    (∀ z : Address, _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.readout
      (p ++ z) U = _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.readout z T) →
    ∃ (g : Address) (ell : _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.Reply),
      (ell = .alpha ∨ ell = .beta) ∧
      _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.readout g U = ell ∧
      scanContinues (R.readout () ()) U (.active q {emptyWork with guardPath := p})
        (.active q {emptyWork with pc := 3,guardPath := g,guardReply := ell})

private theorem guard_bad : ¬ guardArena.Law supportBad := by
  intro h
  obtain ⟨g,ell,_,_,cont⟩ := h (.of true) (.of true) true [] (fun _ => rfl)
  let d : State := .active true {emptyWork with pc := 3,guardPath := g,guardReply := ell}
  have tail : Run (supportBad.readout () ()) d (.of true) [.observer .ret] d := Run.ret rfl
  obtain ⟨t,_,run⟩ := cont [.observer .ret] d tail
  have same := stopped_only run
  have no := congrArg (fun s : State => match s with
    | .active _ w => w.pc.val | _ => 0) same
  norm_num [d,emptyWork] at no

def guard_searchProof : Registration guardArena (type_of% (@guard_search)) where
  actual := supportActual
  bridge := Iff.rfl
  variation := ⟨@guard_search,supportBad,guard_bad⟩
  sensitivity := ⟨fun i => ⟨supportBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,guard_bad⟩,fun i => nomatch i⟩
  dependence := support_dependence

noncomputable def guard_search_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.guard_search)
      (Realization supportSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.guard_search
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.guard_searchProof
  realizationSource := none
  generated := false
  arena := .source ⟨guardArena⟩
  objectArena := .source ⟨guardArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source guardArena ⟨guard_searchProof⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize supportSignature (fun _ _ s => step s) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
    definition := some {
      owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
      name := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.Continues
      path := #[]}
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","domain","fn","fn","fn","fn","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]


abbrev additionSignature : Signature where
  Params := (Nat → Bool) × World
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := World
  Anchor := Empty
  finiteAnchor := inferInstance

def additionActual : Realization additionSignature :=
  realize additionSignature (fun _ p n => trajectory p.1 p.2 n) (fun i => nomatch i)

def additionBad : Realization additionSignature :=
  realize additionSignature (fun _ _ n => ⟨.entry,.of (decide (n = 1)),false⟩) (fun i => nomatch i)

abbrev additionArena : Arena where
  signature := additionSignature
  Law R := ∀ (σ : Nat → Bool) (w : World) (m k : Nat),
    R.readout () (σ,w) (m+k) =
      R.readout () ((fun i => σ (m+i)),R.readout () (σ,w) m) k

private theorem addition_bad : ¬ additionArena.Law additionBad := by
  intro h
  have no := congrArg World.source (h (fun _ => false) ⟨.entry,.of true,false⟩ 1 1)
  simp [additionBad,realize] at no
  cases no

private theorem addition_dependence : ObservationalDependence additionSignature additionActual := by
  intro i
  refine ⟨((fun _ => false),⟨.entry,.of false,false⟩),0,1,?_⟩
  intro e
  have no := congrArg World.config e
  simp [additionActual,realize,trajectory,worldEvent,step,
    _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.readout] at no

def trajectory_addProof : Registration additionArena (type_of% (@trajectory_add)) where
  actual := additionActual
  bridge := Iff.rfl
  variation := ⟨@trajectory_add,additionBad,addition_bad⟩
  sensitivity := ⟨fun i => ⟨additionBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,addition_bad⟩,fun i => nomatch i⟩
  dependence := addition_dependence

noncomputable def trajectory_add_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.trajectory_add)
      (Realization additionSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.trajectory_add
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA.trajectory_addProof
  realizationSource := none
  generated := false
  arena := .source ⟨additionArena⟩
  objectArena := .source ⟨additionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source additionArena ⟨trajectory_addProof⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize additionSignature (fun _ p n => trajectory p.1 p.2 n) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
