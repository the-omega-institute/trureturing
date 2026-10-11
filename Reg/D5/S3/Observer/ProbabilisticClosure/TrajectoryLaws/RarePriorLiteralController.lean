import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

structure CopyReadout (w : ℕ) where
  run : ℕ → CopyState w
  trace : ℕ → List Bool

abbrev signature : Signature where
  Params := ℕ
  State w := Fin w → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ w := CopyReadout w
  Anchor := Empty
  finiteAnchor := inferInstance

def observed (w : ℕ) (rom : Fin w → Bool) : CopyReadout w :=
  ⟨copyRun rom (copyEntry w),copyTrace rom (copyEntry w)⟩

def actual : Realization signature := realize signature (fun _ => observed) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ w rom => {observed w rom with trace := fun _ => []}) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (w : ℕ) (rom : Fin w → Bool),
    let v := R.readout () w rom
    (∀ (m : ℕ) (hm : m ≤ w) (r : ℕ),
      v.run (4*m+r) = copyRun rom (copyCheckpoint rom m hm) r ∧
      v.trace (4*m+r) = List.ofFn (fun i : Fin m => rom ⟨i.val,by omega⟩) ++
        copyTrace rom (copyCheckpoint rom m hm) r) ∧
    (v.run (4*w)).tape = rom ∧
    (∀ n, v.run (4*w+1+n) = {copyCheckpoint rom w le_rfl with pc := .halt})

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1 (fun _ => true)).1 1 le_rfl 0
  have ht := hh.2
  simp [rejected,realize,copyTrace] at ht

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1,(fun _ => false),(fun _ => true),?_⟩
  intro h
  have hh := congrArg (fun v : CopyReadout 1 => (v.run 4).tape 0) h
  change (copyRun (fun _ : Fin 1 => false) (copyEntry 1) 4).tape 0 =
    (copyRun (fun _ : Fin 1 => true) (copyEntry 1) 4).tape 0 at hh
  rw [(paused_copy_refinement (fun _ : Fin 1 => false)).2.1,
    (paused_copy_refinement (fun _ : Fin 1 => true)).2.1] at hh
  cases hh

def record : Registration arena (type_of% (@paused_copy_refinement)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun _ rom => paused_copy_refinement rom,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@paused_copy_refinement) (type_of% (realize signature
      (fun _ => observed) (fun e => nomatch e))) Unit Unit := {
  unitName := `RarePriorLiteralController.paused_copy_refinement.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := {stage := .evidence,objectStage := .evidence},bundleNonempty := .absent,
  readout := some (realize signature (fun _ => observed) (fun e => nomatch e)),
  variation := .absent,sensitivity := .absent,partialSensitivity := none,escapeFrom := none,
  sourceSelection := none,continuation := .unknown,familyRecord := none,
  options := #[{name := `relaxedAutoImplicit,value := .bool false}] }


namespace EncodedHead

structure Readout (w : ℕ) where
  run : ℕ → Motor w
  trace : ℕ → List Bool

abbrev signature : Signature where
  Params := ℕ
  State w := Fin w → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ w := Readout w
  Anchor := Empty
  finiteAnchor := inferInstance

def observed (w : ℕ) (rom : Fin w → Bool) : Readout w :=
  ⟨motorRun rom (motorEntry w),motorTrace rom (motorEntry w)⟩

def actual : Realization signature := realize signature (fun _ => observed) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ w rom => {observed w rom with trace := fun _ => []}) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (w : ℕ) (rom : Fin w → Bool),
    let v := R.readout () w rom
    (∀ (m : ℕ) (hm : m ≤ w) (r : ℕ),
      v.run (motorTime m+r) = motorRun rom (motorCheckpoint rom m hm) r ∧
      v.trace (motorTime m+r) = copyTrace rom (copyEntry w) (4*m) ++
        motorTrace rom (motorCheckpoint rom m hm) r) ∧
    (v.run (motorTime w)).tape = rom ∧
    (v.trace (motorTime w) = List.ofFn (fun i : Fin w => rom i)) ∧
    (∀ n, v.run (motorTime w+2*w+2+n) =
      {motorCheckpoint rom w le_rfl with probe := ⟨w,by omega⟩,pc := .halt})

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht := (h 1 (fun _ => true)).2.2.1
  simp [rejected,realize] at ht

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1,(fun _ => false),(fun _ => true),?_⟩
  intro h
  have hh := congrArg (fun v : Readout 1 => (v.run (motorTime 1)).tape 0) h
  change (motorRun (fun _ : Fin 1 => false) (motorEntry 1) (motorTime 1)).tape 0 =
    (motorRun (fun _ : Fin 1 => true) (motorEntry 1) (motorTime 1)).tape 0 at hh
  rw [(encoded_head_copy_refinement (fun _ : Fin 1 => false)).2.1,
    (encoded_head_copy_refinement (fun _ : Fin 1 => true)).2.1] at hh
  cases hh

def record : Registration arena (type_of% (@encoded_head_copy_refinement)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun _ rom => encoded_head_copy_refinement rom,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@encoded_head_copy_refinement) (type_of% (realize signature
      (fun _ => observed) (fun e => nomatch e))) Unit Unit := {
  unitName := `RarePriorLiteralController.encoded_head_copy_refinement.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.EncodedHead.record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := {stage := .evidence,objectStage := .evidence},bundleNonempty := .absent,
  readout := some (realize signature (fun _ => observed) (fun e => nomatch e)),
  variation := .absent,sensitivity := .absent,partialSensitivity := none,escapeFrom := none,
  sourceSelection := none,continuation := .unknown,familyRecord := none,
  options := #[{name := `relaxedAutoImplicit,value := .bool false}] }

end EncodedHead


namespace LiteralTransfers
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorResidentCode

structure Readout where
  code : List Bool
  run : ℕ → TransferSnapshot

abbrev signature : Signature where
  Params := Unit
  State _ := TransferSnapshot
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Readout
  Anchor := Empty
  finiteAnchor := inferInstance

def observed (_ : Unit) (s : TransferSnapshot) : Readout :=
  ⟨transferCode s,fun ticks => literalInstallStep^[ticks] (literalInstallStart s)⟩

def actual : Realization signature := realize signature (fun _ => observed) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ s => {observed () s with code := []}) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ s : TransferSnapshot,
    let v := R.readout () () s
    Function.Injective (fun q => (R.readout () () q).code) ∧
    (∀ q : TransferSnapshot, programImage.length+motorStaticImage.length+
      (R.readout () () q).code.length < literalTransferBound) ∧
    (∀ ticks : ℕ,
      let q := v.run ticks
      q.base = s.base ∧ q.header = s.header ∧ q.frame = s.frame ∧
      (∃ m, HeadControl q.installation m) ∧
      q.installation.pc ≠ .fault ∧
      (q.installation.pc ≠ .halt →
        motorRank (literalInstallStep q).installation < motorRank q.installation)) ∧
    (∀ (m : ℕ) (hm : m ≤ programWidth) (r : ℕ),
      (v.run (motorTime m+r)).installation =
        motorRun programTape (motorCheckpoint programTape m hm) r) ∧
    (v.run (motorTime programWidth)).installation.tape = programTape ∧
    (∀ slot : Fin 6,
      motorTrace (literalInstalledFrameROM (v.run (motorTime programWidth)) slot)
        (motorEntry frameWidth) (motorTime frameWidth) =
          bitCode (frameCodec (eventROM s.base.retained.pre.fields s.base.retained.operation slot))) ∧
    literalStreamedBlock s.base.retained.pre.fields s.base.retained.operation =
      eventBlock s.base.retained.pre.fields s.base.retained.operation

private def changed : TransferSnapshot :=
  {transferBoot with frame := {transferBoot.frame with latch := true}}

private theorem distinct : transferBoot ≠ changed := by
  intro h
  have hh := congrArg (fun q : TransferSnapshot => q.frame.latch) h
  change false = true at hh
  cases hh

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hi := (h transferBoot).1
  have he : transferBoot = changed := hi rfl
  exact distinct he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(),transferBoot,changed,?_⟩
  intro h
  have hc := congrArg Readout.code h
  change transferCode transferBoot = transferCode changed at hc
  exact distinct ((charged_literal_transfers transferBoot).1 hc)

def record : Registration arena (type_of% (@charged_literal_transfers)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨charged_literal_transfers,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@charged_literal_transfers) (type_of% (realize signature
      (fun _ => observed) (fun e => nomatch e))) Unit Unit := {
  unitName := `RarePriorLiteralController.charged_literal_transfers.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.LiteralTransfers.record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := {stage := .evidence,objectStage := .evidence},bundleNonempty := .absent,
  readout := some (realize signature (fun _ => observed) (fun e => nomatch e)),
  variation := .absent,sensitivity := .absent,partialSensitivity := none,escapeFrom := none,
  sourceSelection := none,continuation := .unknown,familyRecord := none,
  options := #[{name := `relaxedAutoImplicit,value := .bool false}] }

end LiteralTransfers

namespace LiteralAddress
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorResidentCode

structure Readout where
  code : AddressState → List Bool
  run : Fin frameKeyWidth → Fin frameWidth → ℕ → AddressState

abbrev signature : Signature where
  Params := Unit
  State _ := TransferSnapshot
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Readout
  Anchor := Empty
  finiteAnchor := inferInstance

def observed (_ : Unit) (s : TransferSnapshot) : Readout :=
  ⟨addressCode,fun a i => addressRun (addressEntry s a i)⟩

def actual : Realization signature := realize signature (fun _ => observed) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ s => {observed () s with code := fun _ => []}) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ s : TransferSnapshot,
    let v := R.readout () () s
    Function.Injective v.code ∧
    (∀ q : AddressState, programImage.length+addressStaticImage.length+(v.code q).length < literalAddressBound) ∧
    (∀ (a : Fin frameKeyWidth) (i : Fin frameWidth) (n : ℕ),
      let q := v.run a i n
      q.outer = s ∧ q.key = (addressEntry s a i).key ∧ q.offset = (addressEntry s a i).offset ∧
      q.control.pc ≠ .fault ∧ (q.control.pc ≠ .returned → addressRank (addressStep q) < addressRank q)) ∧
    (∀ (a : Fin frameKeyWidth) (i : Fin frameWidth), ∃ ticks, ∃ q : AddressState,
      v.run a i ticks = q ∧ q.control.pc = .returned ∧
      q.outer = s ∧ q.head.probe.val = (addressIndex a i).val ∧
      q.control.latch = s.installation.tape (addressIndex a i) ∧ ticks ≤ addressTimeBound) ∧
    (∀ (slot : Fin 6) (i : Fin frameWidth),
      let installed := literalInstallStep^[motorTime programWidth] (literalInstallStart s)
      let a := frameKey s slot
      ∃ ticks, ∃ q : AddressState,
        (R.readout () () installed).run a i ticks = q ∧ q.control.pc = .returned ∧
        q.control.latch = frameTape (eventROM s.base.retained.pre.fields s.base.retained.operation slot) i)

private def keyZero : Fin frameKeyWidth := ⟨0,by unfold frameKeyWidth; norm_num⟩
private def offsetZero : Fin frameWidth := ⟨0,by unfold frameWidth; norm_num⟩
private def baseAddress : AddressState := addressEntry transferBoot keyZero offsetZero
private def changedAddress : AddressState :=
  {baseAddress with control := {baseAddress.control with latch := true}}

private theorem address_distinct : baseAddress ≠ changedAddress := by
  intro h
  have hh := congrArg (fun q : AddressState => q.control.latch) h
  change false = true at hh
  cases hh

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hi := (h transferBoot).1
  exact address_distinct (hi rfl)

private def changed : TransferSnapshot :=
  {transferBoot with frame := {transferBoot.frame with latch := true}}

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(),transferBoot,changed,?_⟩
  intro h
  have hh := congrArg (fun v : Readout => (v.run keyZero offsetZero 0).outer.frame.latch) h
  change false = true at hh
  cases hh

def record : Registration arena (type_of% (@charged_address_execution)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨charged_address_execution,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@charged_address_execution) (type_of% (realize signature
      (fun _ => observed) (fun e => nomatch e))) Unit Unit := {
  unitName := `RarePriorLiteralController.charged_address_execution.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.LiteralAddress.record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := {stage := .evidence,objectStage := .evidence},bundleNonempty := .absent,
  readout := some (realize signature (fun _ => observed) (fun e => nomatch e)),
  variation := .absent,sensitivity := .absent,partialSensitivity := none,escapeFrom := none,
  sourceSelection := none,continuation := .unknown,familyRecord := none,
  options := #[{name := `relaxedAutoImplicit,value := .bool false}] }

end LiteralAddress


namespace TaggedProducer
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixState
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFiniteMonitor
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorResidentCode
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.LiveProducer

structure Readout where
  code : State → List Bool
  step : State → Letter → Letter → State
  run : State → Letter → Letter → ℕ → State
  execution : ℕ → State
  acquisition : Letter → ℕ → State

abbrev signature : Signature where
  Params := Unit
  State _ := TransferSnapshot × Operation × Fin 6 × Fin frameWidth
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Readout
  Anchor := Empty
  finiteAnchor := inferInstance

def observed (p : TransferSnapshot × Operation × Fin 6 × Fin frameWidth) : Readout :=
  ⟨code,step,run,run (prepared p.1 p.2.1 p.2.2.1 p.2.2.2) 0 0,
    fun x => run (step (sourceEntry p.1 p.2.2.1 p.2.2.2) x 0) 0 0⟩

def actual : Realization signature := realize signature (fun _ _ => observed) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ p => {observed p with code := fun _ => []}) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (s : TransferSnapshot) (op : Operation) (slot : Fin 6) (i : Fin frameWidth),
    let v := R.readout () () (s,op,slot,i)
    Function.Injective v.code ∧
    (∀ q : State, programImage.length+staticImage.length+(v.code q).length < bound) ∧
    (∀ (q : State) (a b c d : Letter), actualRequest q = false → freshRequest q = false →
      v.step q a b = v.step q c d) ∧
    (∀ (q : State) (a b : Letter) (t : ℕ),
      (v.run q a b t).addressed.outer.base.retained = q.addressed.outer.base.retained) ∧
    (∀ d : Runtime, runtimeStep s.base.retained.actual op = some d →
      (∃ t, ∃ q : State, v.execution t = q ∧ q.stage = .returned ∧
        returnedRuntime q = some d ∧ returnedOperation q = some op ∧
        ∃ u ≤ t, emitted (v.execution u) = some (frameTape (eventROM s.base.retained.actual.fields op slot) i)) ∧
      (∀ n : ℕ, let q := v.execution n
        q.stage ≠ .fault ∧ (q.stage ≠ .returned → rank (step q 0 0) < rank q))) ∧
    (∀ (x : Letter) (d : Runtime), runtimeStep s.base.retained.actual (.read x) = some d →
      ∃ t, ∃ q : State, v.acquisition x t = q ∧ q.stage = .returned ∧
        returnedRuntime q = some d ∧ returnedOperation q = some (.read x))

private def frameZero : Fin frameWidth := ⟨0,by unfold frameWidth; omega⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hi := (h transferBoot (.read 0) 0 frameZero).1
  let p := prepared transferBoot (.read 0) 0 frameZero
  let q : State := {p with stage := .returned}
  have he : p = q := hi rfl
  have hs := congrArg State.stage he
  change Stage.nativeKey = Stage.returned at hs
  cases hs

private theorem dependence : ObservationalDependence signature actual := by
  intro r
  cases r
  refine ⟨(),(transferBoot,.read 0,0,frameZero),(transferBoot,.read 1,0,frameZero),?_⟩
  intro h
  have he := congrArg (fun v : Readout => (v.execution 0).operation) h
  change (operationCodec (.read 0)) = operationCodec (.read 1) at he
  have hh := operationCodec.injective he
  cases hh

def record : Registration arena (type_of% (@tagged_source_commit)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tagged_source_commit,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro r
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j r)).elim
    · intro r; exact nomatch r
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tagged_source_commit) (type_of% (realize signature
      (fun _ _ => observed) (fun e => nomatch e))) Unit Unit := {
  unitName := `RarePriorLiteralController.tagged_source_commit.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.TaggedProducer.record,
  realizationSource := none,generated := false,
  arena := .source ⟨arena⟩,objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := {stage := .evidence,objectStage := .evidence},bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ => observed) (fun e => nomatch e)),
  variation := .absent,sensitivity := .absent,partialSensitivity := none,escapeFrom := none,
  sourceSelection := none,continuation := .unknown,familyRecord := none,
  options := #[{name := `relaxedAutoImplicit,value := .bool false}] }

end TaggedProducer

namespace CurrentBankFetch
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixState
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFiniteMonitor
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorResidentCode
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.LiveProducer

structure Input where
  saved : State
  image : TransferSnapshot
  actual : Fin runtimeSize → Bool
  synthetic : Fin runtimeSize → Bool
  role : Bool
  runtime : Runtime
  operation : Operation

structure Readout where
  code : Current.State → List Bool
  execution : ℕ → Current.State
  scan : CurrentBank.State → CurrentBank.State
  run : CurrentBank.State → ℕ → CurrentBank.State
  bank : CurrentBank.State → Fin runtimeSize → Bool
  fieldROM : CurrentBank.State → Fin 793800 → Bool
  acquisition : Letter → Letter → Current.State
  next : Current.State → Letter → Letter → Current.State

abbrev signature : Signature where
  Params := Unit
  State _ := Input
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Readout
  Anchor := Empty
  finiteAnchor := inferInstance

def observed (p : Input) : Readout :=
  ⟨Current.code,Current.run (Current.entry p.saved p.image p.actual p.synthetic p.role (operationCodec p.operation)) 0 0,
    CurrentBank.scanStep,CurrentBank.run,CurrentBank.bank,CurrentBank.fieldROM,
    fun x y => Current.step (Current.sourceEntry p.saved p.image p.actual p.synthetic) x y,Current.step⟩

def actual : Realization signature := realize signature (fun _ _ => observed) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ p => {observed p with code := fun _ => []}) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (saved : State) (image : TransferSnapshot) (a c : Fin runtimeSize → Bool)
      (role : Bool) (z : Runtime) (op : Operation),
    let v := R.readout () () ⟨saved,image,a,c,role,z,op⟩
    Function.Injective v.code ∧
    (∀ q : Current.State, programImage.length+Current.staticImage.length+(v.code q).length < Current.bound) ∧
    (image.installation.tape = programTape → (if role then c else a) = word (runtimeCodec z) →
      ∃ t, ∃ q : Current.State,
        v.execution t = q ∧ q.acquiring = false ∧ q.current.phase = 2 ∧
        q.current.query = word (nativeKeyCodec (z,op)) ∧
        q.current.native = scannerEntry (nativeKeyCodec (z,op)) ∧
        q.current.opcodes.tape = CurrentBank.opcodeTape 0 ∧
        q.current.actual = a ∧ q.current.synthetic = c ∧
        q.current.operation = operationCodec op ∧ q.current.role = role ∧
        q.current.addressed.outer.installation.tape = programTape) ∧
    (∀ q : CurrentBank.State, q.addressed.outer.installation.tape = programTape →
      q.query = word q.native.query → q.opcodes.tape = CurrentBank.opcodeTape q.native.pc →
      (v.scan q).native = installedGraphStep nativeTable q.native) ∧
    (∀ (q : CurrentBank.State) (n : ℕ), q.role = true → (v.run q n).actual = q.actual) ∧
    (∀ (q : CurrentBank.State) (d : Runtime), q.phase = 9 → q.bankProbe = 0 →
      q.result.tape = word (optionalRuntimeCodec (some d)) →
      ∃ t, ∃ r : CurrentBank.State, v.run q t = r ∧ r.phase = 11 ∧
        v.bank r = word (runtimeCodec d) ∧ r.operation = q.operation ∧
        (q.role = true → r.actual = q.actual)) ∧
    (∀ q : CurrentBank.State, q.pre.tape = word (runtimeCodec z) →
      v.fieldROM q = word (fieldsCodec z.fields)) ∧
    (∀ x y : Letter, v.acquisition x y = Current.entry saved image a c false (operationCodec (.read x))) ∧
    (∀ (q : Current.State) (a b c d : Letter), Current.actualRequest q = false →
      v.next q a b = v.next q c d)

private def zeroFrame : Fin frameWidth := ⟨0,by unfold frameWidth; omega⟩
private def saved : State := prepared transferBoot (.read 0) 0 zeroFrame

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hi := (h saved transferBoot (fun _ => false) (fun _ => false) false runtimeInitial (.read 0)).1
  let p := Current.entry saved transferBoot (fun _ => false) (fun _ => false) false 0
  let q : Current.State := {p with acquiring := true}
  have he : p = q := hi rfl
  have hs := congrArg Current.State.acquiring he
  change false = true at hs
  cases hs

private theorem dependence : ObservationalDependence signature actual := by
  intro r
  cases r
  let a := word (runtimeCodec runtimeInitial)
  refine ⟨(),⟨saved,transferBoot,a,a,false,runtimeInitial,.read 0⟩,
    ⟨saved,transferBoot,a,a,false,runtimeInitial,.read 1⟩,?_⟩
  intro h
  have he := congrArg (fun v : Readout => (v.execution 0).current.operation) h
  change operationCodec (.read 0) = operationCodec (.read 1) at he
  have ho := operationCodec.injective he
  cases ho

def record : Registration arena (type_of% (@current_bank_paid_fetch)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨current_bank_paid_fetch,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro r
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j r)).elim
    · intro r; exact nomatch r
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@current_bank_paid_fetch) (type_of% (realize signature
      (fun _ _ => observed) (fun e => nomatch e))) Unit Unit := {
  unitName := `RarePriorLiteralController.current_bank_paid_fetch.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.CurrentBankFetch.record,
  realizationSource := none,generated := false,
  arena := .source ⟨arena⟩,objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := {stage := .evidence,objectStage := .evidence},bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ => observed) (fun e => nomatch e)),
  variation := .absent,sensitivity := .absent,partialSensitivity := none,escapeFrom := none,
  sourceSelection := none,continuation := .unknown,familyRecord := none,
  options := #[{name := `relaxedAutoImplicit,value := .bool false}] }
end CurrentBankFetch


namespace CurrentBankPayload

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixState
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFiniteMonitor
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorResidentCode
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.LiveProducer


structure Input where
  saved : State
  image : TransferSnapshot
  actual : Fin runtimeSize → Bool
  synthetic : Fin runtimeSize → Bool
  role : Bool
  runtime : Runtime
  result : Runtime
  operation : Operation

abbrev signature : Signature where
  Params := Unit
  State _ := Input
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Current.State
  Anchor := Empty
  finiteAnchor := inferInstance

def observed (p : Input) : ℕ → Current.State :=
  Current.run (Current.entry p.saved p.image p.actual p.synthetic p.role
    (operationCodec p.operation)) 0 0

def actual : Realization signature := realize signature (fun _ _ => observed) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ p _ => {Current.entry p.saved p.image p.actual p.synthetic p.role
    (operationCodec p.operation) with acquiring := true}) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (saved : State) (image : TransferSnapshot) (a c : Fin runtimeSize → Bool)
      (role : Bool) (z d : Runtime) (op : Operation),
    image.installation.tape = programTape → (if role then c else a) = word (runtimeCodec z) →
    runtimeStep z op = some d →
    ∃ t, ∃ q : Current.State,
      R.readout () () ⟨saved,image,a,c,role,z,d,op⟩ t = q ∧
      q.acquiring = false ∧ q.current.phase = 5 ∧
      q.current.payload = word (optionalRuntimeCodec (some d)) ∧
      q.current.native.pc = 2 ∧ q.current.actual = a ∧ q.current.synthetic = c ∧
      q.current.operation = operationCodec op ∧ q.current.role = role ∧
      q.current.addressed.outer.installation.tape = programTape ∧
      q.current.result.tape = word (optionalRuntimeCodec (some d)) ∧
      q.current.pre.tape = word (runtimeCodec z) ∧
      q.current.fields.tape = word (fieldsCodec z.fields) ∧
      q.current.slot = 0 ∧ q.current.offset = ⟨0,by unfold frameWidth; omega⟩ ∧
      q.current.row = keyEntry (word (fieldsCodec z.fields))
        ⟨(operationCodec op).val*6,by have := (operationCodec op).isLt; omega⟩ ∧
      (∀ (x y : Letter), role = false → op = .read x →
        Current.run (Current.step (Current.sourceEntry saved image a c) x y) 0 0 t = q) ∧
      ∃ n, ∃ r : Current.State,
        Current.run q 0 0 n = r ∧ r.current.phase = 7 ∧
        Current.output r = some
          (frameTape (eventROM z.fields op 0) ⟨0,by unfold frameWidth; omega⟩) ∧
        r.current.actual = a ∧ r.current.synthetic = c

private def zeroFrame : Fin frameWidth := ⟨0,by unfold frameWidth; omega⟩
private def saved : State := prepared transferBoot (.read 0) 0 zeroFrame
private def image : TransferSnapshot :=
  {transferBoot with installation := {transferBoot.installation with tape := programTape}}

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let a := word (runtimeCodec runtimeInitial)
  let d := (runtimeStep runtimeInitial (.read 0)).getD runtimeInitial
  have hd : runtimeStep runtimeInitial (.read 0) = some d := by rfl
  obtain ⟨t,q,hq,ha,_⟩ := h saved image a a false runtimeInitial d (.read 0) rfl rfl hd
  have he := congrArg Current.State.acquiring hq
  have hh : true = false := he.trans ha
  cases hh

private theorem dependence : ObservationalDependence signature actual := by
  intro r
  cases r
  let a := word (runtimeCodec runtimeInitial)
  refine ⟨(),⟨saved,image,a,a,false,runtimeInitial,runtimeInitial,.read 0⟩,
    ⟨saved,image,a,a,false,runtimeInitial,runtimeInitial,.read 1⟩,?_⟩
  intro h
  have he := congrArg (fun v : ℕ → Current.State => (v 0).current.operation) h
  change operationCodec (.read 0) = operationCodec (.read 1) at he
  have ho := operationCodec.injective he
  cases ho

def record : Registration arena (type_of% (@current_bank_native_payload)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨current_bank_native_payload,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro r
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j r)).elim
    · intro r; exact nomatch r
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@current_bank_native_payload) (type_of% (realize signature
      (fun _ _ => observed) (fun e => nomatch e))) Unit Unit := {
  unitName := `RarePriorLiteralController.current_bank_native_payload.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.CurrentBankPayload.record,
  realizationSource := none,generated := false,
  arena := .source ⟨arena⟩,objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := {stage := .evidence,objectStage := .evidence},bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ => observed) (fun e => nomatch e)),
  variation := .absent,sensitivity := .absent,partialSensitivity := none,escapeFrom := none,
  sourceSelection := none,continuation := .unknown,familyRecord := none,
  options := #[{name := `relaxedAutoImplicit,value := .bool false}] }
end CurrentBankPayload


namespace CurrentBankFrames

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixState
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFiniteMonitor
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorResidentCode
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.LiveProducer


structure Input where
  saved : State
  image : TransferSnapshot
  actual : Fin runtimeSize → Bool
  synthetic : Fin runtimeSize → Bool
  role : Bool
  runtime : Runtime
  result : Runtime
  operation : Operation

abbrev signature : Signature where
  Params := Unit
  State _ := Input
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Current.State
  Anchor := Empty
  finiteAnchor := inferInstance

def observed (p : Input) : ℕ → Current.State :=
  Current.run (Current.entry p.saved p.image p.actual p.synthetic p.role
    (operationCodec p.operation)) 0 0

def actual : Realization signature := realize signature (fun _ _ => observed) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ p _ => {Current.entry p.saved p.image p.actual p.synthetic p.role
    (operationCodec p.operation) with acquiring := true}) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (saved : State) (image : TransferSnapshot) (a c : Fin runtimeSize → Bool)
      (role : Bool) (z d : Runtime) (op : Operation),
    image.installation.tape = programTape → (if role then c else a) = word (runtimeCodec z) →
    runtimeStep z op = some d →
    ∃ tp, ∃ p : Current.State, ∃ tr, ∃ q : Current.State,
      R.readout () () ⟨saved,image,a,c,role,z,d,op⟩ tp = p ∧
      p.acquiring = false ∧ p.current.phase = 5 ∧
      Current.run p 0 0 tr = q ∧ q.current.phase = 11 ∧
      q.current.actual = (if role then a else word (runtimeCodec d)) ∧
      q.current.synthetic = (if role then word (runtimeCodec d) else c) ∧
      q.current.operation = operationCodec op ∧ q.current.role = role ∧
      q.current.addressed.outer.installation.tape = programTape ∧
      CurrentBank.trace p.current tr =
        (List.ofFn (fun slot : Fin 6 => bitCode
          (frameCodec (eventROM z.fields op slot)))).flatten ∧
      CurrentBank.trace (CurrentBank.entry image a c role (operationCodec op)) (tp+tr) =
        (List.ofFn (fun slot : Fin 6 => bitCode
          (frameCodec (eventROM z.fields op slot)))).flatten ∧
      (∀ k, k ≤ tp+tr → ∃ suffix : List Bool,
        (List.ofFn (fun slot : Fin 6 => bitCode
          (frameCodec (eventROM z.fields op slot)))).flatten =
          CurrentBank.trace
            (CurrentBank.entry image a c role (operationCodec op)) k ++ suffix) ∧
      (∀ n, (CurrentBank.run
        (CurrentBank.entry image a c role (operationCodec op)) n).phase ≠ 12 ∧
        (role = true → (CurrentBank.run
          (CurrentBank.entry image a c role (operationCodec op)) n).actual = a)) ∧
      ((List.ofFn (fun slot : Fin 6 => decodeFrame
        (bitCode (frameCodec (eventROM z.fields op slot))))).filterMap id).map original =
          eventBlock z.fields op ∧
      (∀ (x y : Letter), role = false → op = .read x →
        Current.run (Current.step (Current.sourceEntry saved image a c) x y)
          0 0 (tp+tr) = q)


private def zeroFrame : Fin frameWidth := ⟨0,by unfold frameWidth; omega⟩
private def saved : State := prepared transferBoot (.read 0) 0 zeroFrame
private def image : TransferSnapshot :=
  {transferBoot with installation := {transferBoot.installation with tape := programTape}}

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let a := word (runtimeCodec runtimeInitial)
  let d := (runtimeStep runtimeInitial (.read 0)).getD runtimeInitial
  have hd : runtimeStep runtimeInitial (.read 0) = some d := by rfl
  obtain ⟨tp,p,tr,q,hp,ha,_⟩ := h saved image a a false runtimeInitial d (.read 0) rfl rfl hd
  have he := congrArg Current.State.acquiring hp
  have hh : true = false := he.trans ha
  cases hh

private theorem dependence : ObservationalDependence signature actual := by
  intro r
  cases r
  let a := word (runtimeCodec runtimeInitial)
  refine ⟨(),⟨saved,image,a,a,false,runtimeInitial,runtimeInitial,.read 0⟩,
    ⟨saved,image,a,a,false,runtimeInitial,runtimeInitial,.read 1⟩,?_⟩
  intro h
  have he := congrArg (fun v : ℕ → Current.State => (v 0).current.operation) h
  change operationCodec (.read 0) = operationCodec (.read 1) at he
  have ho := operationCodec.injective he
  cases ho

def record : Registration arena (type_of% (@current_bank_original_frames)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨current_bank_original_frames,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro r
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j r)).elim
    · intro r; exact nomatch r
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@current_bank_original_frames) (type_of% (realize signature
      (fun _ _ => observed) (fun e => nomatch e))) Unit Unit := {
  unitName := `RarePriorLiteralController.current_bank_original_frames.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.CurrentBankFrames.record,
  realizationSource := none,generated := false,
  arena := .source ⟨arena⟩,objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := {stage := .evidence,objectStage := .evidence},bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ => observed) (fun e => nomatch e)),
  variation := .absent,sensitivity := .absent,partialSensitivity := none,escapeFrom := none,
  sourceSelection := none,continuation := .unknown,familyRecord := none,
  options := #[{name := `relaxedAutoImplicit,value := .bool false}] }
end CurrentBankFrames

namespace CurrentBankCoreReturn

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixState
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFiniteMonitor
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorResidentCode
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.LiveProducer

structure Input where
  saved : State
  image : TransferSnapshot
  actual : Fin runtimeSize → Bool
  synthetic : Fin runtimeSize → Bool
  role : Bool
  runtime : Runtime
  result : Runtime
  operation : Operation

abbrev signature : Signature where
  Params := Unit
  State _ := Input
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Return.State
  Anchor := Empty
  finiteAnchor := inferInstance

def observed (p : Input) : ℕ → Return.State :=
  Return.run (Return.entry (Current.entry p.saved p.image p.actual p.synthetic p.role
    (operationCodec p.operation))) 0 0

def actual : Realization signature := realize signature (fun _ _ => observed) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ p _ => {Return.entry (Current.entry p.saved p.image p.actual p.synthetic p.role
    (operationCodec p.operation)) with pc := 8}) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (saved : State) (image : TransferSnapshot) (a c : Fin runtimeSize → Bool)
      (role : Bool) (z d : Runtime) (op : Operation),
    image.installation.tape = programTape → (if role then c else a) = word (runtimeCodec z) →
    runtimeStep z op = some d →
    Function.Injective Return.code ∧
    (∀ s : Return.State, programImage.length+Return.staticImage.length+
      (Return.code s).length < Return.bound) ∧
    (∀ (s : Return.State) (x y u v : Letter), Return.actualRequest s = false →
      Return.step s x y = Return.step s u v) ∧
    ∃ t, ∃ r : Return.State,
      R.readout () () ⟨saved,image,a,c,role,z,d,op⟩ t = r ∧
      r = Return.coreReady saved r.current.current.addressed.outer
        (if role then a else word (runtimeCodec d))
        (if role then word (runtimeCodec d) else c) ∧
      r.current.current.addressed.outer.installation.tape = programTape ∧
      (∀ w : Runtime, r.current.current.actual = word (runtimeCodec w) → Return.NextRound r w)

private def zeroFrame : Fin frameWidth := ⟨0,by unfold frameWidth; omega⟩
private def saved : State := prepared transferBoot (.read 0) 0 zeroFrame
private def image : TransferSnapshot :=
  {transferBoot with installation := {transferBoot.installation with tape := programTape}}

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let a := word (runtimeCodec runtimeInitial)
  let d := (runtimeStep runtimeInitial (.read 0)).getD runtimeInitial
  have hd : runtimeStep runtimeInitial (.read 0) = some d := by rfl
  obtain ⟨_,_,_,t,r,hr,hready,_⟩ := h saved image a a false runtimeInitial d (.read 0) rfl rfl hd
  have he : (8 : Fin 9) = r.pc := congrArg Return.State.pc hr
  have hh : r.pc = 4 := congrArg Return.State.pc hready
  have hn := he.trans hh
  cases hn

private theorem dependence : ObservationalDependence signature actual := by
  intro r
  cases r
  let a := word (runtimeCodec runtimeInitial)
  refine ⟨(),⟨saved,image,a,a,false,runtimeInitial,runtimeInitial,.read 0⟩,
    ⟨saved,image,a,a,false,runtimeInitial,runtimeInitial,.read 1⟩,?_⟩
  intro h
  have he := congrArg (fun v : ℕ → Return.State => (v 0).current.current.operation) h
  simp only [actual,realize,observed,Return.run,Function.iterate_zero,id_eq] at he
  change operationCodec (.read 0) = operationCodec (.read 1) at he
  have ho := operationCodec.injective he
  cases ho

def record : Registration arena (type_of% (@current_bank_paid_core_return)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨current_bank_paid_core_return,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro r
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j r)).elim
    · intro r; exact nomatch r
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@current_bank_paid_core_return) (type_of% (realize signature
      (fun _ _ => observed) (fun e => nomatch e))) Unit Unit := {
  unitName := `RarePriorLiteralController.current_bank_paid_core_return.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.CurrentBankCoreReturn.record,
  realizationSource := none,generated := false,
  arena := .source ⟨arena⟩,objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := {stage := .evidence,objectStage := .evidence},bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ => observed) (fun e => nomatch e)),
  variation := .absent,sensitivity := .absent,partialSensitivity := none,escapeFrom := none,
  sourceSelection := none,continuation := .unknown,familyRecord := none,
  options := #[{name := `relaxedAutoImplicit,value := .bool false}] }
end CurrentBankCoreReturn

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
