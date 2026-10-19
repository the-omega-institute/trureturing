/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/TransfersAddress
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/TransfersAddress
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Charged literal installation and unary address execution read original event bits. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.EncodedHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option Elab.async false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder NativeFullResidual
open RarePriorFiniteMonitor RarePriorResidentCode RarePriorSerialExecution
def transferBoot : TransferSnapshot :=
  ⟨bootSnapshot,motorEntry programWidth,motorEntry 793800,motorEntry frameWidth⟩

def renderWidth : ℕ := retainedSize+copyWidth programWidth+copyWidth 793800+
  copyWidth frameWidth+8+1

private theorem render_code_length (s : RenderSnapshot) : (snapshot s).length = renderWidth := by
  simp only [snapshot,renderWidth,List.length_append,bit_code_length,copy_charge,
    List.length_cons,List.length_nil]

@[irreducible] def transferCode (s : TransferSnapshot) : List Bool :=
  snapshot s.base ++ motorCode s.installation ++ motorCode s.header ++ motorCode s.frame

def literalTransferBound : ℕ := programWidth+motorStaticWidth+renderWidth+
  motorWidth programWidth+motorWidth 793800+motorWidth frameWidth+1

private theorem transfer_charge (s : TransferSnapshot) :
    programImage.length+motorStaticImage.length+(transferCode s).length < literalTransferBound := by
  simp only [transferCode,List.length_append,render_code_length,motor_code_length,
    programImage,List.length_ofFn,motor_static_length,literalTransferBound]
  omega

private theorem transfer_encoding : Function.Injective transferCode := by
  intro s t h
  simp only [transferCode,List.append_assoc] at h
  obtain ⟨hb,h⟩ := split_block (snapshot s.base) (snapshot t.base) _ _ renderWidth
    (render_code_length _) (render_code_length _) h
  obtain ⟨hi,h⟩ := split_block (motorCode s.installation) (motorCode t.installation) _ _
    (motorWidth programWidth) (motor_code_length _) (motor_code_length _) h
  obtain ⟨hh,hf⟩ := split_block (motorCode s.header) (motorCode t.header) _ _
    (motorWidth 793800) (motor_code_length _) (motor_code_length _) h
  exact TransferSnapshot.ext (snapshot_encoding hb) (motor_encoding hi)
    (motor_encoding hh) (motor_encoding hf)

/-- This instruction only advances the literal installation motor. All source
runtimes, scanner flights and both other motors are retained unchanged. -/
def literalInstallStep (s : TransferSnapshot) : TransferSnapshot :=
  {s with installation := motorStep programTape s.installation}

def literalInstallStart (s : TransferSnapshot) : TransferSnapshot :=
  {s with installation := motorEntry programWidth}

private theorem literal_install_run (s : TransferSnapshot) (ticks : ℕ) :
    literalInstallStep^[ticks] s =
      {s with installation := motorRun programTape s.installation ticks} := by
  let lift : Motor programWidth → TransferSnapshot := fun q => {s with installation := q}
  have h : Function.Semiconj lift (motorStep programTape) literalInstallStep := fun _ => rfl
  exact (h.iterate_right ticks s.installation).symm

/-- Original rows remain macro-addressed projections. The literal motor does
not interpret frameAddress or compute its product arithmetic. -/
def literalInstalledFrameROM (s : TransferSnapshot) (slot : Fin 6) : Fin frameWidth → Bool :=
  fun i => s.installation.tape (frameAddress s.base slot i)

noncomputable def literalStreamedBlock (f : FiniteFields) (op : Operation) : List OriginalEvent :=
  ((List.ofFn (fun slot : Fin 6 => decodeFrame
    (motorTrace (frameTape (eventROM f op slot)) (motorEntry frameWidth)
      (motorTime frameWidth)))).filterMap id).map original

private theorem literal_streamed_block (f : FiniteFields) (op : Operation) :
    literalStreamedBlock f op = streamedBlock f op := by
  have ht (slot : Fin 6) := (motor_prefix (frameTape (eventROM f op slot)) frameWidth le_rfl).2
  simp only [literalStreamedBlock,streamedBlock,ht,renderFrame]

/-- The install attachment has a live all-cut head invariant and strictly
falling deterministic rank. It installs the actual image, keeps all concurrent
states charged and reconstructs original frame output at the same checkpoints.
It supplies no adaptive dispatch, image-address execution or source commit. -/
theorem charged_literal_transfers (s : TransferSnapshot) :
    Function.Injective transferCode ∧
    (∀ q : TransferSnapshot, programImage.length+motorStaticImage.length+
      (transferCode q).length < literalTransferBound) ∧
    (∀ ticks : ℕ,
      let q := literalInstallStep^[ticks] (literalInstallStart s)
      q.base = s.base ∧ q.header = s.header ∧ q.frame = s.frame ∧
      (∃ m, HeadControl q.installation m) ∧
      q.installation.pc ≠ .fault ∧
      (q.installation.pc ≠ .halt →
        motorRank (literalInstallStep q).installation < motorRank q.installation)) ∧
    (∀ (m : ℕ) (hm : m ≤ programWidth) (r : ℕ),
      (literalInstallStep^[motorTime m+r] (literalInstallStart s)).installation =
        motorRun programTape (motorCheckpoint programTape m hm) r) ∧
    (literalInstallStep^[motorTime programWidth] (literalInstallStart s)).installation.tape =
      programTape ∧
    (∀ slot : Fin 6,
      motorTrace (literalInstalledFrameROM
        (literalInstallStep^[motorTime programWidth] (literalInstallStart s)) slot)
        (motorEntry frameWidth) (motorTime frameWidth) =
          bitCode (frameCodec (eventROM s.base.retained.pre.fields s.base.retained.operation slot))) ∧
    literalStreamedBlock s.base.retained.pre.fields s.base.retained.operation =
      eventBlock s.base.retained.pre.fields s.base.retained.operation := by
  refine ⟨transfer_encoding,transfer_charge,?_,?_,?_,?_,?_⟩
  · intro ticks
    dsimp only
    rw [literal_install_run]
    have inv := motor_all_cuts programTape ticks
    refine ⟨rfl,rfl,rfl,inv,?_,?_⟩
    · obtain ⟨m,hm⟩ := inv
      intro hp
      change (motorRun programTape (motorEntry programWidth) ticks).pc = .fault at hp
      have hf : False := by simpa [HeadControl,hp] using hm.2.2
      exact hf
    · obtain ⟨m,hm⟩ := inv
      exact (head_control_step programTape _ m hm).choose_spec.2
  · intro m hm r
    rw [literal_install_run]
    exact ((encoded_head_copy_refinement programTape).1 m hm r).1
  · rw [literal_install_run]
    exact (encoded_head_copy_refinement programTape).2.1
  · intro slot
    have tape : (literalInstallStep^[motorTime programWidth]
        (literalInstallStart s)).installation.tape = programTape := by
      rw [literal_install_run]
      exact (encoded_head_copy_refinement programTape).2.1
    have context : (literalInstallStep^[motorTime programWidth]
        (literalInstallStart s)).base = s.base := by rw [literal_install_run]; rfl
    have rom : literalInstalledFrameROM
        (literalInstallStep^[motorTime programWidth] (literalInstallStart s)) slot =
        frameTape (eventROM s.base.retained.pre.fields s.base.retained.operation slot) := by
      unfold literalInstalledFrameROM
      rw [tape,context]
      exact program_frame s.base slot
    rw [rom,(motor_prefix _ frameWidth le_rfl).2]
    exact (streamed_original_events _ _).1 slot |>.1
  · rw [literal_streamed_block]
    exact (streamed_original_events _ _).2


/-- The three physical rails have fixed dimensions from the existing image. -/
@[irreducible] def frameBase : ℕ := B0+headerWidth
@[irreducible] def frameKeyWidth : ℕ := 793800*24

def zeroAddressROM : Fin programWidth → Bool := fun _ => false

inductive AddressPC where
  | baseTest | keyRead | keyBranch | strideTest | offsetRead | offsetBranch
  | increment | returnBase | returnStride | baseMove | keyMove | strideMove | offsetMove
  | seekAddress | readProgram | returned | fault
  deriving DecidableEq

instance : Fintype AddressPC :=
  ⟨{.baseTest,.keyRead,.keyBranch,.strideTest,.offsetRead,.offsetBranch,
    .increment,.returnBase,.returnStride,.baseMove,.keyMove,.strideMove,.offsetMove,
    .seekAddress,.readProgram,.returned,.fault},by intro p; cases p <;> simp⟩

@[ext] structure AddressControl where
  baseProbe : Fin (frameBase+1)
  keyProbe : Fin (frameKeyWidth+1)
  strideProbe : Fin (frameWidth+1)
  offsetProbe : Fin (frameWidth+1)
  pc : AddressPC
  returnBase : Bool
  returnStride : Bool
  latch : Bool
  deriving DecidableEq

/-- The key and offset are raw bit tapes. Their numerical values only occur
in the external entry relation. All concurrent outer states remain retained. -/
@[ext] structure AddressState where
  outer : TransferSnapshot
  control : AddressControl
  key : Fin frameKeyWidth → Bool
  offset : Fin frameWidth → Bool
  head : Motor programWidth
  deriving DecidableEq

/-- Address formation uses bit tests, adjacent rail motion and the paid
encoded-head carry motor. Neither multiplication nor frameAddress occurs in
an instruction. ReturnBase and ReturnStride each test one continuation bit. -/
def addressStep (s : AddressState) : AddressState :=
  match s.control.pc with
  | .baseTest => if endCell s.control.baseProbe then
      {s with control := {s.control with pc := .keyRead,returnBase := false,returnStride := true,latch := false}}
    else {s with control := {s.control with pc := .increment,returnBase := true,returnStride := false}}
  | .keyRead => if h : s.control.keyProbe.val < frameKeyWidth then
      {s with control := {s.control with latch := s.key ⟨s.control.keyProbe.val,h⟩,pc := .keyBranch}}
    else {s with control := {s.control with pc := .fault}}
  | .keyBranch => if s.control.latch then
      {s with control := {s.control with strideProbe := 0,pc := .strideTest}}
    else {s with control := {s.control with pc := .offsetRead,returnBase := false,returnStride := false,latch := false}}
  | .strideTest => if endCell s.control.strideProbe then
      {s with control := {s.control with pc := .keyMove}}
    else {s with control := {s.control with pc := .increment,returnBase := false,returnStride := true}}
  | .offsetRead => if h : s.control.offsetProbe.val < frameWidth then
      {s with control := {s.control with latch := s.offset ⟨s.control.offsetProbe.val,h⟩,pc := .offsetBranch}}
    else {s with control := {s.control with pc := .fault}}
  | .offsetBranch => if s.control.latch then
      {s with control := {s.control with pc := .increment,returnBase := false,returnStride := false}}
    else {s with control := {s.control with pc := .seekAddress}}
  | .increment => {s with head := motorStep zeroAddressROM s.head,control := {s.control with pc := if s.head.pc = .carry then .returnBase else .increment}}
  | .returnBase => if s.control.returnBase then
      {s with control := {s.control with pc := .baseMove}}
    else {s with control := {s.control with pc := .returnStride}}
  | .returnStride => if s.control.returnStride then
      {s with control := {s.control with pc := .strideMove}}
    else {s with control := {s.control with pc := .offsetMove}}
  | .baseMove => match nextCell s.control.baseProbe with
      | none => {s with control := {s.control with pc := .fault}}
      | some i => {s with control := {s.control with baseProbe := i,pc := .baseTest}}
  | .keyMove => match nextCell s.control.keyProbe with
      | none => {s with control := {s.control with pc := .fault}}
      | some i => {s with control := {s.control with keyProbe := i,strideProbe := 0,latch := false,pc := .keyRead}}
  | .strideMove => match nextCell s.control.strideProbe with
      | none => {s with control := {s.control with pc := .fault}}
      | some i => {s with control := {s.control with strideProbe := i,pc := .strideTest}}
  | .offsetMove => match nextCell s.control.offsetProbe with
      | none => {s with control := {s.control with pc := .fault}}
      | some i => {s with control := {s.control with offsetProbe := i,latch := false,pc := .offsetRead}}
  | .seekAddress => {s with head := motorStep zeroAddressROM s.head,control := {s.control with pc := if s.head.pc = .limit then .readProgram else .seekAddress}}
  | .readProgram => if h : s.head.probe.val < programWidth then
      {s with control := {s.control with latch := s.outer.installation.tape ⟨s.head.probe.val,h⟩,pc := .returned}}
    else {s with control := {s.control with pc := .fault}}
  | .returned | .fault => s

def addressRun (s : AddressState) (ticks : ℕ) : AddressState := addressStep^[ticks] s

private theorem address_run_add (s : AddressState) (m n : ℕ) :
    addressRun s (m+n) = addressRun (addressRun s m) n := by
  rw [addressRun,Nat.add_comm,Function.iterate_add_apply]
  rfl

/-- Entry is the subroutine's explicit raw-input relation. The outer controller
must still prepare these key and offset tapes by paid instructions. -/
def addressEntry (s : TransferSnapshot) (key : Fin frameKeyWidth) (offset : Fin frameWidth) : AddressState :=
  ⟨s,⟨0,0,0,0,.baseTest,true,false,false⟩,
    (fun i => decide (i.val < key.val)),(fun i => decide (i.val < offset.val)),motorEntry programWidth⟩

private def withHead (s : AddressState) (m : ℕ) (hm : m ≤ programWidth) (pc : AddressPC) : AddressState :=
  {s with head := motorCheckpoint zeroAddressROM m hm,control := {s.control with pc := pc}}

private theorem address_seek (s : AddressState) (m : ℕ) (hm : m ≤ programWidth)
    (pc : AddressPC) (hp : pc = .increment ∨ pc = .seekAddress)
    (j : ℕ) (hj : j ≤ m) :
    addressRun (withHead s m hm pc) (2*j) =
      {withHead s m hm pc with
        head := {motorCheckpoint zeroAddressROM m hm with probe := ⟨j,by omega⟩}} := by
  induction j with
  | zero => simp [addressRun,withHead,motorCheckpoint,encodeCopy]
  | succ j ih =>
    have hjm : j < m := by omega
    have hjw : j < programWidth := by omega
    rw [show 2*(j+1)=2+2*j by omega,addressRun,Function.iterate_add_apply]
    change addressRun (addressRun (withHead s m hm pc) (2*j)) 2 = _
    rw [ih (by omega)]
    rcases hp with rfl | rfl <;> simp [addressRun,Function.iterate_succ_apply',addressStep,withHead,motorStep,
      motorCheckpoint,encodeCopy,copyCheckpoint,hjm,nextCell,hjw]

private theorem address_increment (s : AddressState) (m : ℕ) (hm : m < programWidth) :
    addressRun (withHead s m (by omega) .increment) (2*m+6) =
      withHead s (m+1) (by omega) .returnBase := by
  have hs := address_seek s m (by omega) .increment (Or.inl rfl) m le_rfl
  have hc := (motor_cycle zeroAddressROM m hm).1
  rw [Nat.add_comm (2*m) 6,addressRun,Function.iterate_add_apply]
  change addressRun (addressRun (withHead s m (by omega) .increment) (2*m)) 6 = _
  rw [hs]
  apply AddressState.ext
  · simp [addressRun,Function.iterate_succ_apply',addressStep,withHead,motorStep,endCell,
      motorCheckpoint,encodeCopy,copyCheckpoint,hm,show m ≠ programWidth by omega]
  · simp [addressRun,Function.iterate_succ_apply',addressStep,withHead,motorStep,endCell,
      motorCheckpoint,encodeCopy,copyCheckpoint,hm,show m ≠ programWidth by omega]
  · simp [addressRun,Function.iterate_succ_apply',addressStep,withHead,motorStep,endCell,
      motorCheckpoint,encodeCopy,copyCheckpoint,hm,show m ≠ programWidth by omega]
  · simp [addressRun,Function.iterate_succ_apply',addressStep,withHead,motorStep,endCell,
      motorCheckpoint,encodeCopy,copyCheckpoint,hm,show m ≠ programWidth by omega]
  · have hc6 : motorRun zeroAddressROM
        {motorCheckpoint zeroAddressROM m (by omega) with probe := ⟨m,by omega⟩} 6 =
        motorCheckpoint zeroAddressROM (m+1) (by omega) := by
      have ha : motorRun zeroAddressROM (motorCheckpoint zeroAddressROM m (by omega)) (2*m+6) =
          motorRun zeroAddressROM
            (motorRun zeroAddressROM (motorCheckpoint zeroAddressROM m (by omega)) (2*m)) 6 := by
        rw [Nat.add_comm (2*m) 6,motorRun,Function.iterate_add_apply]
        rfl
      rw [ha,(motor_seek zeroAddressROM m (by omega) m le_rfl).1] at hc
      exact hc
    simpa [motorRun,addressRun,Function.iterate_succ_apply',addressStep,withHead,
      motorStep,endCell,motorCheckpoint,encodeCopy,copyCheckpoint,
      hm,show m ≠ programWidth by omega] using hc6


private def baseCheckpoint (s : AddressState) (j m : ℕ) (hj : j ≤ frameBase)
    (hm : m ≤ programWidth) : AddressState :=
  {withHead s m hm .baseTest with control :=
    {s.control with baseProbe := ⟨j,by omega⟩,pc := .baseTest,returnBase := true,returnStride := false}}

private def baseTicks (m q : ℕ) : ℕ := q*q+(2*m+8)*q

private theorem base_cycle (s : AddressState) (j m : ℕ) (hj : j < frameBase)
    (hm : m < programWidth) :
    addressRun (baseCheckpoint s j m (by omega) (by omega)) (2*m+9) =
      baseCheckpoint s (j+1) (m+1) (by omega) (by omega) := by
  have hs : addressStep (baseCheckpoint s j m (by omega) (by omega)) =
      withHead (baseCheckpoint s j m (by omega) (by omega)) m (by omega) .increment := by
    simp [addressStep,baseCheckpoint,withHead,endCell,show j ≠ frameBase by omega]
  rw [show 2*m+9=1+(2*m+6)+2 by omega,address_run_add,address_run_add]
  change addressRun (addressRun (addressStep
    (baseCheckpoint s j m (by omega) (by omega))) (2*m+6)) 2 = _
  rw [hs,address_increment _ m hm]
  simp [addressRun,Function.iterate_succ_apply',addressStep,baseCheckpoint,withHead,nextCell,hj]

private theorem base_prefix (s : AddressState) (j m q : ℕ)
    (hj : j+q ≤ frameBase) (hm : m+q ≤ programWidth) :
    addressRun (baseCheckpoint s j m (by omega) (by omega)) (baseTicks m q) =
      baseCheckpoint s (j+q) (m+q) hj hm := by
  induction q with
  | zero => simp [baseTicks,addressRun,baseCheckpoint,withHead]
  | succ q ih =>
    have ht : baseTicks m (q+1)=baseTicks m q+(2*(m+q)+9) := by unfold baseTicks; ring
    rw [ht,address_run_add]
    rw [ih (by omega) (by omega)]
    simpa only [Nat.add_assoc] using base_cycle s (j+q) (m+q) (by omega) (by omega)


private def strideCheckpoint (s : AddressState) (j m : ℕ) (hj : j ≤ frameWidth)
    (hm : m ≤ programWidth) : AddressState :=
  {withHead s m hm .strideTest with control :=
    {s.control with strideProbe := ⟨j,by omega⟩,pc := .strideTest,returnBase := false,returnStride := true,latch := true}}

private def strideTicks (m q : ℕ) : ℕ := q*q+(2*m+9)*q

private theorem stride_cycle (s : AddressState) (j m : ℕ) (hj : j < frameWidth)
    (hm : m < programWidth) :
    addressRun (strideCheckpoint s j m (by omega) (by omega)) (2*m+10) =
      strideCheckpoint s (j+1) (m+1) (by omega) (by omega) := by
  have hs : addressStep (strideCheckpoint s j m (by omega) (by omega)) =
      withHead (strideCheckpoint s j m (by omega) (by omega)) m (by omega) .increment := by
    simp [addressStep,strideCheckpoint,withHead,endCell,show j ≠ frameWidth by omega]
  rw [show 2*m+10=1+(2*m+6)+3 by omega,address_run_add,address_run_add]
  change addressRun (addressRun (addressStep
    (strideCheckpoint s j m (by omega) (by omega))) (2*m+6)) 3 = _
  rw [hs,address_increment _ m hm]
  simp [addressRun,Function.iterate_succ_apply',addressStep,strideCheckpoint,withHead,nextCell,hj]

private theorem stride_prefix (s : AddressState) (j m q : ℕ)
    (hj : j+q ≤ frameWidth) (hm : m+q ≤ programWidth) :
    addressRun (strideCheckpoint s j m (by omega) (by omega)) (strideTicks m q) =
      strideCheckpoint s (j+q) (m+q) hj hm := by
  induction q with
  | zero => simp [strideTicks,addressRun,strideCheckpoint,withHead]
  | succ q ih =>
    have ht : strideTicks m (q+1)=strideTicks m q+(2*(m+q)+10) := by unfold strideTicks; ring
    rw [ht,address_run_add]
    rw [ih (by omega) (by omega)]
    simpa only [Nat.add_assoc] using stride_cycle s (j+q) (m+q) (by omega) (by omega)

private def keyCheckpoint (s : AddressState) (j m : ℕ) (hj : j ≤ frameKeyWidth)
    (hm : m ≤ programWidth) : AddressState :=
  {withHead s m hm .keyRead with control :=
    {s.control with keyProbe := ⟨j,by omega⟩,strideProbe := 0,pc := .keyRead,returnBase := false,returnStride := true,latch := false}}

private def keyTicks (m q : ℕ) : ℕ :=
  (q*frameWidth)*(q*frameWidth)+(2*m+9)*(q*frameWidth)+4*q

private theorem key_cycle (s : AddressState) (j m : ℕ) (hj : j < frameKeyWidth)
    (hk : s.key ⟨j,hj⟩ = true) (hm : m+frameWidth ≤ programWidth) :
    addressRun (keyCheckpoint s j m (by omega) (by omega)) (strideTicks m frameWidth+4) =
      keyCheckpoint s (j+1) (m+frameWidth) (by omega) hm := by
  have hs : addressRun (keyCheckpoint s j m (by omega) (by omega)) 2 =
      strideCheckpoint (keyCheckpoint s j m (by omega) (by omega)) 0 m (by omega) (by omega) := by
    simp [addressRun,Function.iterate_succ_apply',addressStep,keyCheckpoint,strideCheckpoint,withHead,hj,hk]
  rw [show strideTicks m frameWidth+4=2+strideTicks m frameWidth+2 by omega,
    address_run_add,address_run_add,hs,stride_prefix _ 0 m frameWidth (by omega) hm]
  simp [addressRun,Function.iterate_succ_apply',addressStep,keyCheckpoint,strideCheckpoint,
    withHead,endCell,nextCell,hj]

private theorem key_prefix (s : AddressState) (j m q : ℕ)
    (hj : j+q ≤ frameKeyWidth) (hm : m+q*frameWidth ≤ programWidth)
    (hk : ∀ (i : ℕ) (hi : i < q), s.key ⟨j+i,by omega⟩ = true) :
    addressRun (keyCheckpoint s j m (by omega) (by omega)) (keyTicks m q) =
      keyCheckpoint s (j+q) (m+q*frameWidth) hj hm := by
  induction q with
  | zero => simp [keyTicks,addressRun,keyCheckpoint,withHead]
  | succ q ih =>
    have ht : keyTicks m (q+1)=keyTicks m q+strideTicks (m+q*frameWidth) frameWidth+4 := by
      unfold keyTicks strideTicks; ring
    rw [ht,show keyTicks m q+strideTicks (m+q*frameWidth) frameWidth+4 =
      keyTicks m q+(strideTicks (m+q*frameWidth) frameWidth+4) by omega,address_run_add]
    rw [ih (by omega) (by nlinarith) (by intro i hi; exact hk i (by omega))]
    have hc := key_cycle s (j+q) (m+q*frameWidth) (by omega) (hk q (by omega)) (by nlinarith)
    simpa [Nat.add_mul,Nat.add_assoc] using hc

private def offsetCheckpoint (s : AddressState) (j m : ℕ) (hj : j ≤ frameWidth)
    (hm : m ≤ programWidth) : AddressState :=
  {withHead s m hm .offsetRead with control :=
    {s.control with offsetProbe := ⟨j,by omega⟩,pc := .offsetRead,returnBase := false,returnStride := false,latch := false}}

private def offsetTicks (m q : ℕ) : ℕ := q*q+(2*m+10)*q

private theorem offset_cycle (s : AddressState) (j m : ℕ) (hj : j < frameWidth)
    (hk : s.offset ⟨j,hj⟩ = true) (hm : m < programWidth) :
    addressRun (offsetCheckpoint s j m (by omega) (by omega)) (2*m+11) =
      offsetCheckpoint s (j+1) (m+1) (by omega) (by omega) := by
  let sc := {offsetCheckpoint s j m (by omega) (by omega) with
    control := {(offsetCheckpoint s j m (by omega) (by omega)).control with latch := true}}
  have hs : addressRun (offsetCheckpoint s j m (by omega) (by omega)) 2 =
      withHead sc m (by omega) .increment := by
    simp [addressRun,Function.iterate_succ_apply',addressStep,sc,offsetCheckpoint,withHead,hj,hk]
  rw [show 2*m+11=2+(2*m+6)+3 by omega,address_run_add,address_run_add,hs,address_increment _ m hm]
  simp [addressRun,Function.iterate_succ_apply',addressStep,sc,offsetCheckpoint,withHead,nextCell,hj]

private theorem offset_prefix (s : AddressState) (j m q : ℕ)
    (hj : j+q ≤ frameWidth) (hm : m+q ≤ programWidth)
    (hk : ∀ (i : ℕ) (hi : i < q), s.offset ⟨j+i,by omega⟩ = true) :
    addressRun (offsetCheckpoint s j m (by omega) (by omega)) (offsetTicks m q) =
      offsetCheckpoint s (j+q) (m+q) hj hm := by
  induction q with
  | zero => simp [offsetTicks,addressRun,offsetCheckpoint,withHead]
  | succ q ih =>
    have ht : offsetTicks m (q+1)=offsetTicks m q+(2*(m+q)+11) := by unfold offsetTicks; ring
    rw [ht,address_run_add,ih (by omega) (by omega) (by intro i hi; exact hk i (by omega))]
    simpa only [Nat.add_assoc] using offset_cycle s (j+q) (m+q) (by omega) (hk q (by omega)) (by omega)


private def addressReturned (s : AddressState) (m : ℕ) (hm : m < programWidth) : AddressState :=
  {withHead s m (by omega) .returned with
    head := {motorCheckpoint zeroAddressROM m (by omega) with probe := ⟨m,by omega⟩,pc := .read},
    control := {s.control with pc := .returned,latch := s.outer.installation.tape ⟨m,hm⟩}}

private theorem address_read (s : AddressState) (m : ℕ) (hm : m < programWidth) :
    addressRun (withHead s m (by omega) .seekAddress) (2*m+3) = addressReturned s m hm := by
  rw [address_run_add]
  rw [address_seek s m (by omega) .seekAddress (Or.inr rfl) m le_rfl]
  simp [addressRun,Function.iterate_succ_apply',addressStep,withHead,addressReturned,
    motorStep,endCell,motorCheckpoint,encodeCopy,copyCheckpoint,hm,show m ≠ programWidth by omega]

private theorem frame_base_bound : frameBase ≤ programWidth := by
  unfold frameBase programWidth
  omega

private theorem frame_address_bound (a : Fin frameKeyWidth) (i : Fin frameWidth) :
    frameBase+a.val*frameWidth+i.val < programWidth := by
  have ha := a.isLt
  have hi := i.isLt
  simp only [frameBase,frameKeyWidth,programWidth,eventWidth,frameWidth] at *
  omega

/-- Closed uniform ceiling for this subroutine's external instruction count. -/
def addressTimeBound : ℕ := 8*programWidth*programWidth+40*programWidth+8*frameKeyWidth+16

private theorem address_time_bound_aux (b c d e f a p k : ℕ)
    (hb : b ≤ p) (hc : c ≤ p) (hd : d ≤ p) (he : e ≤ p) (hf : f ≤ p) (ha : a ≤ k) :
    b*b+8*b+c*c+(2*b+9)*c+4*a+f*f+(2*d+10)*f+2*e+8 ≤
      8*p*p+40*p+8*k+16 := by
  have hbb := Nat.mul_self_le_mul_self hb
  have hcc := Nat.mul_self_le_mul_self hc
  have hff := Nat.mul_self_le_mul_self hf
  have hbc := Nat.mul_le_mul hb hc
  have hdf := Nat.mul_le_mul hd hf
  nlinarith

private theorem address_time_bound (a : Fin frameKeyWidth) (i : Fin frameWidth) :
    baseTicks 0 frameBase+1+keyTicks frameBase a.val+2+
      offsetTicks (frameBase+a.val*frameWidth) i.val+2+
      (2*(frameBase+a.val*frameWidth+i.val)+3) ≤ addressTimeBound := by
  have ha := frame_address_bound a i
  have hb := frame_base_bound
  have hk := a.isLt
  have h := address_time_bound_aux frameBase (a.val*frameWidth)
    (frameBase+a.val*frameWidth) (frameBase+a.val*frameWidth+i.val) i.val a.val
    programWidth frameKeyWidth hb (by omega) (by omega) (by omega) (by omega) (by omega)
  unfold baseTicks keyTicks offsetTicks addressTimeBound
  nlinarith [h]

theorem address_execution (s : TransferSnapshot) (a : Fin frameKeyWidth) (i : Fin frameWidth) :
    ∃ ticks, ∃ q : AddressState,
      addressRun (addressEntry s a i) ticks = q ∧ q.control.pc = .returned ∧
      q.outer = s ∧ q.head.probe.val = frameBase+a.val*frameWidth+i.val ∧
      q.control.latch = s.installation.tape ⟨frameBase+a.val*frameWidth+i.val,frame_address_bound a i⟩ ∧
      ticks ≤ addressTimeBound := by
  let e := addressEntry s a i
  let d := frameBase+a.val*frameWidth
  let m := d+i.val
  have hb := frame_base_bound
  have hbound := frame_address_bound a i
  have hd : d ≤ programWidth := by dsimp [d,m] at *; omega
  have he : baseCheckpoint e 0 0 (by omega) (by omega) = e := by
    simp [baseCheckpoint,withHead,e,addressEntry,motorEntry,motorCheckpoint,
      encodeCopy,copyEntry,copyCheckpoint]
  have hbase : addressRun e (baseTicks 0 frameBase) =
      baseCheckpoint e frameBase frameBase le_rfl hb := by
    have hp := base_prefix e 0 0 frameBase (by omega) (by omega)
    simpa only [he,Nat.zero_add] using hp
  let b := baseCheckpoint e frameBase frameBase le_rfl hb
  have hbaseEnd : addressRun b 1 = keyCheckpoint b 0 frameBase (by omega) hb := by
    simp [addressRun,Function.iterate_succ_apply',addressStep,b,baseCheckpoint,
      keyCheckpoint,withHead,endCell,e,addressEntry]
  have hkey : addressRun (keyCheckpoint b 0 frameBase (by omega) hb) (keyTicks frameBase a.val) =
      keyCheckpoint b a.val d (by have := a.isLt; omega) hd := by
    have hk : ∀ (j : ℕ) (hj : j < a.val), b.key ⟨0+j,by have := a.isLt; omega⟩ = true := by
      intro j hj
      change decide (0+j < a.val) = true
      simp [hj]
    simpa only [Nat.zero_add] using key_prefix b 0 frameBase a.val (by have := a.isLt; omega) hd hk
  let k := keyCheckpoint b a.val d (by have := a.isLt; omega) hd
  have hkeyEnd : addressRun k 2 = offsetCheckpoint k 0 d (by omega) hd := by
    have ha : a.val < frameKeyWidth := a.isLt
    simp [addressRun,Function.iterate_succ_apply',addressStep,k,keyCheckpoint,
      offsetCheckpoint,withHead,b,baseCheckpoint,e,addressEntry,ha]
  have hoff : addressRun (offsetCheckpoint k 0 d (by omega) hd) (offsetTicks d i.val) =
      offsetCheckpoint k i.val m (by have := i.isLt; omega) (by dsimp [m]; omega) := by
    have hk : ∀ (j : ℕ) (hj : j < i.val), k.offset ⟨0+j,by have := i.isLt; omega⟩ = true := by
      intro j hj
      change decide (0+j < i.val) = true
      simp [hj]
    simpa only [Nat.zero_add] using offset_prefix k 0 d i.val (by have := i.isLt; omega) (by omega) hk
  let o := offsetCheckpoint k i.val m (by have := i.isLt; omega) (by dsimp [m]; omega)
  have hoffEnd : addressRun o 2 = withHead o m (by dsimp [m]; omega) .seekAddress := by
    have hi : i.val < frameWidth := i.isLt
    simp [addressRun,Function.iterate_succ_apply',addressStep,o,offsetCheckpoint,
      withHead,k,keyCheckpoint,b,baseCheckpoint,e,addressEntry,hi]
  have hm : m < programWidth := by dsimp [m,d]; exact hbound
  let ticks := baseTicks 0 frameBase+1+keyTicks frameBase a.val+2+offsetTicks d i.val+2+(2*m+3)
  refine ⟨ticks,addressReturned o m hm,?_,?_,?_,?_,?_,?_⟩
  · have h1 : addressRun e (baseTicks 0 frameBase+1) = keyCheckpoint b 0 frameBase (by omega) hb := by
      rw [address_run_add,hbase]
      exact hbaseEnd
    have h2 : addressRun e (baseTicks 0 frameBase+1+keyTicks frameBase a.val) = k := by
      rw [address_run_add,h1]
      exact hkey
    have h3 : addressRun e (baseTicks 0 frameBase+1+keyTicks frameBase a.val+2) =
        offsetCheckpoint k 0 d (by omega) hd := by
      rw [address_run_add,h2]
      exact hkeyEnd
    have h4 : addressRun e (baseTicks 0 frameBase+1+keyTicks frameBase a.val+2+offsetTicks d i.val) = o := by
      rw [address_run_add,h3]
      exact hoff
    have h5 : addressRun e (baseTicks 0 frameBase+1+keyTicks frameBase a.val+2+offsetTicks d i.val+2) =
        withHead o m (by omega) .seekAddress := by
      rw [address_run_add,h4]
      exact hoffEnd
    change addressRun e ticks = _
    dsimp only [ticks]
    rw [address_run_add,h5,address_read]
  · rfl
  · rfl
  · rfl
  · rfl
  · exact address_time_bound a i

/-- Reachability of a returned address is an external analysis predicate. -/
def AddressReturns (s : AddressState) : Prop :=
  ∃ n, (addressRun s n).control.pc = .returned

/-- Least remaining instruction count, used only as a proof rank. It is not a
retained counter and no instruction reads it. -/
noncomputable def addressRank (s : AddressState) : ℕ := by
  classical
  exact if h : AddressReturns s then Nat.find h else 0

private theorem address_absorbing (s : AddressState)
    (hp : s.control.pc = .returned ∨ s.control.pc = .fault) (n : ℕ) : addressRun s n = s := by
  have hs : addressStep s = s := by
    rcases hp with hp | hp <;> simp [addressStep,hp]
  exact Function.iterate_fixed hs n

private theorem address_returns_after (s : AddressState) (ht : AddressReturns s) (n : ℕ) :
    AddressReturns (addressRun s n) := by
  obtain ⟨t,hp⟩ := ht
  refine ⟨t,?_⟩
  have h : addressRun (addressRun s n) t = addressRun (addressRun s t) n := by
    rw [←address_run_add,Nat.add_comm n t,address_run_add]
  rw [h,address_absorbing _ (Or.inl hp) n]
  exact hp

private theorem address_no_fault (s : AddressState) (ht : AddressReturns s) :
    s.control.pc ≠ .fault := by
  intro hf
  obtain ⟨n,hp⟩ := ht
  rw [address_absorbing s (Or.inr hf) n,hf] at hp
  cases hp

private theorem address_rank_step (s : AddressState) (ht : AddressReturns s)
    (hp : s.control.pc ≠ .returned) : addressRank (addressStep s) < addressRank s := by
  classical
  have hn : 0 < Nat.find ht := (Nat.find_pos ht).2 (by
    simpa only [addressRun,Function.iterate_zero,id_eq] using hp)
  let k := Nat.find ht - 1
  have hk : k+1 = Nat.find ht := by dsimp [k]; omega
  have hrun : addressRun (addressStep s) k = addressRun s (Nat.find ht) := by
    rw [←hk]
    exact (Function.iterate_succ_apply addressStep k s).symm
  have hc : (addressRun (addressStep s) k).control.pc = .returned := by
    rw [hrun]
    exact Nat.find_spec ht
  have hs : AddressReturns (addressStep s) := ⟨k,hc⟩
  have hm := Nat.find_min' hs hc
  simp only [addressRank,dif_pos hs,dif_pos ht]
  omega

/-- A semantic address for external endpoint comparison; addressStep never
reads this product or this Fin value. -/
def addressIndex (a : Fin frameKeyWidth) (i : Fin frameWidth) : Fin programWidth :=
  ⟨frameBase+a.val*frameWidth+i.val,frame_address_bound a i⟩

private def addressPCCodec : AddressPC ≃ Fin 17 where
  toFun
    | .baseTest => 0 | .keyRead => 1 | .keyBranch => 2 | .strideTest => 3
    | .offsetRead => 4 | .offsetBranch => 5 | .increment => 6 | .returnBase => 7
    | .returnStride => 8 | .baseMove => 9 | .keyMove => 10 | .strideMove => 11
    | .offsetMove => 12 | .seekAddress => 13 | .readProgram => 14
    | .returned => 15 | .fault => 16
  invFun i := match i.val with
    | 0 => .baseTest | 1 => .keyRead | 2 => .keyBranch | 3 => .strideTest
    | 4 => .offsetRead | 5 => .offsetBranch | 6 => .increment | 7 => .returnBase
    | 8 => .returnStride | 9 => .baseMove | 10 => .keyMove | 11 => .strideMove
    | 12 => .offsetMove | 13 => .seekAddress | 14 => .readProgram
    | 15 => .returned | _ => .fault
  left_inv p := by cases p <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[irreducible] private def addressControlCode (c : AddressControl) : List Bool :=
  bitCode c.baseProbe ++ bitCode c.keyProbe ++ bitCode c.strideProbe ++
    bitCode c.offsetProbe ++ bitCode (addressPCCodec c.pc) ++
    [c.returnBase,c.returnStride,c.latch]

def addressControlWidth : ℕ := (frameBase+1)+(frameKeyWidth+1)+2*(frameWidth+1)+17+3

private theorem address_control_length (c : AddressControl) :
    (addressControlCode c).length = addressControlWidth := by
  simp only [addressControlCode,addressControlWidth,List.length_append,bit_code_length,
    List.length_cons,List.length_nil]
  omega

private theorem address_control_encoding : Function.Injective addressControlCode := by
  intro s t h
  simp only [addressControlCode,List.append_assoc] at h
  obtain ⟨hb,h⟩ := split_block (bitCode s.baseProbe) (bitCode t.baseProbe) _ _ (frameBase+1)
    (bit_code_length _) (bit_code_length _) h
  obtain ⟨hk,h⟩ := split_block (bitCode s.keyProbe) (bitCode t.keyProbe) _ _ (frameKeyWidth+1)
    (bit_code_length _) (bit_code_length _) h
  obtain ⟨hs,h⟩ := split_block (bitCode s.strideProbe) (bitCode t.strideProbe) _ _ (frameWidth+1)
    (bit_code_length _) (bit_code_length _) h
  obtain ⟨ho,h⟩ := split_block (bitCode s.offsetProbe) (bitCode t.offsetProbe) _ _ (frameWidth+1)
    (bit_code_length _) (bit_code_length _) h
  obtain ⟨hp,h⟩ := split_block (bitCode (addressPCCodec s.pc)) (bitCode (addressPCCodec t.pc)) _ _ 17
    (bit_code_length _) (bit_code_length _) h
  have hx : s.returnBase=t.returnBase ∧ s.returnStride=t.returnStride ∧ s.latch=t.latch := by
    simpa only [List.cons.injEq,and_true] using h
  exact AddressControl.ext (bit_code_injective hb) (bit_code_injective hk)
    (bit_code_injective hs) (bit_code_injective ho)
    (addressPCCodec.injective (bit_code_injective hp)) hx.1 hx.2.1 hx.2.2

def transferWidth : ℕ := renderWidth+motorWidth programWidth+motorWidth 793800+motorWidth frameWidth

private theorem transfer_code_length (s : TransferSnapshot) : (transferCode s).length = transferWidth := by
  simp only [transferCode,transferWidth,List.length_append,render_code_length,motor_code_length]

@[irreducible] def addressCode (s : AddressState) : List Bool :=
  transferCode s.outer ++ addressControlCode s.control ++ List.ofFn s.key ++
    List.ofFn s.offset ++ motorCode s.head

def addressWidth : ℕ := transferWidth+addressControlWidth+frameKeyWidth+frameWidth+motorWidth programWidth

theorem address_code_length (s : AddressState) : (addressCode s).length = addressWidth := by
  simp only [addressCode,addressWidth,List.length_append,transfer_code_length,
    address_control_length,List.length_ofFn,motor_code_length]

theorem address_encoding : Function.Injective addressCode := by
  intro s t h
  simp only [addressCode,List.append_assoc] at h
  obtain ⟨ho,h⟩ := split_block (transferCode s.outer) (transferCode t.outer) _ _ transferWidth
    (transfer_code_length _) (transfer_code_length _) h
  obtain ⟨hc,h⟩ := split_block (addressControlCode s.control) (addressControlCode t.control) _ _ addressControlWidth
    (address_control_length _) (address_control_length _) h
  obtain ⟨hk,h⟩ := split_block (List.ofFn s.key) (List.ofFn t.key) _ _ frameKeyWidth
    List.length_ofFn List.length_ofFn h
  obtain ⟨hi,hh⟩ := split_block (List.ofFn s.offset) (List.ofFn t.offset) _ _ frameWidth
    List.length_ofFn List.length_ofFn h
  exact AddressState.ext (transfer_encoding ho) (address_control_encoding hc)
    (List.ofFn_injective hk) (List.ofFn_injective hi) (motor_encoding hh)

/-- All immutable rails, opcode records and zero scratch ROM are included. -/
@[irreducible] def addressStaticImage : List Bool := motorStaticImage ++
  endMask frameBase ++ endMask frameKeyWidth ++
  (List.ofFn (fun i : Fin 17 => bitCode i)).flatten ++ List.ofFn zeroAddressROM

@[irreducible] def addressStaticWidth : ℕ := motorStaticWidth+(frameBase+1)+(frameKeyWidth+1)+289+programWidth

private theorem address_static_length_aux (b k : ℕ) :
    (motorStaticImage ++ endMask b ++ endMask k ++
      (List.ofFn (fun i : Fin 17 => bitCode i)).flatten ++ List.ofFn zeroAddressROM).length =
    motorStaticWidth+(b+1)+(k+1)+289+programWidth := by
  have hop : ((List.ofFn (fun i : Fin 17 => bitCode i)).flatten).length = 289 := by
    simp [List.length_flatten,List.map_map,bit_code_length]
  simp only [List.length_append,motor_static_length,end_mask_length,hop,List.length_ofFn,
    Nat.add_assoc]

theorem address_static_length : addressStaticImage.length = addressStaticWidth := by
  unfold addressStaticImage addressStaticWidth
  exact address_static_length_aux frameBase frameKeyWidth

def literalAddressBound : ℕ := programWidth+addressStaticWidth+addressWidth+1

private theorem address_charge (s : AddressState) :
    programImage.length+addressStaticImage.length+(addressCode s).length < literalAddressBound := by
  simp only [programImage,List.length_ofFn,address_static_length,address_code_length,literalAddressBound]
  omega

theorem address_context_step (s : AddressState) :
    (addressStep s).outer = s.outer ∧ (addressStep s).key = s.key ∧ (addressStep s).offset = s.offset := by
  cases hp : s.control.pc <;> simp [addressStep,hp] <;> split <;> simp_all

private theorem address_context (s : AddressState) (n : ℕ) :
    (addressRun s n).outer = s.outer ∧ (addressRun s n).key = s.key ∧ (addressRun s n).offset = s.offset := by
  induction n with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
    have hs := address_context_step (addressRun s n)
    have h := And.intro (hs.1.trans ih.1) (And.intro (hs.2.1.trans ih.2.1) (hs.2.2.trans ih.2.2))
    simpa only [addressRun,Function.iterate_succ_apply'] using h

/-- External row selection for the subroutine input relation. -/
def frameKey (s : TransferSnapshot) (slot : Fin 6) : Fin frameKeyWidth :=
  Fin.cast (by unfold frameKeyWidth; rfl)
    (eventKeyCodec (s.base.retained.pre.fields,s.base.retained.operation,slot))

set_option maxHeartbeats 2000000 in
-- The finite cast compares two fixed image layouts.
theorem address_frame_index (s : TransferSnapshot) (slot : Fin 6) (i : Fin frameWidth) :
    addressIndex (frameKey s slot) i = frameAddress s.base slot i := by
  apply Fin.ext
  change frameBase+(frameKey s slot).val*frameWidth+i.val =
    B0+(headerWidth+(i.val+frameWidth*
      (eventKeyCodec (s.base.retained.pre.fields,s.base.retained.operation,slot)).val))
  simp only [frameBase,frameKey,Fin.val_cast]
  rw [Nat.mul_comm]
  omega

private theorem address_program_frame (s installed : TransferSnapshot)
    (ht : installed.installation.tape = programTape) (slot : Fin 6) (i : Fin frameWidth) :
    ∃ ticks, ∃ q : AddressState,
      addressRun (addressEntry installed (frameKey s slot) i) ticks = q ∧
      q.control.pc = .returned ∧
      q.control.latch = frameTape
        (eventROM s.base.retained.pre.fields s.base.retained.operation slot) i := by
  obtain ⟨ticks, q, hq, hp, _, _, hl, _⟩ := address_execution installed (frameKey s slot) i
  refine ⟨ticks, q, hq, hp, ?_⟩
  change q.control.latch = installed.installation.tape (addressIndex (frameKey s slot) i) at hl
  rw [ht, address_frame_index] at hl
  exact hl.trans (congrFun (program_frame s.base slot) i)

/-- A charged address subroutine, with explicit raw key/offset inputs. Its
instructions perform rail tests, single-bit reads, unary carries and return
branches before reading the installed bit. The endpoint multiplication occurs
only in the theorem, not in the instruction transition. Paid preparation of
those raw inputs and the unified adaptive dispatcher are separate obligations. -/
theorem charged_address_execution (s : TransferSnapshot) :
    Function.Injective addressCode ∧
    (∀ q : AddressState, programImage.length+addressStaticImage.length+(addressCode q).length < literalAddressBound) ∧
    (∀ (a : Fin frameKeyWidth) (i : Fin frameWidth) (n : ℕ),
      let q := addressRun (addressEntry s a i) n
      q.outer = s ∧ q.key = (addressEntry s a i).key ∧ q.offset = (addressEntry s a i).offset ∧
      q.control.pc ≠ .fault ∧ (q.control.pc ≠ .returned → addressRank (addressStep q) < addressRank q)) ∧
    (∀ (a : Fin frameKeyWidth) (i : Fin frameWidth), ∃ ticks, ∃ q : AddressState,
      addressRun (addressEntry s a i) ticks = q ∧ q.control.pc = .returned ∧
      q.outer = s ∧ q.head.probe.val = (addressIndex a i).val ∧
      q.control.latch = s.installation.tape (addressIndex a i) ∧ ticks ≤ addressTimeBound) ∧
    (∀ (slot : Fin 6) (i : Fin frameWidth),
      let installed := literalInstallStep^[motorTime programWidth] (literalInstallStart s)
      let a := frameKey s slot
      ∃ ticks, ∃ q : AddressState,
        addressRun (addressEntry installed a i) ticks = q ∧ q.control.pc = .returned ∧
        q.control.latch = frameTape (eventROM s.base.retained.pre.fields s.base.retained.operation slot) i) := by
  refine ⟨address_encoding,address_charge,?_,?_,?_⟩
  · intro a i n
    have hc := address_context (addressEntry s a i) n
    obtain ⟨t,z,hz,hp,_,_,_,_⟩ := address_execution s a i
    have ht : AddressReturns (addressEntry s a i) := ⟨t,by rw [hz]; exact hp⟩
    have hq := address_returns_after (addressEntry s a i) ht n
    exact ⟨hc.1,hc.2.1,hc.2.2,address_no_fault _ hq,address_rank_step _ hq⟩
  · intro a i
    exact address_execution s a i
  · intro slot i
    exact address_program_frame s _ ((charged_literal_transfers s).2.2.2.2.1) slot i



namespace LiveProducer
open RarePriorFairBitService

/-- Raw unary words are machine data; their Runtime/Service interpretation is external. -/
def word {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i.val < v.val)

/-- The two concrete strides used by this producer are four for native operations
and two for service bits. The stride and tail loops perform adjacent rail moves. -/
@[ext] structure Key (k m : ℕ) where
  tape : Fin k → Bool
  tail : Fin m
  probe : Fin (k+1)
  carry : Fin (m+1)
  query : Fin (k*m+1)
  pc : Fin 6
  deriving DecidableEq

def keyEntry {k m : ℕ} (tape : Fin k → Bool) (tail : Fin m) : Key k m :=
  ⟨tape,tail,0,0,0,0⟩

/-- Tags 0/1/2/3/4/5 are test, carry, move, tail, returned and fault.
Only a unary input-bit test, an adjacent rail move or a fixed reset occurs here. -/
def keyStep {k m : ℕ} (s : Key k m) : Key k m :=
  if s.pc = 0 then
    if h : s.probe.val < k then
      if s.tape ⟨s.probe.val,h⟩ then {s with pc := 1,carry := 0}
      else {s with pc := 3,carry := 0}
    else {s with pc := 5}
  else if s.pc = 1 then
    if hc : s.carry.val < m then
      if h : s.query.val < k*m then
        {s with query := ⟨s.query.val+1,by omega⟩, carry := ⟨s.carry.val+1,by omega⟩}
      else {s with pc := 5}
    else {s with pc := 2}
  else if s.pc = 2 then
    if h : s.probe.val < k then
      {s with probe := ⟨s.probe.val+1,by omega⟩,carry := 0,pc := 0}
    else {s with pc := 5}
  else if s.pc = 3 then
    if hc : s.carry.val < s.tail.val then
      if h : s.query.val < k*m then
        {s with query := ⟨s.query.val+1,by omega⟩, carry := ⟨s.carry.val+1,by have := s.tail.isLt; omega⟩}
      else {s with pc := 5}
    else {s with pc := 4}
  else s

def keyRun {k m : ℕ} (s : Key k m) (t : ℕ) : Key k m := keyStep^[t] s

private def keyCheckpoint {k m : ℕ} (a : Fin k) (b : Fin m) (j : ℕ) (hj : j ≤ a.val) : Key k m :=
  ⟨word a,b,⟨j,by have := a.isLt; omega⟩,0,
    ⟨j*m,by have := a.isLt; nlinarith⟩,0⟩

private def keyCarry {k m : ℕ} (a : Fin k) (b : Fin m) (j r : ℕ)
    (hj : j < a.val) (hr : r ≤ m) : Key k m :=
  ⟨word a,b,⟨j,by have := a.isLt; omega⟩,⟨r,by omega⟩,
    ⟨j*m+r,by have := a.isLt; nlinarith⟩,1⟩

private theorem key_carry_run {k m : ℕ} (a : Fin k) (b : Fin m) (j : ℕ)
    (hj : j < a.val) (r : ℕ) (hr : r ≤ m) :
    keyRun (keyCarry a b j 0 hj (Nat.zero_le _)) r = keyCarry a b j r hj hr := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hm : r < m := by omega
    have hq : j*m+r < k*m := by have := a.isLt; nlinarith
    rw [keyRun,Function.iterate_succ_apply']
    change keyStep (keyRun (keyCarry a b j 0 hj (Nat.zero_le _)) r) = _
    rw [ih (by omega)]
    simp [keyStep,keyCarry,hm,hq,Nat.add_assoc]

private theorem key_cycle {k m : ℕ} (a : Fin k) (b : Fin m) (j : ℕ)
    (hj : j < a.val) :
    keyRun (keyCheckpoint a b j (by omega)) (m+3) =
      keyCheckpoint a b (j+1) (by omega) := by
  have hk : j < k := by have := a.isLt; omega
  have hs : keyStep (keyCheckpoint a b j (by omega)) =
      keyCarry a b j 0 hj (Nat.zero_le _) := by
    simp [keyStep,keyCheckpoint,word,hk,hj,keyCarry]
  rw [show m+3 = (m+2)+1 by omega,keyRun,Function.iterate_add_apply]
  change keyRun (keyStep (keyCheckpoint a b j (by omega))) (m+2) = _
  rw [hs,keyRun,show m+2 = 2+m by omega,Function.iterate_add_apply]
  change keyRun (keyRun (keyCarry a b j 0 hj (Nat.zero_le _)) m) 2 = _
  rw [key_carry_run a b j hj m le_rfl]
  simp [keyRun,Function.iterate_succ_apply',keyStep,keyCarry,keyCheckpoint,hk,Nat.add_mul]

private theorem key_prefix {k m : ℕ} (a : Fin k) (b : Fin m) (j : ℕ)
    (hj : j ≤ a.val) :
    keyRun (keyEntry (word a) b) ((m+3)*j) = keyCheckpoint a b j hj := by
  induction j with
  | zero => simp [keyRun,keyEntry,keyCheckpoint]
  | succ j ih =>
    rw [Nat.mul_succ,Nat.add_comm,keyRun,Function.iterate_add_apply]
    change keyRun (keyRun (keyEntry (word a) b) ((m+3)*j)) (m+3) = _
    rw [ih (by omega)]
    exact key_cycle a b j (by omega)

private def keyTail {k m : ℕ} (a : Fin k) (b : Fin m) (r : ℕ) (hr : r ≤ b.val) : Key k m :=
  ⟨word a,b,⟨a.val,by have := a.isLt; omega⟩,⟨r,by have := b.isLt; omega⟩,
    ⟨a.val*m+r,by have := a.isLt; have := b.isLt; nlinarith⟩,3⟩

private theorem key_tail_run {k m : ℕ} (a : Fin k) (b : Fin m) (r : ℕ)
    (hr : r ≤ b.val) :
    keyRun (keyTail a b 0 (Nat.zero_le _)) r = keyTail a b r hr := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hb : r < b.val := by omega
    have hq : a.val*m+r < k*m := by have := a.isLt; have := b.isLt; nlinarith
    rw [keyRun,Function.iterate_succ_apply']
    change keyStep (keyRun (keyTail a b 0 (Nat.zero_le _)) r) = _
    rw [ih (by omega)]
    simp [keyStep,keyTail,hb,hq,Nat.add_assoc]

/-- This is a theorem clock, not a retained counter. -/
def keyTime {k m : ℕ} (a : Fin k) (b : Fin m) : ℕ := (m+3)*a.val+b.val+2

private theorem key_add {k m : ℕ} (s : Key k m) (a b : ℕ) :
    keyRun s (a+b) = keyRun (keyRun s a) b := by
  simp only [keyRun,Nat.add_comm a b,Function.iterate_add_apply]

theorem key_execution {k m : ℕ} (a : Fin k) (b : Fin m) :
    (keyRun (keyEntry (word a) b) (keyTime a b)).pc = 4 ∧
    (keyRun (keyEntry (word a) b) (keyTime a b)).query.val = a.val*m+b.val := by
  have hs : keyStep (keyCheckpoint a b a.val le_rfl) = keyTail a b 0 (Nat.zero_le _) := by
    simp [keyStep,keyCheckpoint,word,a.isLt,keyTail]
  have he : keyRun (keyEntry (word a) b) (keyTime a b) =
      {keyTail a b b.val le_rfl with pc := 4} := by
    rw [show keyTime a b = ((m+3)*a.val+1)+b.val+1 by unfold keyTime; omega, key_add,key_add,key_add,key_prefix a b a.val le_rfl]
    change keyStep (keyRun (keyStep (keyCheckpoint a b a.val le_rfl)) b.val) = _
    rw [hs,key_tail_run a b b.val le_rfl]
    simp [keyStep,keyTail]
  rw [he]
  exact ⟨rfl,rfl⟩



end LiveProducer
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
