/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerSetup
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerSetup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Resident producer codecs and finite controls encode current-bank native transactions. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.TransfersAddress

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option Elab.async false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
namespace LiveProducer
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder NativeFullResidual
open RarePriorFiniteMonitor RarePriorResidentCode RarePriorSerialExecution
open RarePriorFairBitService
namespace CurrentBank

abbrev RuntimeWidth := runtimeSize
abbrev NativeKeyWidth := runtimeSize*4
abbrev NativeResultWidth := runtimeSize+1
abbrev FieldsWidth := 793800
abbrev RuntimeStride := 6023*4

/-- All banks are raw tapes. The role selects the sole mutable destination. -/
@[ext] structure State where
  addressed : AddressState
  actual : Fin runtimeSize → Bool
  synthetic : Fin runtimeSize → Bool
  role : Bool
  operation : Fin 4
  pre : Motor runtimeSize
  key : Key runtimeSize 4
  query : Fin (runtimeSize*4) → Bool
  native : Scanner (runtimeSize*4) (runtimeSize+1)
  payload : Fin (runtimeSize+1) → Bool
  result : Motor (runtimeSize+1)
  fields : Motor 793800
  row : Key 793800 24
  slot : Fin 6
  offset : Fin frameWidth
  bankProbe : Fin (runtimeSize+1)
  bankLatch : Bool
  phase : Fin 14
  opcodes : Motor 12
  deriving DecidableEq

def bank (s : State) : Fin runtimeSize → Bool := if s.role then s.synthetic else s.actual

/-- This fixed tap layout is a macro address map. Each tapped bit is copied by
Motor; no typed Runtime value is read by the transition. -/
def fieldROM (s : State) (i : Fin 793800) : Bool :=
  s.pre.tape ⟨(i.val+1)*(6023*4)-1,by
    have hi := i.isLt
    unfold runtimeSize
    omega⟩

/-- This is the physical native-row address map, still a macro address map. -/
def nativeBit (s : State) (row : Fin (runtimeSize*4))
    (i : Fin (runtimeSize*5+1)) : Bool :=
  s.addressed.outer.installation.tape ⟨864+row.val*(runtimeSize*5+1)+i.val,by
    have hr := row.isLt
    have hi := i.isLt
    unfold programWidth B0 snapshotWidth residentWidth
    nlinarith⟩

/-- The three four-bit words in one resident instruction record are fetched
through the installed tape before the native scanner takes its next step. -/
def opcodeROM (s : State) (i : Fin 12) : Bool :=
  s.addressed.outer.installation.tape ⟨s.native.pc.val*12+i.val,by
    have := s.native.pc.isLt
    have := i.isLt
    unfold programWidth B0 snapshotWidth residentWidth runtimeSize
    omega⟩

def decodeOpcode (tape : Fin 12 → Bool) (part : Fin 3) : Fin 4 :=
  if tape ⟨part.val*4,by have := part.isLt; omega⟩ = false then 0
  else if tape ⟨part.val*4+1,by have := part.isLt; omega⟩ = false then 1
  else if tape ⟨part.val*4+2,by have := part.isLt; omega⟩ = false then 2
  else 3

/-- Key and payload reads consult the installed tape. They never evaluate the
native table. The query is the raw tape written by the carry instructions. -/
def scanStep (s : State) : State :=
  if hr : s.native.row.val < runtimeSize*4 then
    let r : Fin (runtimeSize*4) := ⟨s.native.row.val,hr⟩
    if decodeOpcode s.opcodes.tape 0 = 0 then
      if hi : s.native.cursor.val < runtimeSize*4 then
        {s with native := {s.native with
          cursor := ⟨s.native.cursor.val+1,by omega⟩,
          equalFlag := s.native.equalFlag &&
            (s.query ⟨s.native.cursor.val,hi⟩ ==
             nativeBit s r ⟨s.native.cursor.val,by unfold runtimeSize at *; omega⟩)}}
      else if s.native.equalFlag then
        {s with native := {s.native with pc := decodeOpcode s.opcodes.tape 1,cursor := 0,accumulator := 0}}
      else {s with native := {s.native with
        row := ⟨s.native.row.val+1,by omega⟩,pc := decodeOpcode s.opcodes.tape 2,cursor := 0,equalFlag := true}}
    else if decodeOpcode s.opcodes.tape 0 = 1 then
      if hi : s.native.cursor.val < runtimeSize+1 then
        let bit := nativeBit s r ⟨runtimeSize*4+s.native.cursor.val,by
          unfold runtimeSize at *; omega⟩
        {s with payload := Function.update s.payload ⟨s.native.cursor.val,hi⟩ bit,native := {s.native with cursor := ⟨s.native.cursor.val+1,by omega⟩,accumulator := ⟨min (runtimeSize+1) (s.native.accumulator.val+if bit then 1 else 0),
              Nat.lt_succ_of_le (min_le_left _ _)⟩}}
      else {s with native := {s.native with pc := if s.native.accumulator.val < runtimeSize+1 then decodeOpcode s.opcodes.tape 1 else decodeOpcode s.opcodes.tape 2}}
    else s
  else {s with native := {s.native with pc := 3}}

/-- The native carry writes the corresponding raw query bit. The numerical
query rail is retained alongside the actual tape and charged separately. -/
def buildKey (s : State) : State :=
  let k := keyStep s.key
  if h : s.key.query.val < runtimeSize*4 then
    if k.query.val = s.key.query.val+1 then
      {s with key := k,query := Function.update s.query ⟨s.key.query.val,h⟩ true}
    else {s with key := k}
  else {s with key := k}

/-- Finite stages: bank copy, key, native scan, result copy, fields copy,
row key, installed address, output, advance, bank read, bank write, retired,
fault and reserved reset. Address arithmetic and register resets remain rail
primitives; the raw native and output dataflow uses actual tapes. -/
def step (s : State) : State :=
  match s.phase.val with
  | 0 => if s.pre.pc = .halt then
      {s with phase := 1,key := keyEntry s.pre.tape s.operation}
    else {s with pre := motorStep (bank s) s.pre}
  | 1 => if s.key.pc = 4 then
      if h : s.key.query.val < runtimeSize*4 then
        {s with phase := 13,native := scannerEntry ⟨s.key.query.val,h⟩}
      else {s with phase := 12}
    else if s.key.pc = 5 then {s with phase := 12}
    else buildKey s
  | 2 => if s.native.pc = 2 then {s with phase := 3}
    else if s.native.pc = 3 then {s with phase := 12}
    else {(scanStep s) with phase := 13,opcodes := motorEntry 12}
  | 3 => if s.payload ⟨0,by omega⟩ = false then {s with phase := 12}
    else if s.result.pc = .halt then {s with phase := 4}
    else {s with result := motorStep s.payload s.result}
  | 4 => if s.fields.pc = .halt then
      {s with phase := 5,row := keyEntry s.fields.tape ⟨s.operation.val*6+s.slot.val,by have := s.operation.isLt; have := s.slot.isLt; omega⟩}
    else {s with fields := motorStep (fieldROM s) s.fields}
  | 5 => if s.row.pc = 4 then
      if h : s.row.query.val < frameKeyWidth then
        {s with phase := 6,addressed := addressEntry s.addressed.outer ⟨s.row.query.val,h⟩ s.offset}
      else {s with phase := 12}
    else if s.row.pc = 5 then {s with phase := 12}
    else {s with row := keyStep s.row}
  | 6 => if s.addressed.control.pc = .returned then {s with phase := 7}
    else if s.addressed.control.pc = .fault then {s with phase := 12}
    else {s with addressed := addressStep s.addressed}
  | 7 => {s with phase := 8}
  | 8 => if hq : s.row.query.val < frameKeyWidth then
      if h : s.offset.val+1 < frameWidth then
        {s with phase := 6,offset := ⟨s.offset.val+1,h⟩,addressed := addressEntry s.addressed.outer ⟨s.row.query.val,hq⟩ ⟨s.offset.val+1,h⟩}
      else if h : s.slot.val+1 < 6 then
        {s with phase := 5,slot := ⟨s.slot.val+1,h⟩,offset := ⟨0,by unfold frameWidth; omega⟩,row := keyEntry s.fields.tape ⟨s.operation.val*6+(s.slot.val+1),by have := s.operation.isLt; omega⟩}
      else {s with phase := 9,bankProbe := 0}
    else {s with phase := 12}
  | 9 => if h : s.bankProbe.val < runtimeSize then
      {s with phase := 10,bankLatch := s.result.tape ⟨s.bankProbe.val+1,by omega⟩}
    else {s with phase := 11}
  | 10 => if h : s.bankProbe.val < runtimeSize then
      let i : Fin runtimeSize := ⟨s.bankProbe.val,h⟩
      if s.role then
        {s with phase := 9,synthetic := Function.update s.synthetic i s.bankLatch,bankProbe := ⟨s.bankProbe.val+1,by omega⟩}
      else {s with phase := 9,actual := Function.update s.actual i s.bankLatch,bankProbe := ⟨s.bankProbe.val+1,by omega⟩}
    else {s with phase := 12}
  | 13 => if s.opcodes.pc = .halt then {s with phase := 2}
    else {s with opcodes := motorStep (opcodeROM s) s.opcodes}
  | _ => s

def run (s : State) (ticks : ℕ) : State := step^[ticks] s

def output (s : State) : Option Bool := if s.phase = 7 then some s.addressed.control.latch else none

def trace (s : State) : ℕ → List Bool
  | 0 => []
  | n+1 => (output s).toList ++ trace (step s) n

/-- Entry supplies only installed physical image, current banks and captured
raw Operation. Query, result and current-event tapes are unprepared. -/
def entry (image : TransferSnapshot) (actual synthetic : Fin runtimeSize → Bool)
    (role : Bool) (operation : Fin 4) : State where
  addressed := addressEntry image ⟨0,by unfold frameKeyWidth; omega⟩ ⟨0,by unfold frameWidth; omega⟩
  actual := actual
  synthetic := synthetic
  role := role
  operation := operation
  pre := motorEntry runtimeSize
  key := keyEntry (fun _ => false) 0
  query := fun _ => false
  native := scannerEntry ⟨0,by unfold runtimeSize; omega⟩
  payload := fun _ => false
  result := motorEntry (runtimeSize+1)
  fields := motorEntry 793800
  row := keyEntry (fun _ => false) 0
  slot := 0
  offset := ⟨0,by unfold frameWidth; omega⟩
  bankProbe := 0
  bankLatch := false
  phase := 0
  opcodes := motorEntry 12


end CurrentBank



inductive Stage where
  | boot | install | ready | acquire | pendingZero | pendingOne | initializing
  | serviceInput | serviceKey | serviceScan | serviceCopy | serviceMenu | serviceReset
  | nativeKey | nativeScan | runtimeCopy | render | emit | commit | returned | terminal | fault | retry
  deriving DecidableEq

instance : Fintype Stage := ⟨{.boot,.install,.ready,.acquire,.pendingZero,.pendingOne,.initializing,
  .serviceInput,.serviceKey,.serviceScan,.serviceCopy,.serviceMenu,.serviceReset,.nativeKey,
  .nativeScan,.runtimeCopy,.render,.emit,.commit,.returned,.terminal,.fault,.retry},by
  intro p; cases p <;> simp⟩

/-- This menu is fixed producer code. Its semantics is not evaluated by step. -/
def serviceMenuTable (a : Fin 21504) : Fin 8 :=
  finProdFinEquiv (RarePriorResidentCode.pcCodec (serviceCodec.symm a).pc,
    (serviceCodec.symm a).output)

/-- The resident query, service and native scanners, both copied raw return
words and the address motor coexist with the entire inherited snapshot. -/
@[ext] structure State where
  addressed : AddressState
  nativeKey : Key runtimeSize 4
  serviceKey : Key 21504 2
  initialization : Scanner runtimeSize 21504
  sampler : Scanner 43008 21504
  native : Scanner (runtimeSize*4) (runtimeSize+1)
  menu : Scanner 21504 8
  runtime : Motor (runtimeSize+1)
  service : Motor 21504
  stage : Stage
  operation : Fin 4
  readyRole : Fin 5
  rawService : Fin 21505
  resetProbe : Fin 21505
  freshRequested : Bool
  committed : Bool
  sourceLatch : Letter
  freshLatch : Letter
  deriving DecidableEq

def actualRequest (s : State) : Bool := decide (s.stage = .acquire)
def freshRequest (s : State) : Bool := decide (s.stage = .serviceInput) && s.freshRequested

/-- Each return word is read one bit at a time. Runtime and Service codecs are
absent from the instruction transition; they occur only in the refinement. -/
def runtimeROM (s : State) : Fin (runtimeSize+1) → Bool :=
  fun i => decide (i.val < s.native.accumulator.val)
def serviceROM (s : State) : Fin 21504 → Bool :=
  fun i => decide (i.val < s.rawService.val)

/-- The source and fresh-bit ports are different arguments. No deterministic
branch reads either port. Installed graph instructions and rail control resets
remain the supplier's atomic primitives in this concrete composition. -/
def step (s : State) (source fresh : Letter) : State :=
  match s.stage with
  | .boot => {s with stage := .install}
  | .install => if s.addressed.outer.installation.pc = .halt then {s with stage := .ready}
      else {s with addressed := {s.addressed with outer := literalInstallStep s.addressed.outer}}
  | .ready => match s.readyRole.val with
      | 0 => {s with stage := .acquire}
      | 1 => {s with stage := .pendingZero}
      | 2 => {s with stage := .pendingOne}
      | 3 => {s with stage := .terminal}
      | _ => {s with stage := .initializing}
  | .acquire =>
      let op : Fin 4 := Fin.castAdd 2 source
      {s with stage := .nativeKey,operation := op,sourceLatch := source,   nativeKey := {s.nativeKey with tail := op,probe := 0,carry := 0,query := 0,pc := 0}}
  | .pendingZero => {s with stage := .nativeKey,operation := 2, nativeKey := {s.nativeKey with tail := 2,probe := 0,carry := 0,query := 0,pc := 0}}
  | .pendingOne => {s with stage := .nativeKey,operation := 3, nativeKey := {s.nativeKey with tail := 3,probe := 0,carry := 0,query := 0,pc := 0}}
  | .initializing => if s.initialization.pc = 2 then
      {s with stage := .serviceCopy,rawService := s.initialization.accumulator}
    else if s.initialization.pc = 3 then {s with stage := .fault}
    else {s with initialization := installedGraphStep initializationTable s.initialization}
  | .serviceInput =>
      let b := if s.freshRequested then fresh else 0
      {s with stage := .serviceKey,freshLatch := b,   serviceKey := ⟨s.service.tape,b,0,0,0,0⟩}
  | .serviceKey => if s.serviceKey.pc = 4 then
      if h : s.serviceKey.query.val < 43008 then
        {s with stage := .serviceReset,resetProbe := 0,     sampler := scannerEntry ⟨s.serviceKey.query.val,h⟩}
      else {s with stage := .fault}
    else if s.serviceKey.pc = 5 then {s with stage := .fault}
    else {s with serviceKey := keyStep s.serviceKey}
  | .serviceReset => if h : s.resetProbe.val < 21504 then
      {s with resetProbe := ⟨s.resetProbe.val+1,by omega⟩,   service := {s.service with headBits := Function.update s.service.headBits s.resetProbe false}}
    else {s with stage := .serviceScan, service := {s.service with headBits := Function.update s.service.headBits s.resetProbe false,   probe := 0,pc := .seek,latch := false}}
  | .serviceScan => if s.sampler.pc = 2 then
      {s with stage := .serviceCopy,rawService := s.sampler.accumulator}
    else if s.sampler.pc = 3 then {s with stage := .fault}
    else {s with sampler := installedGraphStep serviceTable s.sampler}
  | .serviceCopy => if s.service.pc = .halt then
      if h : s.rawService.val < 21504 then
        {s with stage := .serviceMenu,menu := scannerEntry ⟨s.rawService.val,h⟩}
      else {s with stage := .fault}
    else {s with service := motorStep (serviceROM s) s.service}
  | .serviceMenu => if s.menu.pc = 2 then
      if s.menu.accumulator.val = 6 then
        {s with stage := .nativeKey,operation := 0,     nativeKey := {s.nativeKey with tail := 0,probe := 0,carry := 0,query := 0,pc := 0}}
      else if s.menu.accumulator.val = 7 then
        {s with stage := .nativeKey,operation := 1,     nativeKey := {s.nativeKey with tail := 1,probe := 0,carry := 0,query := 0,pc := 0}}
      else {s with stage := .serviceInput,   freshRequested := decide (s.menu.accumulator.val = 2 ∨ s.menu.accumulator.val = 3)}
    else if s.menu.pc = 3 then {s with stage := .fault}
    else {s with menu := installedGraphStep serviceMenuTable s.menu}
  | .nativeKey => if s.nativeKey.pc = 4 then
      if h : s.nativeKey.query.val < runtimeSize*4 then
        {s with stage := .nativeScan,native := scannerEntry ⟨s.nativeKey.query.val,h⟩}
      else {s with stage := .fault}
    else if s.nativeKey.pc = 5 then {s with stage := .fault}
    else {s with nativeKey := keyStep s.nativeKey}
  | .nativeScan => if s.native.pc = 2 then {s with stage := .runtimeCopy}
    else if s.native.pc = 3 then {s with stage := .fault}
    else {s with native := installedGraphStep nativeTable s.native}
  | .runtimeCopy => if s.runtime.pc = .halt then {s with stage := .render}
    else {s with runtime := motorStep (runtimeROM s) s.runtime}
  | .render => if s.addressed.control.pc = .returned then {s with stage := .emit}
    else if s.addressed.control.pc = .fault then {s with stage := .fault}
    else {s with addressed := addressStep s.addressed}
  | .emit => {s with stage := .commit}
  | .commit => {s with stage := .returned,committed := true}
  | .returned | .terminal | .fault => s
  | .retry => {s with stage := .boot,committed := false}

def run (s : State) (source fresh : Letter) (t : ℕ) : State :=
  (fun q => step q source fresh)^[t] s

def emitted (s : State) : Option Bool :=
  if s.stage = .emit then some s.addressed.control.latch else none

/-- Decoding and canonical source selection are observations of the physical
word. Neither this function nor its choice is an instruction input. -/
noncomputable def returnedRuntime (s : State) : Option Runtime :=
  if s.committed then
    if h : ∃ v : Fin (runtimeSize+1), s.runtime.tape = word v then
      optionalRuntimeCodec.symm (Classical.choose h) else none
  else some s.addressed.outer.base.retained.actual

noncomputable def returnedOperation (s : State) : Option Operation :=
  if s.stage = .returned then some (operationCodec.symm s.operation) else none


private def stageCodec : Stage ≃ Fin 23 where
  toFun
    | .boot => 0 | .install => 1 | .ready => 2 | .acquire => 3
    | .pendingZero => 4 | .pendingOne => 5 | .initializing => 6
    | .serviceInput => 7 | .serviceKey => 8 | .serviceScan => 9
    | .serviceCopy => 10 | .serviceMenu => 11 | .serviceReset => 12
    | .nativeKey => 13 | .nativeScan => 14 | .runtimeCopy => 15
    | .render => 16 | .emit => 17 | .commit => 18 | .returned => 19
    | .terminal => 20 | .fault => 21 | .retry => 22
  invFun i := match i.val with
    | 0 => .boot | 1 => .install | 2 => .ready | 3 => .acquire
    | 4 => .pendingZero | 5 => .pendingOne | 6 => .initializing
    | 7 => .serviceInput | 8 => .serviceKey | 9 => .serviceScan
    | 10 => .serviceCopy | 11 => .serviceMenu | 12 => .serviceReset
    | 13 => .nativeKey | 14 => .nativeScan | 15 => .runtimeCopy
    | 16 => .render | 17 => .emit | 18 => .commit | 19 => .returned
    | 20 => .terminal | 21 => .fault | _ => .retry
  left_inv s := by cases s <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def keyWidth (k m : ℕ) : ℕ := m+(k+1)+(m+1)+(k*m+1)+6+k

@[irreducible] private def keyCode {k m : ℕ} (s : Key k m) : List Bool :=
  bitCode s.tail ++ bitCode s.probe ++ bitCode s.carry ++ bitCode s.query ++
    bitCode s.pc ++ List.ofFn s.tape

private theorem key_length {k m : ℕ} (s : Key k m) : (keyCode s).length = keyWidth k m := by
  simp only [keyCode,keyWidth,List.length_append,bit_code_length,List.length_ofFn]

private theorem key_encoding {k m : ℕ} : Function.Injective (@keyCode k m) := by
  intro s t h
  simp only [keyCode,List.append_assoc] at h
  obtain ⟨ht,h⟩ := split_block (bitCode s.tail) (bitCode t.tail) _ _ m (bit_code_length _) (bit_code_length _) h
  obtain ⟨hp,h⟩ := split_block (bitCode s.probe) (bitCode t.probe) _ _ (k+1) (bit_code_length _) (bit_code_length _) h
  obtain ⟨hc,h⟩ := split_block (bitCode s.carry) (bitCode t.carry) _ _ (m+1) (bit_code_length _) (bit_code_length _) h
  obtain ⟨hq,h⟩ := split_block (bitCode s.query) (bitCode t.query) _ _ (k*m+1) (bit_code_length _) (bit_code_length _) h
  obtain ⟨hi,hb⟩ := split_block (bitCode s.pc) (bitCode t.pc) _ _ 6 (bit_code_length _) (bit_code_length _) h
  exact Key.ext (List.ofFn_injective hb) (bit_code_injective ht) (bit_code_injective hp)
    (bit_code_injective hc) (bit_code_injective hq) (bit_code_injective hi)

private def controlSize : ℕ := 23*(4*(5*(21505*(21505*(2*(2*(2*2)))))))
private def controlCodec :
    (Stage × Fin 4 × Fin 5 × Fin 21505 × Fin 21505 × Bool × Bool × Letter × Letter) ≃ Fin controlSize :=
  pairFin stageCodec (pairFin (Equiv.refl _) (pairFin (Equiv.refl _) (pairFin (Equiv.refl _)
    (pairFin (Equiv.refl _) (pairFin finTwoEquiv.symm (pairFin finTwoEquiv.symm
      (pairFin (Equiv.refl _) (Equiv.refl _))))))))

private def scannerWidth (k n : ℕ) : ℕ := k*((k+1)*((k+n+1)*((n+1)*(4*2))))

namespace CurrentBank
private def controlWidth : ℕ := 2*(4*(6*(frameWidth*((runtimeSize+1)*(2*14)))))
private def controlCodec :
    (Bool × Fin 4 × Fin 6 × Fin frameWidth × Fin (runtimeSize+1) × Bool × Fin 14) ≃ Fin controlWidth :=
  pairFin finTwoEquiv.symm (pairFin (Equiv.refl _) (pairFin (Equiv.refl _)
    (pairFin (Equiv.refl _) (pairFin (Equiv.refl _) (pairFin finTwoEquiv.symm (Equiv.refl _))))))

@[irreducible] def code (s : State) : List Bool :=
  addressCode s.addressed ++ List.ofFn s.actual ++ List.ofFn s.synthetic ++
  motorCode s.pre ++ keyCode s.key ++ List.ofFn s.query ++
  bitCode (scannerCodec (runtimeSize*4) (runtimeSize+1) s.native) ++ List.ofFn s.payload ++
  motorCode s.result ++ motorCode s.fields ++ keyCode s.row ++ motorCode s.opcodes ++
  bitCode (controlCodec (s.role,s.operation,s.slot,s.offset,s.bankProbe,s.bankLatch,s.phase))

def width : ℕ := addressWidth+runtimeSize+runtimeSize+motorWidth runtimeSize+
  keyWidth runtimeSize 4+runtimeSize*4+scannerWidth (runtimeSize*4) (runtimeSize+1)+
  (runtimeSize+1)+motorWidth (runtimeSize+1)+motorWidth 793800+keyWidth 793800 24+motorWidth 12+controlWidth

theorem code_length (s : State) : (code s).length = width := by
  simp only [code,width,List.length_append,List.length_ofFn,address_code_length,
    motor_code_length,key_length,bit_code_length,scannerWidth]

theorem code_injective : Function.Injective code := by
  intro s t h
  simp only [code,List.append_assoc] at h
  obtain ⟨ha,h⟩ := split_block (addressCode s.addressed) (addressCode t.addressed) _ _ addressWidth (address_code_length _) (address_code_length _) h
  obtain ⟨hactual,h⟩ := split_block (List.ofFn s.actual) (List.ofFn t.actual) _ _ runtimeSize (List.length_ofFn) (List.length_ofFn) h
  obtain ⟨hsyn,h⟩ := split_block (List.ofFn s.synthetic) (List.ofFn t.synthetic) _ _ runtimeSize (List.length_ofFn) (List.length_ofFn) h
  obtain ⟨hp,h⟩ := split_block (motorCode s.pre) (motorCode t.pre) _ _ (motorWidth runtimeSize) (motor_code_length _) (motor_code_length _) h
  obtain ⟨hk,h⟩ := split_block (keyCode s.key) (keyCode t.key) _ _ (keyWidth runtimeSize 4) (key_length _) (key_length _) h
  obtain ⟨hq,h⟩ := split_block (List.ofFn s.query) (List.ofFn t.query) _ _ (runtimeSize*4) (List.length_ofFn) (List.length_ofFn) h
  obtain ⟨hn,h⟩ := split_block (bitCode (scannerCodec (runtimeSize*4) (runtimeSize+1) s.native)) (bitCode (scannerCodec (runtimeSize*4) (runtimeSize+1) t.native)) _ _ _ (bit_code_length _) (bit_code_length _) h
  obtain ⟨hv,h⟩ := split_block (List.ofFn s.payload) (List.ofFn t.payload) _ _ (runtimeSize+1) (List.length_ofFn) (List.length_ofFn) h
  obtain ⟨hr,h⟩ := split_block (motorCode s.result) (motorCode t.result) _ _ (motorWidth (runtimeSize+1)) (motor_code_length _) (motor_code_length _) h
  obtain ⟨hf,h⟩ := split_block (motorCode s.fields) (motorCode t.fields) _ _ (motorWidth 793800) (motor_code_length _) (motor_code_length _) h
  obtain ⟨hrow,hc⟩ := split_block (keyCode s.row) (keyCode t.row) _ _ (keyWidth 793800 24) (key_length _) (key_length _) h
  obtain ⟨hopcode,hc⟩ := split_block (motorCode s.opcodes) (motorCode t.opcodes) _ _ (motorWidth 12) (motor_code_length _) (motor_code_length _) hc
  have hh := controlCodec.injective (bit_code_injective hc)
  simp only [Prod.mk.injEq] at hh
  exact State.ext (address_encoding ha) (List.ofFn_injective hactual) (List.ofFn_injective hsyn)
    hh.1 hh.2.1 (motor_encoding hp) (key_encoding hk) (List.ofFn_injective hq)
    ((scannerCodec _ _).injective (bit_code_injective hn)) (List.ofFn_injective hv)
    (motor_encoding hr) (motor_encoding hf) (key_encoding hrow)
    hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1 hh.2.2.2.2.2.1 hh.2.2.2.2.2.2 (motor_encoding hopcode)
end CurrentBank

@[irreducible] def code (s : State) : List Bool :=
  addressCode s.addressed ++ keyCode s.nativeKey ++ keyCode s.serviceKey ++
  bitCode (scannerCodec runtimeSize 21504 s.initialization) ++
  bitCode (scannerCodec 43008 21504 s.sampler) ++
  bitCode (scannerCodec (runtimeSize*4) (runtimeSize+1) s.native) ++
  bitCode (scannerCodec 21504 8 s.menu) ++ motorCode s.runtime ++ motorCode s.service ++
  bitCode (controlCodec (s.stage,s.operation,s.readyRole,s.rawService,s.resetProbe,
    s.freshRequested,s.committed,s.sourceLatch,s.freshLatch))

def stateWidth : ℕ := addressWidth+keyWidth runtimeSize 4+keyWidth 21504 2+
  scannerWidth runtimeSize 21504+scannerWidth 43008 21504+
  scannerWidth (runtimeSize*4) (runtimeSize+1)+scannerWidth 21504 8+
  motorWidth (runtimeSize+1)+motorWidth 21504+controlSize

theorem code_length (s : State) : (code s).length = stateWidth := by
  simp only [code,stateWidth,List.length_append,address_code_length,key_length,bit_code_length,
    motor_code_length,scannerWidth]

theorem code_encoding : Function.Injective code := by
  intro s t h
  simp only [code,List.append_assoc] at h
  obtain ⟨ha,h⟩ := split_block (addressCode s.addressed) (addressCode t.addressed) _ _ addressWidth (address_code_length _) (address_code_length _) h
  obtain ⟨hk,h⟩ := split_block (keyCode s.nativeKey) (keyCode t.nativeKey) _ _ (keyWidth runtimeSize 4) (key_length _) (key_length _) h
  obtain ⟨hb,h⟩ := split_block (keyCode s.serviceKey) (keyCode t.serviceKey) _ _ (keyWidth 21504 2) (key_length _) (key_length _) h
  obtain ⟨hi,h⟩ := split_block (bitCode (scannerCodec runtimeSize 21504 s.initialization)) (bitCode (scannerCodec runtimeSize 21504 t.initialization)) _ _ _ (bit_code_length _) (bit_code_length _) h
  obtain ⟨hs,h⟩ := split_block (bitCode (scannerCodec 43008 21504 s.sampler)) (bitCode (scannerCodec 43008 21504 t.sampler)) _ _ _ (bit_code_length _) (bit_code_length _) h
  obtain ⟨hn,h⟩ := split_block (bitCode (scannerCodec (runtimeSize*4) (runtimeSize+1) s.native)) (bitCode (scannerCodec (runtimeSize*4) (runtimeSize+1) t.native)) _ _ _ (bit_code_length _) (bit_code_length _) h
  obtain ⟨hm,h⟩ := split_block (bitCode (scannerCodec 21504 8 s.menu)) (bitCode (scannerCodec 21504 8 t.menu)) _ _ _ (bit_code_length _) (bit_code_length _) h
  obtain ⟨hr,h⟩ := split_block (motorCode s.runtime) (motorCode t.runtime) _ _ (motorWidth (runtimeSize+1)) (motor_code_length _) (motor_code_length _) h
  obtain ⟨he,hc⟩ := split_block (motorCode s.service) (motorCode t.service) _ _ (motorWidth 21504) (motor_code_length _) (motor_code_length _) h
  have hp := controlCodec.injective (bit_code_injective hc)
  simp only [Prod.mk.injEq] at hp
  exact State.ext (address_encoding ha) (key_encoding hk) (key_encoding hb)
    ((scannerCodec _ _).injective (bit_code_injective hi))
    ((scannerCodec _ _).injective (bit_code_injective hs))
    ((scannerCodec _ _).injective (bit_code_injective hn))
    ((scannerCodec _ _).injective (bit_code_injective hm))
    (motor_encoding hr) (motor_encoding he) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1
    hp.2.2.2.2.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2

private theorem row_code_length {k n : ℕ} (table : Fin k → Fin n) :
    (List.ofFn (fun i : Fin k => bitCode i ++ bitCode (table i))).flatten.length = k*(k+n) := by
  simp only [List.length_flatten,List.map_ofFn,Function.comp_def,List.length_append,bit_code_length]
  simp

theorem opcode_length (k : ℕ) :
    (List.ofFn (fun i : Fin k => bitCode i)).flatten.length = k*k := by
  simp only [List.length_flatten,List.map_ofFn,Function.comp_def,bit_code_length]
  simp

@[irreducible] private def producerOpcodes : List Bool := (List.ofFn (fun i : Fin 23 => bitCode i)).flatten
@[irreducible] private def producerMenuImage : List Bool :=
  (List.ofFn (fun i : Fin 21504 => bitCode i ++ bitCode (serviceMenuTable i))).flatten

private theorem producer_opcodes_length : producerOpcodes.length = 529 := by
  unfold producerOpcodes
  exact opcode_length 23
private theorem producer_menu_length : producerMenuImage.length = 21504*(21504+8) := by
  unfold producerMenuImage
  exact row_code_length serviceMenuTable

@[irreducible] def staticImage : List Bool := addressStaticImage ++ producerOpcodes ++
  endMask (runtimeSize+1) ++ endMask 21504 ++ endMask runtimeSize ++ endMask 4 ++
  endMask 21504 ++ endMask 2 ++ producerMenuImage

def staticWidth : ℕ := addressStaticWidth+529+(runtimeSize+2)+21505+(runtimeSize+1)+5+21505+3+21504*(21504+8)

private theorem static_length_aux (r : ℕ) :
    (addressStaticImage ++ producerOpcodes ++ endMask (r+1) ++ endMask 21504 ++
      endMask r ++ endMask 4 ++ endMask 21504 ++ endMask 2 ++ producerMenuImage).length =
    addressStaticWidth+529+(r+2)+21505+(r+1)+5+21505+3+21504*(21504+8) := by
  simp only [List.length_append,address_static_length,end_mask_length,
    producer_opcodes_length,producer_menu_length]

theorem static_length : staticImage.length = staticWidth := by
  unfold staticImage staticWidth
  exact static_length_aux runtimeSize

def bound : ℕ := programWidth+staticWidth+stateWidth+1

theorem charged (s : State) :
    programImage.length+staticImage.length+(code s).length < bound := by
  simp only [programImage,List.length_ofFn,static_length,code_length,bound]
  omega

theorem ports (s : State) (a b c d : Letter)
    (ha : actualRequest s = false) (hf : freshRequest s = false) :
    step s a b = step s c d := by
  cases hs : s.stage <;> simp_all [step,actualRequest,freshRequest]

private theorem saved_step (s : State) (a b : Letter) :
    (step s a b).addressed.outer.base.retained = s.addressed.outer.base.retained := by
  have hc := (address_context_step s.addressed).1
  cases hs : s.stage <;> simp [step,hs] <;>
    (repeat' first | split | simp_all [literalInstallStep])

theorem saved_cuts (s : State) (a b : Letter) (t : ℕ) :
    (run s a b t).addressed.outer.base.retained = s.addressed.outer.base.retained := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run,Function.iterate_succ_apply']
    exact (saved_step _ a b).trans ih

def ScannerSafe {k n : ℕ} (q : Scanner k n) : Prop := q.pc = 2 → q.row.val < k

theorem scanner_safe_step {k n : ℕ} (table : Fin k → Fin n) (q : Scanner k n)
    (h : ScannerSafe q) : ScannerSafe (installedGraphStep table q) := by
  intro hp
  rcases q with ⟨a,r,c,v,p,e⟩
  by_cases hr : r.val < k
  · fin_cases p <;> simp [installedGraphStep,instructionGraph,scannerStep,hr] at hp ⊢ <;>
      (repeat' first | split at hp | split | simp_all [ScannerSafe])
  · fin_cases p <;> simp [installedGraphStep,instructionGraph,scannerStep,hr] at hp

theorem graph_terminal {k n : ℕ} (table : Fin k → Fin n) (q : Scanner k n)
    (h : (q.pc = 2 ∧ q.row.val < k) ∨ q.pc = 3) : installedGraphStep table q = q := by
  rcases q with ⟨a,r,c,v,p,e⟩
  rcases h with ⟨h,hr⟩ | h
  · change p = 2 at h
    subst p
    simp [installedGraphStep,instructionGraph,scannerStep,hr]
  · change p = 3 at h
    subst p
    by_cases hr : r.val < k <;> simp [installedGraphStep,instructionGraph,scannerStep,hr]

private theorem native_exit (s : State) (n : ℕ)
    (hs : s.stage = .nativeScan) (hsa : ScannerSafe s.native)
    (he : ((installedGraphStep nativeTable)^[n] s.native).pc = 2) :
    ∃ t ≤ n+1, run s 0 0 t =
      {s with native := (installedGraphStep nativeTable)^[n] s.native,stage := .runtimeCopy} := by
  induction n generalizing s with
  | zero =>
    have hp : s.native.pc = 2 := he
    refine ⟨1,by omega,?_⟩
    simp [run,step,hs,hp]
  | succ n ih =>
    by_cases hp : s.native.pc = 2
    · have hfix := graph_terminal nativeTable s.native (Or.inl ⟨hp,hsa hp⟩)
      have hi := Function.iterate_fixed hfix (n+1)
      refine ⟨1,by omega,?_⟩
      rw [hi]
      simp [run,step,hs,hp]
    · by_cases hf : s.native.pc = 3
      · have hfix := graph_terminal nativeTable s.native (Or.inr hf)
        rw [Function.iterate_fixed hfix] at he
        have : (3 : Fin 4) = 2 := hf.symm.trans he
        cases this
      · let q : State := {s with native := installedGraphStep nativeTable s.native}
        have hq : step s 0 0 = q := by simp [q,step,hs,hp,hf]
        have hqs : q.stage = .nativeScan := hs
        have hqe : ((installedGraphStep nativeTable)^[n] q.native).pc = 2 := by
          rw [Function.iterate_succ_apply] at he
          exact he
        obtain ⟨t,ht,heq⟩ := ih q hqs (scanner_safe_step nativeTable s.native hsa) hqe
        refine ⟨t+1,by omega,?_⟩
        rw [run,Function.iterate_succ_apply,hq]
        change run q 0 0 t = _
        rw [heq]
        simp only [q,Function.iterate_succ_apply]

private theorem runtime_exit (s : State) (n : ℕ)
    (hs : s.stage = .runtimeCopy)
    (he : (motorRun (runtimeROM s) s.runtime n).pc = .halt) :
    ∃ t ≤ n+1, run s 0 0 t =
      {s with runtime := motorRun (runtimeROM s) s.runtime n,stage := .render} := by
  induction n generalizing s with
  | zero =>
    have hp : s.runtime.pc = .halt := he
    refine ⟨1,by omega,?_⟩
    simp [run,step,hs,hp,motorRun]
  | succ n ih =>
    by_cases hp : s.runtime.pc = .halt
    · have hfix : motorStep (runtimeROM s) s.runtime = s.runtime := by simp [motorStep,hp]
      have hi := Function.iterate_fixed hfix (n+1)
      refine ⟨1,by omega,?_⟩
      change (motorStep (runtimeROM s))^[n+1] s.runtime = _ at hi
      change ((motorStep (runtimeROM s))^[n+1] s.runtime).pc = .halt at he
      simp [run,step,hs,hp,motorRun,hi]
    · let q : State := {s with runtime := motorStep (runtimeROM s) s.runtime}
      have hq : step s 0 0 = q := by simp [q,step,hs,hp]
      have hqs : q.stage = .runtimeCopy := hs
      have hrom : runtimeROM q = runtimeROM s := rfl
      have hqe : (motorRun (runtimeROM q) q.runtime n).pc = .halt := by
        rw [motorRun,Function.iterate_succ_apply] at he
        exact he
      obtain ⟨t,ht,heq⟩ := ih q hqs hqe
      refine ⟨t+1,by omega,?_⟩
      rw [run,Function.iterate_succ_apply,hq]
      change run q 0 0 t = _
      rw [heq]
      simp only [q,hrom,motorRun,Function.iterate_succ_apply]

theorem render_exit (s : State) (n : ℕ)
    (hs : s.stage = .render) (he : (addressRun s.addressed n).control.pc = .returned) :
    ∃ t ≤ n+1, run s 0 0 t = {s with addressed := addressRun s.addressed n,stage := .emit} := by
  induction n generalizing s with
  | zero =>
    have hp : s.addressed.control.pc = .returned := he
    refine ⟨1,by omega,?_⟩
    simp [run,step,hs,hp,addressRun]
  | succ n ih =>
    by_cases hp : s.addressed.control.pc = .returned
    · have hfix : addressStep s.addressed = s.addressed := by simp [addressStep,hp]
      refine ⟨1,by omega,?_⟩
      simp [run,step,hs,hp,addressRun,Function.iterate_fixed hfix]
    · by_cases hf : s.addressed.control.pc = .fault
      · have hfix : addressStep s.addressed = s.addressed := by simp [addressStep,hf]
        have hi := Function.iterate_fixed hfix (n+1)
        change (addressStep^[n+1] s.addressed).control.pc = .returned at he
        rw [hi] at he
        have : AddressPC.fault = .returned := hf.symm.trans he
        cases this
      · let q : State := {s with addressed := addressStep s.addressed}
        have hq : step s 0 0 = q := by simp [q,step,hs,hp,hf]
        have hqs : q.stage = .render := hs
        have hqe : (addressRun q.addressed n).control.pc = .returned := by
          rw [addressRun,Function.iterate_succ_apply] at he
          exact he
        obtain ⟨t,ht,heq⟩ := ih q hqs hqe
        refine ⟨t+1,by omega,?_⟩
        rw [run,Function.iterate_succ_apply,hq]
        change run q 0 0 t = _
        rw [heq]
        simp only [q,addressRun,Function.iterate_succ_apply]


private theorem native_key_exit (s : State) (n : ℕ) (hs : s.stage = .nativeKey)
    (he : (keyRun s.nativeKey n).pc = 4)
    (hb : (keyRun s.nativeKey n).query.val < runtimeSize*4) :
    ∃ t ≤ n+1, run s 0 0 t =
      {s with nativeKey := keyRun s.nativeKey n,stage := .nativeScan, native := scannerEntry ⟨(keyRun s.nativeKey n).query.val,hb⟩} := by
  induction n generalizing s with
  | zero =>
    have hp : s.nativeKey.pc = 4 := he
    have hb' : s.nativeKey.query.val < runtimeSize*4 := hb
    refine ⟨1,by omega,?_⟩
    simp [run,step,hs,hp,keyRun,hb']
  | succ n ih =>
    by_cases hp : s.nativeKey.pc = 4
    · have hf : keyStep s.nativeKey = s.nativeKey := by simp [keyStep,hp]
      have hi := Function.iterate_fixed hf (n+1)
      have hb' : s.nativeKey.query.val < runtimeSize*4 := by simpa [keyRun,hi] using hb
      refine ⟨1,by omega,?_⟩
      simp [run,step,hs,hp,keyRun,hi,hb']
    · by_cases hf : s.nativeKey.pc = 5
      · have hh : keyStep s.nativeKey = s.nativeKey := by simp [keyStep,hf]
        have hi := Function.iterate_fixed hh (n+1)
        have he' : s.nativeKey.pc = 4 := by simpa [keyRun,hi] using he
        have : (5 : Fin 6) = 4 := hf.symm.trans he'
        cases this
      · let q : State := {s with nativeKey := keyStep s.nativeKey}
        have hq : step s 0 0 = q := by simp [q,step,hs,hp,hf]
        have hqs : q.stage = .nativeKey := hs
        have hqe : (keyRun q.nativeKey n).pc = 4 := by
          rw [keyRun,Function.iterate_succ_apply] at he
          exact he
        have hqb : (keyRun q.nativeKey n).query.val < runtimeSize*4 := by
          rw [keyRun,Function.iterate_succ_apply] at hb
          exact hb
        obtain ⟨t,ht,heq⟩ := ih q hqs hqe hqb
        refine ⟨t+1,by omega,?_⟩
        rw [run,Function.iterate_succ_apply,hq]
        change run q 0 0 t = _
        rw [heq]
        simp only [q,keyRun,Function.iterate_succ_apply]

/-- Prepared entry is an external relation. Address key/offset preparation and
classification of the original ready menu are not supplied by this definition. -/
def context (s : TransferSnapshot) (op : Operation) : TransferSnapshot :=
  {s with base := {s.base with retained := {s.base.retained with
    pre := s.base.retained.actual,operation := op}}}

def prepared (s : TransferSnapshot) (op : Operation) (slot : Fin 6) (i : Fin frameWidth) : State :=
  let c := context s op
  let installed := literalInstallStep^[motorTime programWidth] (literalInstallStart c)
  { addressed := addressEntry installed (frameKey c slot) i
    nativeKey := keyEntry (word (runtimeCodec s.base.retained.actual)) (operationCodec op)
    serviceKey := keyEntry (word (serviceCodec (entry .ordinary))) 0
    initialization := scannerEntry (runtimeCodec s.base.retained.actual)
    sampler := scannerEntry 0
    native := scannerEntry (nativeKeyCodec (s.base.retained.actual,op))
    menu := scannerEntry 0
    runtime := motorEntry (runtimeSize+1)
    service := motorEntry 21504
    stage := .nativeKey
    operation := operationCodec op
    readyRole := 0
    rawService := 0
    resetProbe := 0
    freshRequested := false
    committed := false
    sourceLatch := 0
    freshLatch := 0 }

private theorem keyed_native (p : State) (z : Runtime) (op : Operation)
    (hp : p.stage = .nativeKey)
    (hkey : p.nativeKey = keyEntry (word (runtimeCodec z)) (operationCodec op)) :
    ∃ t, ∃ q : State,
      run p 0 0 t = q ∧ q.stage = .nativeScan ∧
      q.native = scannerEntry (nativeKeyCodec (z,op)) ∧
      q.addressed = p.addressed ∧
      q.runtime = p.runtime ∧ q.operation = p.operation ∧ q.committed = p.committed := by
  let a := runtimeCodec z
  let b := operationCodec op
  have hk := key_execution a b
  have hb : (keyRun p.nativeKey (keyTime a b)).query.val < runtimeSize*4 := by
    rw [hkey]
    change (keyRun (keyEntry (word a) b) (keyTime a b)).query.val < _
    rw [hk.2]
    have := a.isLt
    have := b.isLt
    omega
  obtain ⟨t,_,he⟩ := native_key_exit p (keyTime a b) hp (by rw [hkey]; exact hk.1) hb
  let q : State := {p with nativeKey := keyRun p.nativeKey (keyTime a b),stage := .nativeScan, native := scannerEntry ⟨(keyRun p.nativeKey (keyTime a b)).query.val,hb⟩}
  have ha : (⟨(keyRun p.nativeKey (keyTime a b)).query.val,hb⟩ : Fin (runtimeSize*4)) =
      nativeKeyCodec (z,op) := by
    apply Fin.ext
    change (keyRun p.nativeKey (keyTime a b)).query.val = (nativeKeyCodec (z,op)).val
    rw [hkey]
    change (keyRun (keyEntry (word a) b) (keyTime a b)).query.val = _
    rw [hk.2]
    change a.val*4+b.val = b.val+4*a.val
    omega
  refine ⟨t,q,he,rfl,?_,rfl,rfl,rfl,rfl⟩
  exact congrArg scannerEntry ha

private theorem scanner_return_code {k n : ℕ} (v : Scanner k n) (x : Fin n)
    (hv : scannerResult v = some x) : v.pc = 2 ∧ v.accumulator.val = x.val := by
  have hp : v.pc = 2 := by
    by_contra h
    simp [scannerResult,h] at hv
  refine ⟨hp,?_⟩
  unfold scannerResult at hv
  simp only [hp,↓reduceIte] at hv
  split at hv
  · exact congrArg (fun y : Fin n => y.val) (Option.some.inj hv)
  · simp at hv

theorem native_endpoint (z : Runtime) (op : Operation) (d : Runtime)
    (hd : runtimeStep z op = some d) :
    ∃ n, ∃ v : Scanner (runtimeSize*4) (runtimeSize+1),
      (installedGraphStep nativeTable)^[n] (scannerEntry (nativeKeyCodec (z,op))) = v ∧
      v.pc = 2 ∧ v.accumulator.val = (optionalRuntimeCodec (some d)).val := by
  let a := nativeKeyCodec (z,op)
  let n := a.val*(runtimeSize*4+1)+(runtimeSize*4)+1+(runtimeSize+1)+1
  let v := (installedGraphStep nativeTable)^[n] (scannerEntry a)
  have hn := (installed_bounded_program z op (entry .ordinary) 0
    ⟨z,z,entry .ordinary,op,fun _ => 0,0,0,0,0,0,0,false,false⟩).1
  let f : Flight (runtimeSize*4) (runtimeSize+1) := flightEntry a
  have hf := (serial_adaptive_execution.1 (runtimeSize*4) (runtimeSize+1)
    nativeTable f n (by exact le_rfl)).1
  have hvf : v = (flightRun nativeTable f n).scanner := hf.symm
  have hr : (scannerResult (flightRun nativeTable f n).scanner).bind optionalRuntimeCodec.symm = some d := by
    rw [←hvf]
    rw [hd] at hn
    simpa only [nativeProgram,tableProgram] using hn
  rw [←hvf] at hr
  cases hv : scannerResult v with
  | none => simp [hv] at hr
  | some x =>
    have hx : optionalRuntimeCodec.symm x = some d := by simpa [hv] using hr
    have hx' : x = optionalRuntimeCodec (some d) := by
      exact (optionalRuntimeCodec.apply_symm_apply x).symm.trans (congrArg optionalRuntimeCodec hx)
    obtain ⟨hp,ha⟩ := scanner_return_code v x hv
    refine ⟨n,v,rfl,hp,?_⟩
    exact ha.trans (congrArg Fin.val hx')

private theorem word_injective {n : ℕ} : Function.Injective (@word n) := by
  intro a b h
  have hh := congrArg (fun f : Fin n → Bool => (List.ofFn f).count true) h
  change (List.ofFn (fun i : Fin n => decide (i.val < a.val))).count true =
    (List.ofFn (fun i : Fin n => decide (i.val < b.val))).count true at hh
  have ha := thermometer_count n a.val (Nat.le_of_lt a.isLt)
  have hb := thermometer_count n b.val (Nat.le_of_lt b.isLt)
  exact Fin.ext (ha.symm.trans (hh.trans hb))

theorem returned_code (q : State) (v : Fin (runtimeSize+1))
    (hc : q.committed = true) (ht : q.runtime.tape = word v) :
    returnedRuntime q = optionalRuntimeCodec.symm v := by
  have h : ∃ x : Fin (runtimeSize+1), q.runtime.tape = word x := ⟨v,ht⟩
  have hx : Classical.choose h = v := word_injective ((Classical.choose_spec h).symm.trans ht)
  simp only [returnedRuntime,hc,↓reduceIte,dif_pos h,hx]

theorem run_add (s : State) (a b : Letter) (m n : ℕ) :
    run s a b (m+n) = run (run s a b m) a b n := by
  simp only [run,Nat.add_comm m n,Function.iterate_add_apply]

@[irreducible] def copyTime (w : ℕ) : ℕ := motorTime w+2*w+2

theorem motor_return {w : ℕ} (rom : Fin w → Bool) :
    (motorRun rom (motorEntry w) (copyTime w)).pc = .halt ∧
    (motorRun rom (motorEntry w) (copyTime w)).tape = rom := by
  have h := (encoded_head_copy_refinement rom).2.2.2 0
  have hh := congrArg Motor.pc h
  have ht := congrArg Motor.tape h
  have he : (motorCheckpoint rom w le_rfl).tape = rom := by
    funext i
    simp [motorCheckpoint,encodeCopy,copyCheckpoint,i.isLt]
  simpa only [copyTime,Nat.add_zero,he] using And.intro hh ht

private theorem motor_return_from {w : ℕ} (rom : Fin w → Bool) (start : Motor w)
    (hr : start = motorEntry w) :
    (motorRun rom start (copyTime w)).pc = .halt ∧
      (motorRun rom start (copyTime w)).tape = rom := by
  rw [hr]
  exact motor_return rom

private theorem runtime_render (r : State) (value : Fin (runtimeSize+1))
    (hs : r.stage = .runtimeCopy) (hr : r.runtime = motorEntry (runtimeSize+1))
    (hv : r.native.accumulator.val = value.val) :
    ∃ t, ∃ a : State, run r 0 0 t = a ∧ a.stage = .render ∧
      a.runtime.tape = word value ∧ a.addressed = r.addressed ∧
      a.operation = r.operation ∧ a.committed = r.committed := by
  have hrom : runtimeROM r = word value := by
    funext j
    change decide (j.val < r.native.accumulator.val) = decide (j.val < value.val)
    rw [hv]
  let clock := copyTime (runtimeSize+1)
  let target := motorRun (runtimeROM r) r.runtime clock
  have htarget := motor_return_from (runtimeROM r) r.runtime hr
  obtain ⟨t,_,ht⟩ := runtime_exit r clock hs htarget.1
  exact ⟨t,{r with runtime := target,stage := .render},ht,rfl,
    htarget.2.trans hrom,rfl,rfl,rfl⟩

theorem native_render (p : State) (z : Runtime) (op : Operation) (d : Runtime)
    (hps : p.stage = .nativeKey)
    (hkey : p.nativeKey = keyEntry (word (runtimeCodec z)) (operationCodec op))
    (hpr : p.runtime = motorEntry (runtimeSize+1)) (hpo : p.operation = operationCodec op)
    (hpc : p.committed = false) (hd : runtimeStep z op = some d) :
    ∃ t, ∃ a : State, run p 0 0 t = a ∧ a.stage = .render ∧
      a.runtime.tape = word (optionalRuntimeCodec (some d)) ∧ a.addressed = p.addressed ∧
      a.operation = operationCodec op ∧ a.committed = false := by
  obtain ⟨tk,k,hk,hks,hkn,hka,hkr,hko,hkc⟩ := keyed_native p z op hps hkey
  obtain ⟨n,v,hv,hvp,hva⟩ := native_endpoint z op d hd
  have hsafe : ScannerSafe k.native := by rw [hkn]; simp [ScannerSafe,scannerEntry]
  have hnp : ((installedGraphStep nativeTable)^[n] k.native).pc = 2 := by rw [hkn,hv]; exact hvp
  obtain ⟨tn,_,hn⟩ := native_exit k n hks hsafe hnp
  let r : State := {k with native := v,stage := .runtimeCopy}
  have hnr : run k 0 0 tn = r := by simpa only [hkn,hv] using hn
  obtain ⟨tr,a,hra,has,hat,haa,hao,hac⟩ :=
    runtime_render r (optionalRuntimeCodec (some d)) rfl (hkr.trans hpr) hva
  refine ⟨tk+tn+tr,a,?_,has,hat,haa.trans hka,hao.trans (hko.trans hpo),
    hac.trans (hkc.trans hpc)⟩
  rw [run_add,run_add,hk,hnr,hra]




end LiveProducer
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
