/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Charged encoded-head and unary-address execution refines original event transfers. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorSerialExecution
import Mathlib.Data.List.OfFn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option Elab.async false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder NativeFullResidual
open RarePriorFiniteMonitor RarePriorResidentCode RarePriorSerialExecution

/-- The completion index is a finite field of the emitted event, not a counter. -/
inductive Event where
  | acquired (x : Letter)
  | rejected (x : Letter)
  | accepted (seed : Letter)
  | completed (index : Fin 4) (bit : Letter)
  | written (fields : Registers)
  | latched (snapshot : Option ThirdSnapshot)
  | moved (control : NativeControl)
  | held (fields : Registers)
  | stopped (bit : Letter)
  deriving DecidableEq, Fintype

def original : Event → OriginalEvent
  | .acquired x => .acquired x
  | .rejected x => .rejected x
  | .accepted x => .accepted x
  | .completed i b => .completed i.val b
  | .written r => .written r
  | .latched s => .latched s
  | .moved c => .moved c
  | .held r => .held r
  | .stopped b => .stopped b

def narrow : OriginalEvent → Option Event
  | .acquired x => some (.acquired x)
  | .rejected x => some (.rejected x)
  | .accepted x => some (.accepted x)
  | .completed i b => if h : i < 4 then some (.completed ⟨i,h⟩ b) else none
  | .written r => some (.written r)
  | .latched s => some (.latched s)
  | .moved c => some (.moved c)
  | .held r => some (.held r)
  | .stopped b => some (.stopped b)

private theorem completion_bounds (f : FiniteFields) (t : ℕ) (b : Letter)
    (ht : t < 4) :
    (completionEvents f t b).length ≤ 5 ∧
    ∀ e ∈ completionEvents f t b, (narrow e).map original = some e := by
  by_cases h : t = 2 <;>
    simp [completionEvents,h,narrow,original,ht]

private theorem payload_bounds (f : FiniteFields) (t : ℕ) (s : ActivePhase)
    (x : Letter) (ht : t < 4) :
    (payloadEvents f t s x).length ≤ 5 ∧
    ∀ e ∈ payloadEvents f t s x, (narrow e).map original = some e := by
  cases s <;> by_cases h : x = 0
  · simpa [payloadEvents,h] using completion_bounds f t 0 ht
  · simp [payloadEvents,h,narrow,original]
  · simp [payloadEvents,h,narrow,original]
  · simpa [payloadEvents,h] using completion_bounds f t 1 ht

/-- The sole semantic ROM source is the original eventBlock. -/
def eventROM (f : FiniteFields) (op : Operation) : Fin 6 → Option Event :=
  fun i => (eventBlock f op)[i.val]?.bind narrow

private theorem event_bounds (f : FiniteFields) (op : Operation) :
    (eventBlock f op).length ≤ 6 ∧
    ∀ e ∈ eventBlock f op, (narrow e).map original = some e := by
  cases op with
  | stop b => simp [eventBlock,narrow,original]
  | read x =>
    cases hc : f.control with
    | seed first =>
      cases first with
      | none => simp [eventBlock,hc,narrow,original]
      | some y => by_cases h : x = y <;> simp [eventBlock,hc,h,narrow,original]
    | early t s =>
      obtain ⟨hl,he⟩ := payload_bounds f t.val s x (by have := t.isLt; omega)
      constructor
      · simp only [eventBlock,hc,List.length_cons]; omega
      · intro e hm
        simp only [eventBlock,hc,List.mem_cons] at hm
        rcases hm with rfl | hm
        · rfl
        · exact he e hm
    | fourth c =>
      cases c with
      | active s =>
        obtain ⟨hl,he⟩ := payload_bounds f 3 s x (by omega)
        constructor
        · simp only [eventBlock,hc,List.length_cons]; omega
        · intro e hm
          simp only [eventBlock,hc,List.mem_cons] at hm
          rcases hm with rfl | hm
          · rfl
          · exact he e hm
      | pending b => simp [eventBlock,hc,narrow,original]
      | delivered => simp [eventBlock,hc,narrow,original]

private theorem padded_list {α : Type} (l : List α) (n : ℕ) (h : l.length ≤ n) :
    (List.ofFn (fun i : Fin n => l[i.val]?)).filterMap id = l := by
  induction n generalizing l with
  | zero => have he : l = [] := List.eq_nil_of_length_eq_zero (by omega); subst l; rfl
  | succ n ih =>
    cases l with
    | nil => simp
    | cons a l =>
      rw [List.ofFn_succ]
      simpa using congrArg (List.cons a) (ih l (by simpa using h))

/-- Six finite slots reconstruct the original block, including the third latch. -/
theorem six_slot_original_events (f : FiniteFields) (op : Operation) :
    (eventBlock f op).length ≤ 6 ∧
    (∀ i b, OriginalEvent.completed i b ∈ eventBlock f op → i < 4) ∧
    ((List.ofFn (eventROM f op)).filterMap id).map original = eventBlock f op := by
  obtain ⟨hl,he⟩ := event_bounds f op
  refine ⟨hl,?_,?_⟩
  · intro i b hi
    have hh := he _ hi
    by_contra hn
    simp [narrow,hn] at hh
  · have hp := padded_list (eventBlock f op) 6 hl
    have hh : List.ofFn (fun i : Fin 6 => ((eventBlock f op)[i.val]?.bind narrow).map original) =
        List.ofFn (fun i : Fin 6 => (eventBlock f op)[i.val]?) := by
      congr 1
      funext i
      cases h : (eventBlock f op)[i.val]? with
      | none => simp
      | some e =>
        have hm : e ∈ eventBlock f op := List.mem_of_getElem? h
        simpa [h] using he e hm
    calc
      _ = (List.ofFn (fun i : Fin 6 => (eventROM f op i).map original)).filterMap id := by
        change _ = (List.map (Option.map original) (List.ofFn (eventROM f op))).filterMap id
        rw [List.filterMap_map,List.map_filterMap]
        rfl
      _ = eventBlock f op := by change (List.ofFn (fun i : Fin 6 =>
          ((eventBlock f op)[i.val]?.bind narrow).map original)).filterMap id = _
                                rw [hh]; exact hp

inductive CopyPC where
  | read | write | emit | advance | halt
  deriving DecidableEq

instance : Fintype CopyPC := ⟨{.read,.write,.emit,.advance,.halt},by
  intro p; cases p <;> simp⟩

/-- The tape is bounded scratch, the head is a bounded position, and the latch
    holds the bit between its read and write. No output prefix is stored. -/
@[ext] structure CopyState (w : ℕ) where
  tape : Fin w → Bool
  head : Fin (w+1)
  pc : CopyPC
  latch : Bool
  deriving DecidableEq, Fintype

def copyEntry (w : ℕ) : CopyState w := ⟨fun _ => false,0,.read,false⟩

/-- One instruction reads one ROM bit, writes one scratch bit, exposes one
    scratch bit, or advances the head one cell. No source port is consulted. -/
def copyStep {w : ℕ} (rom : Fin w → Bool) (s : CopyState w) : CopyState w :=
  if h : s.head.val < w then
    let i : Fin w := ⟨s.head.val,h⟩
    match s.pc with
    | .read => {s with latch := rom i,pc := .write}
    | .write => {s with tape := Function.update s.tape i s.latch,pc := .emit}
    | .emit => {s with pc := .advance}
    | .advance => {s with head := ⟨s.head.val+1,by omega⟩,pc := .read}
    | .halt => s
  else {s with pc := .halt}

def copyOutput {w : ℕ} (s : CopyState w) : Option Bool :=
  if h : s.head.val < w then
    if s.pc = .emit then some (s.tape ⟨s.head.val,h⟩) else none
  else none

def copyRun {w : ℕ} (rom : Fin w → Bool) (s : CopyState w) (ticks : ℕ) : CopyState w :=
  (copyStep rom)^[ticks] s

/-- This observation list is external trace analysis, never a state field. -/
def copyTrace {w : ℕ} (rom : Fin w → Bool) (s : CopyState w) : ℕ → List Bool
  | 0 => []
  | n+1 => (copyOutput s).toList ++ copyTrace rom (copyStep rom s) n

def copyCheckpoint {w : ℕ} (rom : Fin w → Bool) (m : ℕ) (hm : m ≤ w) : CopyState w :=
  ⟨fun i => if i.val < m then rom i else false,⟨m,by omega⟩,.read,
    if h : m = 0 then false else rom ⟨m-1,by omega⟩⟩

private theorem copy_cycle {w : ℕ} (rom : Fin w → Bool) (m : ℕ) (hm : m < w) :
    copyRun rom (copyCheckpoint rom m (by omega)) 4 =
      copyCheckpoint rom (m+1) (by omega) ∧
    copyTrace rom (copyCheckpoint rom m (by omega)) 4 = [rom ⟨m,hm⟩] := by
  constructor
  · apply CopyState.ext
    · funext i
      simp only [copyRun,show 4 = 1+1+1+1 by rfl,Function.iterate_succ_apply',
        Function.iterate_zero_apply,copyStep,copyCheckpoint,hm,↓reduceDIte,
        Fin.val_mk]
      simp only [Function.update_apply]
      by_cases hi : i.val = m
      · have he : i = (⟨m,hm⟩ : Fin w) := Fin.ext hi
        subst i
        simp
      · have he : i ≠ (⟨m,hm⟩ : Fin w) := fun h => hi (congrArg Fin.val h)
        simp only [he,if_false]
        split_ifs <;> first | rfl | (exfalso; omega)
    · simp [copyRun,Function.iterate_succ_apply',copyStep,copyCheckpoint,hm]
    · simp [copyRun,Function.iterate_succ_apply',copyStep,copyCheckpoint,hm]
    · simp [copyRun,Function.iterate_succ_apply',copyStep,copyCheckpoint,hm]
  · simp [copyTrace,copyOutput,copyStep,copyCheckpoint,hm]

private theorem trace_add {w : ℕ} (rom : Fin w → Bool) (s : CopyState w) (m n : ℕ) :
    copyTrace rom s (m+n) = copyTrace rom s m ++ copyTrace rom (copyRun rom s m) n := by
  induction m generalizing s with
  | zero => simp [copyTrace,copyRun]
  | succ m ih =>
    simp only [Nat.succ_add,copyTrace,ih,copyRun,Function.iterate_succ_apply,
      List.append_assoc]

private theorem copy_prefix {w : ℕ} (rom : Fin w → Bool) (m : ℕ) (hm : m ≤ w) :
    copyRun rom (copyEntry w) (4*m) = copyCheckpoint rom m hm ∧
    copyTrace rom (copyEntry w) (4*m) = List.ofFn (fun i : Fin m => rom ⟨i.val,by omega⟩) := by
  induction m with
  | zero => simp [copyRun,copyEntry,copyCheckpoint,copyTrace]
  | succ m ih =>
    obtain ⟨hr,ht⟩ := ih (by omega)
    have hc := copy_cycle rom m (by omega)
    constructor
    · rw [show 4*(m+1) = 4+4*m by omega,copyRun,Function.iterate_add_apply]
      change copyRun rom (copyRun rom (copyEntry w) (4*m)) 4 = _
      rw [hr]
      exact hc.1
    · rw [show 4*(m+1) = 4*m+4 by omega,trace_add,hr,ht,hc.2]
      rw [List.ofFn_succ_last]
      rfl

/-- Every internal cut retains exactly the copied prefix and its current latch.
    The observable trace is a prefix of the same ROM; after install the complete
    scratch tape is the ROM, and the exhausted instruction is absorbing. -/
theorem paused_copy_refinement {w : ℕ} (rom : Fin w → Bool) :
    (∀ (m : ℕ) (hm : m ≤ w) (r : ℕ),
      copyRun rom (copyEntry w) (4*m+r) =
        copyRun rom (copyCheckpoint rom m hm) r ∧
      copyTrace rom (copyEntry w) (4*m+r) =
        List.ofFn (fun i : Fin m => rom ⟨i.val,by omega⟩) ++
          copyTrace rom (copyCheckpoint rom m hm) r) ∧
    (copyRun rom (copyEntry w) (4*w)).tape = rom ∧
    (∀ n, copyRun rom (copyEntry w) (4*w+1+n) =
      {copyCheckpoint rom w le_rfl with pc := .halt}) := by
  have hp := copy_prefix rom
  refine ⟨?_,?_,?_⟩
  · intro m hm r
    obtain ⟨hr,ht⟩ := hp m hm
    constructor
    · rw [Nat.add_comm (4*m) r,copyRun,Function.iterate_add_apply]
      exact congrArg ((copyStep rom)^[r]) hr
    · rw [trace_add,hr,ht]
  · rw [(hp w le_rfl).1]
    funext i
    simp [copyCheckpoint]
  · intro n
    rw [Nat.add_comm (4*w+1) n,copyRun,Function.iterate_add_apply]
    have he : copyRun rom (copyEntry w) (4*w+1) =
        {copyCheckpoint rom w le_rfl with pc := .halt} := by
      rw [copyRun,Function.iterate_succ_apply']
      change copyStep rom (copyRun rom (copyEntry w) (4*w)) = _
      rw [(hp w le_rfl).1]
      simp [copyStep,copyCheckpoint]
    change copyRun rom (copyRun rom (copyEntry w) (4*w+1)) n = _
    rw [he]
    exact Function.iterate_fixed (by simp [copyStep,copyCheckpoint]) n


/-- Explicit sum/product encoding of all event payloads. -/
def eventCodec : Event ≃ Fin 113451 :=
  ({ toFun := fun e => match e with
      | .acquired x => .inl x
      | .rejected x => .inr (.inl x)
      | .accepted x => .inr (.inr (.inl x))
      | .completed i b => .inr (.inr (.inr (.inl (i,b))))
      | .written r => .inr (.inr (.inr (.inr (.inl r))))
      | .latched s => .inr (.inr (.inr (.inr (.inr (.inl s)))))
      | .moved c => .inr (.inr (.inr (.inr (.inr (.inr (.inl c))))))
      | .held r => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl r)))))))
      | .stopped b => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr b)))))))
     invFun := fun e => match e with
      | .inl x => .acquired x
      | .inr (.inl x) => .rejected x
      | .inr (.inr (.inl x)) => .accepted x
      | .inr (.inr (.inr (.inl (i,b)))) => .completed i b
      | .inr (.inr (.inr (.inr (.inl r)))) => .written r
      | .inr (.inr (.inr (.inr (.inr (.inl s))))) => .latched s
      | .inr (.inr (.inr (.inr (.inr (.inr (.inl c)))))) => .moved c
      | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl r))))))) => .held r
      | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr b))))))) => .stopped b
     left_inv := by intro e; cases e <;> rfl
     right_inv := by intro e; rcases e with x|x|x|⟨i,b⟩|r|s|c|r|b <;> rfl } :
      Event ≃ (Letter ⊕ Letter ⊕ Letter ⊕ (Fin 4 × Letter) ⊕ Registers ⊕
        Option ThirdSnapshot ⊕ NativeControl ⊕ Registers ⊕ Letter)).trans
    (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _)
      (sumFin (pairFin (Equiv.refl _) (Equiv.refl _)) (sumFin registersCodec
        (sumFin ((Equiv.optionCongr snapshotCodec).trans (finSuccEquiv 20).symm)
          (sumFin controlCodec (sumFin registersCodec (Equiv.refl _)))))))))

def frameWidth : ℕ := 113452

def frameCodec : Option Event ≃ Fin frameWidth :=
  (Equiv.optionCongr eventCodec).trans (finSuccEquiv 113451).symm

/-- Each frame includes the absent/present marker as part of its paid code. -/
def frameTape (e : Option Event) : Fin frameWidth → Bool :=
  fun i => tapeBit (frameCodec e) i.val

private theorem tape_list {n : ℕ} (v : Fin n) :
    List.ofFn (fun i : Fin n => tapeBit v i.val) = bitCode v := by
  apply List.ext_getElem
  · simp [bit_code_length]
  · intro i hi hj
    simp only [List.getElem_ofFn,tapeBit]
    simp only [List.getElem?_eq_getElem hj,Option.getD_some]

/-- A renderer reads one finite ROM slot and stores only its single current frame. -/
def renderFrame : CopyState frameWidth :=
  copyEntry frameWidth

def frameRun (f : FiniteFields) (op : Operation) (slot : Fin 6) (ticks : ℕ) :
    CopyState frameWidth :=
  copyRun (frameTape (eventROM f op slot)) renderFrame ticks

/-- Frame decoding is a property of the external output, not an input operation
    or an instruction that evaluates the original semantics. -/
noncomputable def decodeFrame (bits : List Bool) : Option Event :=
  if h : ∃ v : Fin frameWidth, bitCode v = bits then
    frameCodec.symm (Classical.choose h) else none

private theorem decode_code (e : Option Event) : decodeFrame (bitCode (frameCodec e)) = e := by
  classical
  have h : ∃ v : Fin frameWidth, bitCode v = bitCode (frameCodec e) := ⟨_,rfl⟩
  simp only [decodeFrame,dif_pos h]
  have he := bit_code_injective (Classical.choose_spec h)
  rw [he,frameCodec.symm_apply_apply]

/-- Original events are actually obtained from the emitted finite frames. Every
    internal frame cut is governed by the generic paused-copy invariant. -/
theorem streamed_original_events (f : FiniteFields) (op : Operation) :
    (∀ slot : Fin 6,
      copyTrace (frameTape (eventROM f op slot)) renderFrame
        (4*frameWidth) = bitCode (frameCodec (eventROM f op slot)) ∧
      (frameRun f op slot (4*frameWidth)).tape = frameTape (eventROM f op slot)) ∧
    ((List.ofFn (fun slot : Fin 6 => decodeFrame
      (copyTrace (frameTape (eventROM f op slot)) renderFrame
        (4*frameWidth)))).filterMap id).map original = eventBlock f op := by
  have hc (slot : Fin 6) := paused_copy_refinement (frameTape (eventROM f op slot))
  have ht (slot : Fin 6) : copyTrace (frameTape (eventROM f op slot))
      renderFrame (4*frameWidth) = bitCode (frameCodec (eventROM f op slot)) := by
    change copyTrace (frameTape (eventROM f op slot)) (copyEntry frameWidth)
      (4*frameWidth) = _
    have hh := (copy_prefix (frameTape (eventROM f op slot)) frameWidth le_rfl).2
    rw [hh]
    exact tape_list _
  constructor
  · intro slot
    exact ⟨ht slot,(hc slot).2.1⟩
  · simp only [ht,decode_code]
    exact (six_slot_original_events f op).2.2


private def pcCodec : CopyPC ≃ Fin 5 where
  toFun | .read => 0 | .write => 1 | .emit => 2 | .advance => 3 | .halt => 4
  invFun i := match i.val with | 0 => .read | 1 => .write | 2 => .emit | 3 => .advance | _ => .halt
  left_inv p := by cases p <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def copyControlCodec (w : ℕ) : (Fin (w+1) × CopyPC × Bool) ≃ Fin ((w+1)*10) :=
  pairFin (Equiv.refl _) (pairFin pcCodec finTwoEquiv.symm)

/-- Both scratch and the between-instruction latch are serialized. -/
@[irreducible] def copyCode {w : ℕ} (s : CopyState w) : List Bool :=
  bitCode (copyControlCodec w (s.head,s.pc,s.latch)) ++ List.ofFn s.tape

def copyWidth (w : ℕ) : ℕ := (w+1)*10+w

private theorem copy_charge {w : ℕ} (s : CopyState w) : (copyCode s).length = copyWidth w := by
  simp [copyCode,copyWidth,bit_code_length]

private theorem copy_encoding {w : ℕ} : Function.Injective (@copyCode w) := by
  intro s t h
  have hh := congrArg (List.take ((w+1)*10)) h
  have ht := congrArg (List.drop ((w+1)*10)) h
  simp only [copyCode,List.take_left',bit_code_length] at hh
  have hr := (copyControlCodec w).injective (bit_code_injective hh)
  simp only [copyCode,List.drop_left',bit_code_length] at ht
  have hmem := List.ofFn_injective ht
  have hs : s.head = t.head ∧ s.pc = t.pc ∧ s.latch = t.latch := by
    simpa only [Prod.mk.injEq] using hr
  exact CopyState.ext hmem hs.1 hs.2.1 hs.2.2

/-- All concurrently retained native and scanner fields are paid, even when a
    particular rendering instruction leaves some of them unchanged. -/
@[ext] structure Retained where
  actual : Runtime
  synthetic : Runtime
  pre : Runtime
  next : Runtime
  service : RarePriorFairBitService.Service
  initialization : Flight runtimeSize 21504
  native : Flight (runtimeSize*4) (runtimeSize+1)
  sampler : Flight 43008 21504
  operation : Operation
  slot : Fin 7
  role : Fin 3
  deriving DecidableEq

def retainedSize : ℕ := runtimeSize*(runtimeSize*(runtimeSize*(runtimeSize*(21504*
  (flightSize runtimeSize 21504*(flightSize (runtimeSize*4) (runtimeSize+1)*
    (flightSize 43008 21504*(4*(7*3)))))))))

def retainedCodec : Retained ≃ Fin retainedSize :=
  ({ toFun := fun s => (s.actual,s.synthetic,s.pre,s.next,s.service,s.initialization,
      s.native,s.sampler,s.operation,s.slot,s.role)
     invFun := fun s => ⟨s.1,s.2.1,s.2.2.1,s.2.2.2.1,s.2.2.2.2.1,s.2.2.2.2.2.1,
       s.2.2.2.2.2.2.1,s.2.2.2.2.2.2.2.1,s.2.2.2.2.2.2.2.2.1,
       s.2.2.2.2.2.2.2.2.2.1,s.2.2.2.2.2.2.2.2.2.2⟩
     left_inv := by intro s; rfl
     right_inv := by intro s; rfl } :
      Retained ≃ (Runtime × Runtime × Runtime × Runtime × RarePriorFairBitService.Service ×
        Flight runtimeSize 21504 × Flight (runtimeSize*4) (runtimeSize+1) ×
        Flight 43008 21504 × Operation × Fin 7 × Fin 3)).trans
    (pairFin runtimeCodec (pairFin runtimeCodec (pairFin runtimeCodec (pairFin runtimeCodec
      (pairFin serviceCodec (pairFin (flightCodec runtimeSize 21504)
        (pairFin (flightCodec (runtimeSize*4) (runtimeSize+1))
          (pairFin (flightCodec 43008 21504)
            (pairFin operationCodec (pairFin (Equiv.refl _) (Equiv.refl _)))))))))))

/-- The addressed event table is static code, generated from eventBlock. -/
def eventKeyCodec : (FiniteFields × Operation × Fin 6) ≃ Fin (793800*24) :=
  pairFin fieldsCodec (pairFin operationCodec (Equiv.refl _))

def headerWidth : ℕ := 793800*793800
def eventWidth : ℕ := (793800*24)*frameWidth

/-- Padding B0 pays the old resident image without computing its huge length.
    The two ROM segments and five unary opcodes have explicit fixed widths. -/
@[irreducible] def programWidth : ℕ := B0+(headerWidth+(eventWidth+(25+64)))

private def headerImage (i : Fin headerWidth) : Bool :=
  let key := (finProdFinEquiv (m := 793800) (n := 793800)).symm i
  tapeBit key.1 key.2.val

@[irreducible] private def matrixRead {α : Type} {k n : ℕ} (e : α ≃ Fin k)
    (f : α → Fin n → Bool) (i : Fin (k*n)) : Bool :=
  let key := finProdFinEquiv.symm i
  f (e.symm key.1) key.2

private theorem matrix_read {α : Type} {k n : ℕ} (e : α ≃ Fin k)
    (f : α → Fin n → Bool) (a : α) (i : Fin n) :
    matrixRead e f (finProdFinEquiv (e a,i)) = f a i := by
  simp only [matrixRead,Equiv.symm_apply_apply]

private def eventImage (i : Fin eventWidth) : Bool :=
  matrixRead eventKeyCodec (fun row => frameTape (eventROM row.1 row.2.1 row.2.2)) i

/-- Finite sum/product addresses retain each physical image segment. -/
private theorem selected_segment {a b c d : ℕ} (p : Fin a → Bool)
    (q : Fin b → Bool) (r : Fin c → Bool) (t : Fin d → Bool) (i : Fin c) :
    Fin.addCases p (Fin.addCases q (Fin.addCases r t))
      (Fin.natAdd a (Fin.natAdd b (Fin.castAdd d i))) = r i := by
  rw [Fin.addCases_right,Fin.addCases_right,Fin.addCases_left]

private def rawProgramTape : Fin (B0+(headerWidth+(eventWidth+(25+64)))) → Bool :=
  Fin.addCases (fun i => residentCode[i.val]?.getD false)
    (Fin.addCases headerImage (Fin.addCases eventImage (fun i =>
      ((List.ofFn (fun j : Fin 5 => bitCode j)).flatten ++
        List.replicate 64 false)[i.val]?.getD false)))

def programTape (i : Fin programWidth) : Bool :=
  rawProgramTape (Fin.cast (by unfold programWidth; rfl) i)

def programImage : List Bool := List.ofFn programTape

/-- The installation tape is retained alongside header and current-event tapes.
    Stage tags include boot, install, header, frame, commit, done, fault and retry. -/
@[ext] structure RenderSnapshot where
  retained : Retained
  installation : CopyState programWidth
  header : CopyState 793800
  frame : CopyState frameWidth
  stage : Fin 8
  framing : Bool
  deriving DecidableEq

/-- Concrete finite boot data contains no source history or stream coordinate. -/
def bootSnapshot : RenderSnapshot where
  retained := {
    actual := runtimeInitial,synthetic := runtimeInitial,pre := runtimeInitial,next := runtimeInitial,
    service := RarePriorFairBitService.entry .ordinary,
    initialization := flightEntry (runtimeCodec runtimeInitial),native := flightEntry (nativeKeyCodec (runtimeInitial,.read 0)),
    sampler := flightEntry (bitKeyCodec (RarePriorFairBitService.entry .ordinary,0)),
    operation := .read 0,slot := 0,role := 0 }
  installation := copyEntry programWidth
  header := copyEntry 793800
  frame := renderFrame
  stage := 0
  framing := false

@[irreducible] def snapshot (s : RenderSnapshot) : List Bool :=
  bitCode (retainedCodec s.retained) ++ copyCode s.installation ++
  copyCode s.header ++ copyCode s.frame ++ bitCode s.stage ++ [s.framing]

def rendererBound : ℕ := programWidth + retainedSize + copyWidth programWidth +
  copyWidth 793800 + copyWidth frameWidth + 8 + 1 + 1

private theorem snapshot_charge (s : RenderSnapshot) :
    programImage.length + (snapshot s).length < rendererBound := by
  simp only [snapshot,List.length_append,bit_code_length,copy_charge,
    List.length_cons,List.length_nil,rendererBound,programImage,List.length_ofFn]
  omega

private theorem split_block {α : Type} (a b : List α) (u v : List α) (n : ℕ)
    (ha : a.length = n) (hb : b.length = n) (h : a++u = b++v) : a=b ∧ u=v := by
  exact List.append_inj h (ha.trans hb.symm)

private theorem snapshot_encoding : Function.Injective snapshot := by
  intro s t h
  simp only [snapshot] at h
  simp only [List.append_assoc] at h
  obtain ⟨hr,h⟩ := split_block (bitCode (retainedCodec s.retained))
    (bitCode (retainedCodec t.retained)) _ _ retainedSize
    (bit_code_length _) (bit_code_length _) h
  obtain ⟨hi,h⟩ := split_block (copyCode s.installation) (copyCode t.installation) _ _ (copyWidth programWidth) (copy_charge _) (copy_charge _) h
  obtain ⟨hh,h⟩ := split_block (copyCode s.header) (copyCode t.header) _ _ (copyWidth 793800) (copy_charge _) (copy_charge _) h
  obtain ⟨hf,h⟩ := split_block (copyCode s.frame) (copyCode t.frame) _ _ (copyWidth frameWidth) (copy_charge _) (copy_charge _) h
  obtain ⟨hp,hb⟩ := split_block (bitCode s.stage) (bitCode t.stage) _ _ 8 (bit_code_length _) (bit_code_length _) h
  exact RenderSnapshot.ext ((retainedCodec).injective (bit_code_injective hr))
    (copy_encoding hi) (copy_encoding hh) (copy_encoding hf) (bit_code_injective hp)
    (by simpa only [List.cons.injEq,and_true] using hb)

/-- Loader and frame instructions preserve every retained context field. -/
def installStep (s : RenderSnapshot) : RenderSnapshot :=
  {s with installation := copyStep programTape s.installation}

/-- The address selects one bit of the already retained installation tape.
    Address arithmetic is finite macro addressing, not an encoded carry program. -/
def frameAddress (s : RenderSnapshot) (slot : Fin 6) (i : Fin frameWidth) : Fin programWidth :=
  Fin.cast (by unfold programWidth; rfl)
    (Fin.natAdd B0 (Fin.natAdd headerWidth (Fin.castAdd (25+64)
      (finProdFinEquiv (eventKeyCodec (s.retained.pre.fields,s.retained.operation,slot),i)))))

def installedFrameROM (s : RenderSnapshot) (slot : Fin 6) : Fin frameWidth → Bool :=
  fun i => s.installation.tape (frameAddress s slot i)

def frameStep (slot : Fin 6) (s : RenderSnapshot) : RenderSnapshot :=
  {s with frame := copyStep (installedFrameROM s slot) s.frame}

private theorem program_frame (s : RenderSnapshot) (slot : Fin 6) :
    (fun i => programTape (frameAddress s slot i)) =
      frameTape (eventROM s.retained.pre.fields s.retained.operation slot) := by
  funext i
  let row := finProdFinEquiv (eventKeyCodec (s.retained.pre.fields,s.retained.operation,slot),i)
  have hc : Fin.cast (by unfold programWidth; rfl) (frameAddress s slot i) =
      Fin.natAdd B0 (Fin.natAdd headerWidth (Fin.castAdd (25+64) row)) := Fin.ext rfl
  have hs : rawProgramTape
      (Fin.natAdd B0 (Fin.natAdd headerWidth (Fin.castAdd (25+64) row))) = eventImage row :=
    selected_segment (fun i => residentCode[i.val]?.getD false) headerImage eventImage
      (fun i => ((List.ofFn (fun j : Fin 5 => bitCode j)).flatten ++
        List.replicate 64 false)[i.val]?.getD false) row
  have he : eventImage row = frameTape
      (eventROM s.retained.pre.fields s.retained.operation slot) i :=
    matrix_read eventKeyCodec (fun row => frameTape (eventROM row.1 row.2.1 row.2.2))
      (s.retained.pre.fields,s.retained.operation,slot) i
  exact (congrArg rawProgramTape hc).trans (hs.trans he)

private theorem install_run (s : RenderSnapshot) (ticks : ℕ) :
    installStep^[ticks] s = {s with installation := copyRun programTape s.installation ticks} := by
  let lift : CopyState programWidth → RenderSnapshot := fun q => {s with installation := q}
  have h : Function.Semiconj lift (copyStep programTape) installStep := fun _ => rfl
  exact (h.iterate_right ticks s.installation).symm

private theorem frame_run (slot : Fin 6) (s : RenderSnapshot) (ticks : ℕ) :
    (frameStep slot)^[ticks] s =
      {s with frame := copyRun (installedFrameROM s slot) s.frame ticks} := by
  let rom := installedFrameROM s slot
  let lift : CopyState frameWidth → RenderSnapshot := fun q => {s with frame := q}
  have h : Function.Semiconj lift (copyStep rom) (frameStep slot) := fun _ => rfl
  exact (h.iterate_right ticks s.frame).symm

/-- The complete endpoint carries proved execution, retained-context and tape
    equalities. The opaque package prevents eager reduction of its huge run. -/
structure Loaded (s : RenderSnapshot) where
  value : RenderSnapshot
  execution : value = installStep^[4*programWidth] {s with installation := copyEntry programWidth}
  context : value.retained = s.retained
  tape : value.installation.tape = programTape

opaque load (s : RenderSnapshot) : Loaded s := {
  value := {s with installation := copyRun programTape (copyEntry programWidth) (4*programWidth)}
  execution := (install_run {s with installation := copyEntry programWidth} (4*programWidth)).symm
  context := rfl
  tape := (paused_copy_refinement programTape).2.1 }

def installed (s : RenderSnapshot) : RenderSnapshot := (load s).value

private theorem installed_context (s : RenderSnapshot) : (installed s).retained = s.retained :=
  (load s).context

private theorem installed_rom (s : RenderSnapshot) (slot : Fin 6) :
    installedFrameROM (installed s) slot =
      frameTape (eventROM s.retained.pre.fields s.retained.operation slot) := by
  have hi : (installed s).installation.tape = programTape := (load s).tape
  unfold installedFrameROM
  rw [hi]
  have hh := program_frame (installed s) slot
  rw [installed_context] at hh
  exact hh

/-- Installation really copies resident bits. A current event really transfers
    through the retained latch and bounded scratch. Every such paused/fault cut
    has one injective code paying all retained flights and simultaneous copies. -/
theorem charged_installed_frames (s : RenderSnapshot) :
    Function.Injective snapshot ∧
    (∀ q : RenderSnapshot, programImage.length+(snapshot q).length < rendererBound) ∧
    installed s = installStep^[4*programWidth] {s with installation := copyEntry programWidth} ∧
    (installStep^[4*programWidth] {s with installation := copyEntry programWidth}).installation.tape =
      programTape ∧
    (∀ (slot : Fin 6) (m : ℕ) (hm : m ≤ frameWidth) (r : ℕ),
      ((frameStep slot)^[4*m+r] {installed s with frame := renderFrame}).frame =
        copyRun (frameTape (eventROM s.retained.pre.fields s.retained.operation slot))
          (copyCheckpoint (frameTape (eventROM s.retained.pre.fields s.retained.operation slot)) m hm) r) ∧
    ((List.ofFn (fun slot : Fin 6 => decodeFrame
      (copyTrace (installedFrameROM (installed s) slot)
        renderFrame (4*frameWidth)))).filterMap id).map original =
      eventBlock s.retained.pre.fields s.retained.operation := by
  refine ⟨snapshot_encoding,snapshot_charge,(load s).execution,?_,?_,?_⟩
  · rw [install_run]
    exact (paused_copy_refinement programTape).2.1
  · intro slot m hm r
    rw [frame_run]
    have hr : installedFrameROM {installed s with frame := renderFrame} slot =
        frameTape (eventROM s.retained.pre.fields s.retained.operation slot) :=
      installed_rom s slot
    rw [hr]
    exact ((paused_copy_refinement
      (frameTape (eventROM s.retained.pre.fields s.retained.operation slot))).1 m hm r).1
  · simp only [installed_rom]
    exact (streamed_original_events s.retained.pre.fields s.retained.operation).2


/-- Decoded observations, used only in external history analysis. -/
noncomputable def streamedBlock (f : FiniteFields) (op : Operation) : List OriginalEvent :=
  ((List.ofFn (fun slot : Fin 6 => decodeFrame
    (copyTrace (frameTape (eventROM f op slot)) renderFrame (4*frameWidth)))).filterMap id).map original

noncomputable def streamedBlocks (f : FiniteFields) : List Operation → List (List OriginalEvent)
  | [] => []
  | op::ops => streamedBlock f op :: match finiteStep f op with
    | none => []
    | some d => streamedBlocks d ops

private theorem streamed_blocks (f : FiniteFields) (ops : List Operation) :
    streamedBlocks f ops = eventBlocks f ops := by
  induction ops generalizing f with
  | nil => rfl
  | cons op ops ih =>
    simp only [streamedBlocks,eventBlocks]
    rw [show streamedBlock f op = eventBlock f op from (streamed_original_events f op).2]
    cases h : finiteStep f op <;> simp only [ih]

/-- The actual finite-frame transduction feeds the public original replay law,
    on every lawful source history, rather than a selected completed history. -/
theorem streamed_original_history (c d : AcquiredNativeState) (ω : Stream)
    (n k : ℕ) (ops : List Operation) (h : nativeDrive c ω n = some (ops,d,k)) :
    fullTranscript c ω n = some (ops,d.source.finiteFields,
      streamedBlocks c.source.finiteFields ops) ∧
    (streamedBlocks c.source.finiteFields ops).foldl replayBlock c.source.finiteFields =
      d.source.finiteFields := by
  rw [streamed_blocks]
  have hh := full_event_reconstruction c d ω n k ops h
  exact ⟨hh.1,hh.2.1⟩


/-! The literal copy motor retains the encoded head. Its physical probe moves
between adjacent cells; no numerical copy head is an instruction input. -/

inductive MotorPC where
  | seek | move | limit | read | write | emit | carry | halt | fault
  deriving DecidableEq

instance : Fintype MotorPC := ⟨{.seek,.move,.limit,.read,.write,.emit,.carry,.halt,.fault},by
  intro p; cases p <;> simp⟩

@[ext] structure Motor (w : ℕ) where
  tape : Fin w → Bool
  headBits : Fin (w+1) → Bool
  probe : Fin (w+1)
  pc : MotorPC
  latch : Bool
  deriving DecidableEq, Fintype

/-- Fixed adjacent rail wiring, rather than arithmetic on the encoded head.
Physical probe motion and reset to the fixed origin are primitives of this
rail model; a stored binary probe-address implementation is not asserted. -/
def nextCell {w : ℕ} (i : Fin (w+1)) : Option (Fin (w+1)) :=
  if h : i.val < w then some ⟨i.val+1,by omega⟩ else none

/-- Seek tests one head bit. Move follows one adjacent rail. Carry writes one
head bit. Read, write and emit each access one cell. The port-free motor does
not execute a decoder, a table evaluator or a source update. -/
def endCell {w : ℕ} (i : Fin (w+1)) : Bool := decide (i.val = w)

def motorStep {w : ℕ} (rom : Fin w → Bool) (s : Motor w) : Motor w :=
  match s.pc with
  | .seek => if s.headBits s.probe then {s with pc := .move} else {s with pc := .limit}
  | .limit => if endCell s.probe then {s with pc := .halt} else {s with pc := .read}
  | .move => match nextCell s.probe with
      | some i => {s with probe := i,pc := .seek}
      | none => {s with pc := .fault}
  | .read => if h : s.probe.val < w then
      {s with latch := rom ⟨s.probe.val,h⟩,pc := .write}
      else {s with pc := .fault}
  | .write => if h : s.probe.val < w then
      {s with tape := Function.update s.tape ⟨s.probe.val,h⟩ s.latch,pc := .emit}
      else {s with pc := .fault}
  | .emit => {s with pc := .carry}
  | .carry => {s with headBits := Function.update s.headBits s.probe true,probe := 0,pc := .seek}
  | .halt | .fault => s

def motorOutput {w : ℕ} (s : Motor w) : Option Bool :=
  if h : s.probe.val < w then
    if s.pc = .emit then some (s.tape ⟨s.probe.val,h⟩) else none
  else none

def motorRun {w : ℕ} (rom : Fin w → Bool) (s : Motor w) (ticks : ℕ) : Motor w :=
  (motorStep rom)^[ticks] s

/-- A trace is an external analysis object, absent from the running motor. -/
def motorTrace {w : ℕ} (rom : Fin w → Bool) (s : Motor w) : ℕ → List Bool
  | 0 => []
  | n+1 => (motorOutput s).toList ++ motorTrace rom (motorStep rom s) n

/-- Macro-to-literal mapping used only to state and prove checkpoints. -/
def encodeCopy {w : ℕ} (s : CopyState w) : Motor w :=
  ⟨s.tape,fun i => decide (i.val < s.head.val),0,.seek,s.latch⟩

def motorEntry (w : ℕ) : Motor w := encodeCopy (copyEntry w)

def motorCheckpoint {w : ℕ} (rom : Fin w → Bool) (m : ℕ) (hm : m ≤ w) : Motor w :=
  encodeCopy (copyCheckpoint rom m hm)

/-- The time reparametrization is external: it is never a machine register. -/
def motorTime (m : ℕ) : ℕ := m*m+5*m

private theorem motor_trace_add {w : ℕ} (rom : Fin w → Bool) (s : Motor w) (m n : ℕ) :
    motorTrace rom s (m+n) = motorTrace rom s m ++
      motorTrace rom (motorRun rom s m) n := by
  induction m generalizing s with
  | zero => simp [motorTrace,motorRun]
  | succ m ih =>
    simp only [Nat.succ_add,motorTrace,ih,motorRun,Function.iterate_succ_apply,
      List.append_assoc]

/-- The probe has tested exactly j head bits; no transfer has occurred. -/
private theorem motor_seek {w : ℕ} (rom : Fin w → Bool) (m : ℕ) (hm : m ≤ w)
    (j : ℕ) (hj : j ≤ m) :
    motorRun rom (motorCheckpoint rom m hm) (2*j) =
      {motorCheckpoint rom m hm with probe := ⟨j,by omega⟩} ∧
    motorTrace rom (motorCheckpoint rom m hm) (2*j) = [] := by
  induction j with
  | zero => simp [motorRun,motorTrace,motorCheckpoint,encodeCopy]
  | succ j ih =>
    obtain ⟨hr,ht⟩ := ih (by omega)
    have hjw : j < w := by omega
    have hjm : j < m := by omega
    have hstep : motorRun rom
        {motorCheckpoint rom m hm with probe := ⟨j,by omega⟩} 2 =
        {motorCheckpoint rom m hm with probe := ⟨j+1,by omega⟩} := by
      simp [motorRun,Function.iterate_succ_apply',motorStep,endCell,motorCheckpoint,
        encodeCopy,copyCheckpoint,hjm,nextCell,hjw]
    have hout : motorTrace rom
        {motorCheckpoint rom m hm with probe := ⟨j,by omega⟩} 2 = [] := by
      simp [motorTrace,motorOutput,motorStep,endCell,motorCheckpoint,encodeCopy,
        copyCheckpoint,hjm,nextCell,hjw]
    constructor
    · rw [show 2*(j+1)=2+2*j by omega,motorRun,Function.iterate_add_apply]
      change motorRun rom (motorRun rom (motorCheckpoint rom m hm) (2*j)) 2 = _
      rw [hr]; exact hstep
    · rw [show 2*(j+1)=2*j+2 by omega,motor_trace_add,hr,ht,hout]
      rfl

private theorem motor_cycle {w : ℕ} (rom : Fin w → Bool) (m : ℕ) (hm : m < w) :
    motorRun rom (motorCheckpoint rom m (by omega)) (2*m+6) =
      motorCheckpoint rom (m+1) (by omega) ∧
    motorTrace rom (motorCheckpoint rom m (by omega)) (2*m+6) = [rom ⟨m,hm⟩] := by
  have seek := motor_seek rom m (by omega) m le_rfl
  have old := copy_cycle rom m hm
  have head : Function.update (fun i : Fin (w+1) => decide (i.val < m))
      (⟨m,by omega⟩ : Fin (w+1)) true =
      (fun i : Fin (w+1) => decide (i.val < m+1)) := by
    funext i
    by_cases hi : i.val = m
    · have he : i = (⟨m,by omega⟩ : Fin (w+1)) := Fin.ext hi
      rw [he]; simp
    · have he : i ≠ (⟨m,by omega⟩ : Fin (w+1)) := fun h => hi (congrArg Fin.val h)
      rw [Function.update_of_ne he]
      exact decide_eq_decide.mpr (by omega : (i.val < m) ↔ (i.val < m+1))
  constructor
  · rw [Nat.add_comm (2*m) 6,motorRun,Function.iterate_add_apply]
    change motorRun rom (motorRun rom (motorCheckpoint rom m (by omega)) (2*m)) 6 = _
    rw [seek.1]
    have ht := congrArg CopyState.tape old.1
    have hl := congrArg CopyState.latch old.1
    apply Motor.ext
    · simpa [motorRun,Function.iterate_succ_apply',motorStep,endCell,motorCheckpoint,
        encodeCopy,copyCheckpoint,hm,show m ≠ w by omega,copyRun,copyStep] using ht
    · simpa [motorRun,Function.iterate_succ_apply',motorStep,endCell,motorCheckpoint,
        encodeCopy,copyCheckpoint,hm,show m ≠ w by omega] using head
    · simp [motorRun,Function.iterate_succ_apply',motorStep,endCell,motorCheckpoint,
        encodeCopy,copyCheckpoint,hm,show m ≠ w by omega]
    · simp [motorRun,Function.iterate_succ_apply',motorStep,endCell,motorCheckpoint,
        encodeCopy,copyCheckpoint,hm,show m ≠ w by omega]
    · simpa [motorRun,Function.iterate_succ_apply',motorStep,endCell,motorCheckpoint,
        encodeCopy,copyCheckpoint,hm,show m ≠ w by omega,copyRun,copyStep] using hl
  · rw [motor_trace_add,seek.1,seek.2]
    simp [motorTrace,motorOutput,motorStep,endCell,motorCheckpoint,encodeCopy,copyCheckpoint,hm,show m ≠ w by omega]

private theorem motor_prefix {w : ℕ} (rom : Fin w → Bool) (m : ℕ) (hm : m ≤ w) :
    motorRun rom (motorEntry w) (motorTime m) = motorCheckpoint rom m hm ∧
    motorTrace rom (motorEntry w) (motorTime m) =
      copyTrace rom (copyEntry w) (4*m) := by
  induction m with
  | zero => simp [motorRun,motorTime,motorEntry,motorCheckpoint,encodeCopy,copyEntry,copyCheckpoint,copyRun,copyTrace,motorTrace]
  | succ m ih =>
    obtain ⟨hr,ht⟩ := ih (by omega)
    have hc := motor_cycle rom m (by omega)
    have tt : motorTime (m+1) = motorTime m+(2*m+6) := by unfold motorTime; ring
    constructor
    · rw [tt,Nat.add_comm,motorRun,Function.iterate_add_apply]
      change motorRun rom (motorRun rom (motorEntry w) (motorTime m)) (2*m+6) = _
      rw [hr]; exact hc.1
    · rw [tt,motor_trace_add,hr,ht,hc.2]
      have old := copy_cycle rom m (by omega)
      rw [show 4*(m+1)=4*m+4 by omega,trace_add,(copy_prefix rom m (by omega)).1,old.2]

/-- Every paused instruction is reached by literal execution from the exact
encoded checkpoint. The traces agree with the old macro checkpoints without
reproving their tape-copy or original-event bounds. -/
theorem encoded_head_copy_refinement {w : ℕ} (rom : Fin w → Bool) :
    (∀ (m : ℕ) (hm : m ≤ w) (r : ℕ),
      motorRun rom (motorEntry w) (motorTime m+r) =
        motorRun rom (motorCheckpoint rom m hm) r ∧
      motorTrace rom (motorEntry w) (motorTime m+r) =
        copyTrace rom (copyEntry w) (4*m) ++
          motorTrace rom (motorCheckpoint rom m hm) r) ∧
    (motorRun rom (motorEntry w) (motorTime w)).tape = rom ∧
    (motorTrace rom (motorEntry w) (motorTime w) =
      List.ofFn (fun i : Fin w => rom i)) ∧
    (∀ n, motorRun rom (motorEntry w) (motorTime w+2*w+2+n) =
      {motorCheckpoint rom w le_rfl with probe := ⟨w,by omega⟩,pc := .halt}) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro m hm r
    obtain ⟨hr,ht⟩ := motor_prefix rom m hm
    constructor
    · rw [Nat.add_comm (motorTime m) r,motorRun,Function.iterate_add_apply]
      exact congrArg ((motorStep rom)^[r]) hr
    · rw [motor_trace_add,hr,ht]
  · rw [(motor_prefix rom w le_rfl).1]
    exact congrArg CopyState.tape ((copy_prefix rom w le_rfl).1.symm) |>.trans
      (paused_copy_refinement rom).2.1
  · rw [(motor_prefix rom w le_rfl).2,(copy_prefix rom w le_rfl).2]
  · intro n
    have seek := motor_seek rom w le_rfl w le_rfl
    have halt : motorRun rom (motorEntry w) (motorTime w+2*w+2) =
        {motorCheckpoint rom w le_rfl with probe := ⟨w,by omega⟩,pc := .halt} := by
      rw [show motorTime w+2*w+2 = 2+(motorTime w+2*w) by omega,motorRun,
        Function.iterate_add_apply]
      change motorRun rom (motorRun rom (motorEntry w) (motorTime w+2*w)) 2 = _
      have hp := (motor_prefix rom w le_rfl).1
      have hs : motorRun rom (motorEntry w) (motorTime w+2*w) =
          {motorCheckpoint rom w le_rfl with probe := ⟨w,by omega⟩} := by
        rw [Nat.add_comm (motorTime w) (2*w),motorRun,Function.iterate_add_apply]
        change motorRun rom (motorRun rom (motorEntry w) (motorTime w)) (2*w) = _
        rw [hp]; exact seek.1
      rw [hs]
      simp [motorRun,Function.iterate_succ_apply',motorStep,endCell,motorCheckpoint,encodeCopy,copyCheckpoint]
    rw [Nat.add_comm (motorTime w+2*w+2) n,motorRun,Function.iterate_add_apply]
    change motorRun rom (motorRun rom (motorEntry w) (motorTime w+2*w+2)) n = _
    rw [halt]
    exact Function.iterate_fixed (by simp [motorStep]) n


/-- An external analysis of the finite head tape; this count is not retained
and is never consulted by motorStep. -/
def headAmount {w : ℕ} (s : Motor w) : ℕ := (List.ofFn s.headBits).count true

/-- The decreasing potential is a function of the finite snapshot alone.
It is not a step budget or an elapsed-time field in the motor. -/
def motorRank {w : ℕ} (s : Motor w) : ℕ :=
  let base := (w-headAmount s)*(2*w+6)
  match s.pc with
  | .seek => base+2*(w-s.probe.val)+6
  | .move => base+2*(w-s.probe.val)+5
  | .limit => base+5
  | .read => base+4
  | .write => base+3
  | .emit => base+2
  | .carry => base+1
  | .halt | .fault => 0

/-- Head-control validity includes every instruction cut. The boundary is a
proof coordinate reconstructed from headBits, not a numerical head register. -/
def HeadControl {w : ℕ} (s : Motor w) (m : ℕ) : Prop :=
  m ≤ w ∧ s.headBits = (fun i => decide (i.val < m)) ∧
  match s.pc with
  | .seek => s.probe.val ≤ m
  | .move => s.probe.val < m
  | .limit => s.probe.val = m
  | .read | .write | .emit | .carry => s.probe.val = m ∧ m < w
  | .halt => s.probe.val = w ∧ m = w
  | .fault => False

private theorem thermometer_count (n m : ℕ) (hm : m ≤ n) :
    (List.ofFn (fun i : Fin n => decide (i.val < m))).count true = m := by
  induction n generalizing m with
  | zero =>
    have h : m = 0 := by omega
    subst m
    simp
  | succ n ih =>
    cases m with
    | zero => simp [List.count_replicate]
    | succ m =>
      rw [List.ofFn_succ]
      simpa [Fin.tail,Nat.succ_lt_succ_iff] using
        congrArg Nat.succ (ih m (by omega))

private theorem head_control_entry (w : ℕ) : HeadControl (motorEntry w) 0 := by
  simp [HeadControl,motorEntry,encodeCopy,copyEntry]

private theorem head_control_amount {w : ℕ} (s : Motor w) (m : ℕ)
    (h : HeadControl s m) : headAmount s = m := by
  rw [headAmount,h.2.1]
  exact thermometer_count (w+1) m (Nat.le_trans h.1 (Nat.le_succ w))

private theorem head_control_step {w : ℕ} (rom : Fin w → Bool) (s : Motor w)
    (m : ℕ) (h : HeadControl s m) :
    ∃ j, HeadControl (motorStep rom s) j ∧
      (s.pc ≠ .halt → motorRank (motorStep rom s) < motorRank s) := by
  have hm := h.1
  have hh := h.2.1
  have amount := head_control_amount s m h
  cases pc : s.pc with
  | seek =>
    have hp : s.probe.val ≤ m := by simpa [HeadControl,pc] using h.2.2
    by_cases hb : s.headBits s.probe = true
    · have hp' : s.probe.val < m := by simpa [hh] using hb
      refine ⟨m,?_,?_⟩
      · simpa [motorStep,pc,hb,HeadControl] using And.intro hm (And.intro hh hp')
      · intro _
        have hn : headAmount (motorStep rom s) = m := by simpa [motorStep,pc,hb,headAmount] using amount
        unfold motorRank
        rw [hn,amount]
        simp [motorStep,pc,hb]
    · have hp' : s.probe.val = m := by
        have hn : ¬s.probe.val < m := by simpa [hh] using hb
        omega
      refine ⟨m,?_,?_⟩
      · simpa [motorStep,pc,hb,HeadControl] using And.intro hm (And.intro hh hp')
      · intro _
        have hn : headAmount (motorStep rom s) = m := by simpa [motorStep,pc,hb,headAmount] using amount
        unfold motorRank
        rw [hn,amount]
        simp [motorStep,pc,hb]
  | limit =>
    have hp : s.probe.val = m := by simpa [HeadControl,pc] using h.2.2
    by_cases hw : s.probe.val = w
    · refine ⟨m,?_,?_⟩
      · simpa [motorStep,pc,endCell,hw,HeadControl] using
          And.intro hm (And.intro hh (And.intro hw (hp.symm.trans hw)))
      · intro _; simp [motorRank,motorStep,pc,endCell,hw]
    · have hmw : m < w := by omega
      refine ⟨m,?_,?_⟩
      · simpa [motorStep,pc,endCell,hw,HeadControl] using
          And.intro hm (And.intro hh (And.intro hp hmw))
      · intro _
        have hn : headAmount (motorStep rom s) = m := by simpa [motorStep,pc,endCell,hw,headAmount] using amount
        unfold motorRank
        rw [hn,amount]
        simp [motorStep,pc,endCell,hw]

  | move =>
    have hp : s.probe.val < m := by simpa [HeadControl,pc] using h.2.2
    have hw : s.probe.val < w := by omega
    refine ⟨m,?_,?_⟩
    · simp only [motorStep,pc,nextCell,hw,↓reduceDIte,HeadControl]
      exact ⟨hm,hh,by change s.probe.val+1 ≤ m; omega⟩
    · intro _
      have hn : headAmount (motorStep rom s) = m := by simpa [motorStep,pc,nextCell,hw,headAmount] using amount
      unfold motorRank
      rw [hn,amount]
      simp only [motorStep,pc,nextCell,hw,↓reduceDIte,Fin.val_mk]
      omega
  | read =>
    have hp : s.probe.val = m ∧ m < w := by simpa [HeadControl,pc] using h.2.2
    have hw : s.probe.val < w := by omega
    refine ⟨m,?_,?_⟩
    · simp only [motorStep,pc,hw,↓reduceDIte,HeadControl]; exact ⟨hm,hh,hp⟩
    · intro _
      have hn : headAmount (motorStep rom s) = m := by simpa [motorStep,pc,hw,headAmount] using amount
      unfold motorRank
      rw [hn,amount]
      simp [motorStep,pc,hw]
  | write =>
    have hp : s.probe.val = m ∧ m < w := by simpa [HeadControl,pc] using h.2.2
    have hw : s.probe.val < w := by omega
    refine ⟨m,?_,?_⟩
    · simp only [motorStep,pc,hw,↓reduceDIte,HeadControl]; exact ⟨hm,hh,hp⟩
    · intro _
      have hn : headAmount (motorStep rom s) = m := by simpa [motorStep,pc,hw,headAmount] using amount
      unfold motorRank
      rw [hn,amount]
      simp [motorStep,pc,hw]
  | emit =>
    have hp : s.probe.val = m ∧ m < w := by simpa [HeadControl,pc] using h.2.2
    refine ⟨m,?_,?_⟩
    · simp only [motorStep,pc,HeadControl]; exact ⟨hm,hh,hp⟩
    · intro _
      have hn : headAmount (motorStep rom s) = m := by simpa [motorStep,pc,headAmount] using amount
      unfold motorRank
      rw [hn,amount]
      simp [motorStep,pc]
  | carry =>
    have hp : s.probe.val = m ∧ m < w := by simpa [HeadControl,pc] using h.2.2
    have bits : Function.update s.headBits s.probe true =
        (fun i : Fin (w+1) => decide (i.val < m+1)) := by
      funext i
      by_cases hi : i = s.probe
      · rw [hi,Function.update_self]
        simp [hp.1]
      · rw [Function.update_of_ne hi,hh]
        have hv : i.val ≠ m := fun hv => hi (Fin.ext (hv.trans hp.1.symm))
        exact decide_eq_decide.mpr (by omega : (i.val < m) ↔ (i.val < m+1))
    have hj : HeadControl (motorStep rom s) (m+1) := by
      simp only [motorStep,pc,HeadControl,Fin.val_zero]
      exact ⟨by omega,bits,by omega⟩
    refine ⟨m+1,hj,?_⟩
    intro _
    have hn := head_control_amount (motorStep rom s) (m+1) hj
    unfold motorRank
    rw [hn,amount]
    simp only [motorStep,pc,Fin.val_zero,Nat.sub_zero]
    have hw : w-m = (w-(m+1))+1 := by omega
    rw [hw,Nat.add_mul]
    omega
  | halt =>
    refine ⟨m,?_,?_⟩
    · simpa [motorStep,pc] using h
    · intro hn; exact (hn rfl).elim
  | fault => have hf : False := by simpa [HeadControl,pc] using h.2.2
             exact hf.elim

private theorem motor_all_cuts {w : ℕ} (rom : Fin w → Bool) (ticks : ℕ) :
    ∃ m, HeadControl (motorRun rom (motorEntry w) ticks) m := by
  induction ticks with
  | zero => exact ⟨0,head_control_entry w⟩
  | succ n ih =>
    obtain ⟨m,hm⟩ := ih
    obtain ⟨j,hj,_⟩ := head_control_step rom _ m hm
    rw [motorRun,Function.iterate_succ_apply']
    exact ⟨j,hj⟩


private def motorPCCodec : MotorPC ≃ Fin 9 where
  toFun
    | .seek => 0 | .move => 1 | .limit => 2 | .read => 3 | .write => 4
    | .emit => 5 | .carry => 6 | .halt => 7 | .fault => 8
  invFun i := match i.val with
    | 0 => .seek | 1 => .move | 2 => .limit | 3 => .read | 4 => .write
    | 5 => .emit | 6 => .carry | 7 => .halt | _ => .fault
  left_inv p := by cases p <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def motorControlCodec (w : ℕ) : (Fin (w+1) × MotorPC × Bool) ≃ Fin ((w+1)*18) :=
  pairFin (Equiv.refl _) (pairFin motorPCCodec finTwoEquiv.symm)

/-- Head bits, physical probe, PC, latch and scratch all occur in the code. -/
@[irreducible] def motorCode {w : ℕ} (s : Motor w) : List Bool :=
  bitCode (motorControlCodec w (s.probe,s.pc,s.latch)) ++
    List.ofFn s.headBits ++ List.ofFn s.tape

def motorWidth (w : ℕ) : ℕ := (w+1)*18+(w+1)+w

private theorem motor_code_length {w : ℕ} (s : Motor w) : (motorCode s).length = motorWidth w := by
  simp only [motorCode,motorWidth,List.length_append,List.length_ofFn,bit_code_length]

private theorem motor_encoding {w : ℕ} : Function.Injective (@motorCode w) := by
  intro s t h
  simp only [motorCode,List.append_assoc] at h
  obtain ⟨hc,h⟩ := split_block (bitCode (motorControlCodec w (s.probe,s.pc,s.latch)))
    (bitCode (motorControlCodec w (t.probe,t.pc,t.latch))) _ _ ((w+1)*18)
    (bit_code_length _) (bit_code_length _) h
  obtain ⟨hh,ht⟩ := split_block (List.ofFn s.headBits) (List.ofFn t.headBits) _ _ (w+1)
    (List.length_ofFn) (List.length_ofFn) h
  have hp := (motorControlCodec w).injective (bit_code_injective hc)
  have he : s.probe=t.probe ∧ s.pc=t.pc ∧ s.latch=t.latch := by
    simpa only [Prod.mk.injEq] using hp
  exact Motor.ext (List.ofFn_injective ht) (List.ofFn_injective hh) he.1 he.2.1 he.2.2

/-- The immutable opcode records and all three physical end-of-rail masks are
paid together with the original image. -/
@[irreducible] private def motorOpcodes : List Bool :=
  (List.ofFn (fun i : Fin 9 => bitCode i)).flatten

@[irreducible] private def endMask (w : ℕ) : List Bool :=
  List.ofFn (fun i : Fin (w+1) => endCell i)

private theorem end_mask_length (w : ℕ) : (endMask w).length = w+1 := by
  simp only [endMask,List.length_ofFn]

private theorem motor_opcodes_length : motorOpcodes.length = 81 := by
  simp [motorOpcodes,List.length_flatten,List.map_map,bit_code_length]

@[irreducible] def motorStaticImage : List Bool :=
  motorOpcodes ++ endMask programWidth ++ endMask 793800 ++ endMask frameWidth

@[irreducible] def motorStaticWidth : ℕ := 81+(programWidth+1)+(793800+1)+(frameWidth+1)

private theorem motor_static_length_aux (p h f : ℕ) :
    (motorOpcodes ++ endMask p ++ endMask h ++ endMask f).length =
      81+(p+1)+(h+1)+(f+1) := by
  simp only [List.length_append,motor_opcodes_length,end_mask_length,Nat.add_assoc]

private theorem motor_static_length : motorStaticImage.length = motorStaticWidth := by
  unfold motorStaticImage motorStaticWidth
  exact motor_static_length_aux programWidth 793800 frameWidth

/-- Transfer attachment with every retained old snapshot and every literal
installation, header and current-frame motor paid simultaneously. -/
@[ext] structure TransferSnapshot where
  base : RenderSnapshot
  installation : Motor programWidth
  header : Motor 793800
  frame : Motor frameWidth
  deriving DecidableEq

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

private theorem address_execution (s : TransferSnapshot) (a : Fin frameKeyWidth) (i : Fin frameWidth) :
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

private theorem address_code_length (s : AddressState) : (addressCode s).length = addressWidth := by
  simp only [addressCode,addressWidth,List.length_append,transfer_code_length,
    address_control_length,List.length_ofFn,motor_code_length]

private theorem address_encoding : Function.Injective addressCode := by
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

private theorem address_static_length : addressStaticImage.length = addressStaticWidth := by
  unfold addressStaticImage addressStaticWidth
  exact address_static_length_aux frameBase frameKeyWidth

def literalAddressBound : ℕ := programWidth+addressStaticWidth+addressWidth+1

private theorem address_charge (s : AddressState) :
    programImage.length+addressStaticImage.length+(addressCode s).length < literalAddressBound := by
  simp only [programImage,List.length_ofFn,address_static_length,address_code_length,literalAddressBound]
  omega

private theorem address_context_step (s : AddressState) :
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
private theorem address_frame_index (s : TransferSnapshot) (slot : Fin 6) (i : Fin frameWidth) :
    addressIndex (frameKey s slot) i = frameAddress s.base slot i := by
  apply Fin.ext
  change frameBase+(frameKey s slot).val*frameWidth+i.val =
    B0+(headerWidth+(i.val+frameWidth*
      (eventKeyCodec (s.base.retained.pre.fields,s.base.retained.operation,slot)).val))
  simp only [frameBase,frameKey,Fin.val_cast]
  rw [Nat.mul_comm]
  omega

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
    dsimp only
    let installed := literalInstallStep^[motorTime programWidth] (literalInstallStart s)
    let a := frameKey s slot
    obtain ⟨ticks,q,hq,hp,_,_,hl,_⟩ := address_execution installed a i
    refine ⟨ticks,q,hq,hp,?_⟩
    have ht : installed.installation.tape = programTape :=
      (charged_literal_transfers s).2.2.2.2.1
    have ha := address_frame_index s slot i
    rw [ht,show (⟨frameBase+a.val*frameWidth+i.val,frame_address_bound a i⟩ : Fin programWidth) = addressIndex a i from rfl,ha] at hl
    exact hl.trans (congrFun (program_frame s.base slot) i)


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

private theorem key_execution {k m : ℕ} (a : Fin k) (b : Fin m) :
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

private theorem code_length (s : State) : (code s).length = width := by
  simp only [code,width,List.length_append,List.length_ofFn,address_code_length,
    motor_code_length,key_length,bit_code_length,scannerWidth]

private theorem code_injective : Function.Injective code := by
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

private theorem code_length (s : State) : (code s).length = stateWidth := by
  simp only [code,stateWidth,List.length_append,address_code_length,key_length,bit_code_length,
    motor_code_length,scannerWidth]

private theorem code_encoding : Function.Injective code := by
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

private theorem opcode_length (k : ℕ) :
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

private theorem static_length : staticImage.length = staticWidth := by
  unfold staticImage staticWidth
  exact static_length_aux runtimeSize

def bound : ℕ := programWidth+staticWidth+stateWidth+1

private theorem charged (s : State) :
    programImage.length+staticImage.length+(code s).length < bound := by
  simp only [programImage,List.length_ofFn,static_length,code_length,bound]
  omega

private theorem ports (s : State) (a b c d : Letter)
    (ha : actualRequest s = false) (hf : freshRequest s = false) :
    step s a b = step s c d := by
  cases hs : s.stage <;> simp_all [step,actualRequest,freshRequest]

private theorem saved_step (s : State) (a b : Letter) :
    (step s a b).addressed.outer.base.retained = s.addressed.outer.base.retained := by
  have hc := (address_context_step s.addressed).1
  cases hs : s.stage <;> simp [step,hs] <;>
    (repeat' first | split | simp_all [literalInstallStep])

private theorem saved_cuts (s : State) (a b : Letter) (t : ℕ) :
    (run s a b t).addressed.outer.base.retained = s.addressed.outer.base.retained := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run,Function.iterate_succ_apply']
    exact (saved_step _ a b).trans ih

private def ScannerSafe {k n : ℕ} (q : Scanner k n) : Prop := q.pc = 2 → q.row.val < k

private theorem scanner_safe_step {k n : ℕ} (table : Fin k → Fin n) (q : Scanner k n)
    (h : ScannerSafe q) : ScannerSafe (installedGraphStep table q) := by
  intro hp
  rcases q with ⟨a,r,c,v,p,e⟩
  by_cases hr : r.val < k
  · fin_cases p <;> simp [installedGraphStep,instructionGraph,scannerStep,hr] at hp ⊢ <;>
      (repeat' first | split at hp | split | simp_all [ScannerSafe])
  · fin_cases p <;> simp [installedGraphStep,instructionGraph,scannerStep,hr] at hp

private theorem graph_terminal {k n : ℕ} (table : Fin k → Fin n) (q : Scanner k n)
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

private theorem render_exit (s : State) (n : ℕ)
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

private theorem native_endpoint (z : Runtime) (op : Operation) (d : Runtime)
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

private theorem returned_code (q : State) (v : Fin (runtimeSize+1))
    (hc : q.committed = true) (ht : q.runtime.tape = word v) :
    returnedRuntime q = optionalRuntimeCodec.symm v := by
  have h : ∃ x : Fin (runtimeSize+1), q.runtime.tape = word x := ⟨v,ht⟩
  have hx : Classical.choose h = v := word_injective ((Classical.choose_spec h).symm.trans ht)
  simp only [returnedRuntime,hc,↓reduceIte,dif_pos h,hx]

private theorem run_add (s : State) (a b : Letter) (m n : ℕ) :
    run s a b (m+n) = run (run s a b m) a b n := by
  simp only [run,Nat.add_comm m n,Function.iterate_add_apply]

@[irreducible] def copyTime (w : ℕ) : ℕ := motorTime w+2*w+2

private theorem motor_return {w : ℕ} (rom : Fin w → Bool) :
    (motorRun rom (motorEntry w) (copyTime w)).pc = .halt ∧
    (motorRun rom (motorEntry w) (copyTime w)).tape = rom := by
  have h := (encoded_head_copy_refinement rom).2.2.2 0
  have hh := congrArg Motor.pc h
  have ht := congrArg Motor.tape h
  have he : (motorCheckpoint rom w le_rfl).tape = rom := by
    funext i
    simp [motorCheckpoint,encodeCopy,copyCheckpoint,i.isLt]
  simpa only [copyTime,Nat.add_zero,he] using And.intro hh ht

private theorem native_render (p : State) (z : Runtime) (op : Operation) (d : Runtime)
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
  have hrom : runtimeROM r = word (optionalRuntimeCodec (some d)) := by
    funext j
    change decide (j.val < v.accumulator.val) = decide (j.val < (optionalRuntimeCodec (some d)).val)
    rw [hva]
  let w := runtimeSize+1
  let clock := copyTime w
  let target := motorRun (runtimeROM r) r.runtime clock
  have htarget : target.pc = .halt ∧ target.tape = word (optionalRuntimeCodec (some d)) := by
    have hr : r.runtime = motorEntry w := hkr.trans hpr
    simpa only [target,hr,hrom] using motor_return (word (optionalRuntimeCodec (some d)))
  obtain ⟨tr,_,hr⟩ := runtime_exit r clock rfl htarget.1
  let a : State := {r with runtime := target,stage := .render}
  have hra : run r 0 0 tr = a := hr
  refine ⟨tk+tn+tr,a,?_,rfl,htarget.2,hka,hko.trans hpo,hkc.trans hpc⟩
  rw [run_add,run_add,hk,hnr,hra]



private theorem native_commit (s : TransferSnapshot) (op : Operation) (slot : Fin 6)
    (i : Fin frameWidth) (d : Runtime) (hd : runtimeStep s.base.retained.actual op = some d) :
    ∃ t, ∃ q : State,
      run (prepared s op slot i) 0 0 t = q ∧ q.stage = .returned ∧
      returnedRuntime q = some d ∧ returnedOperation q = some op ∧
      ∃ u ≤ t, emitted (run (prepared s op slot i) 0 0 u) =
        some (frameTape (eventROM s.base.retained.actual.fields op slot) i) := by
  obtain ⟨t0,a,ht0,has,htape,haddr,hop,hcomm⟩ := native_render
    (prepared s op slot i) s.base.retained.actual op d rfl rfl rfl rfl rfl hd
  let c := context s op
  obtain ⟨na,ab,hab,hap,hbit⟩ := (charged_address_execution c).2.2.2.2 slot i
  have had : a.addressed = addressEntry
      (literalInstallStep^[motorTime programWidth] (literalInstallStart c)) (frameKey c slot) i := haddr
  have hap' : (addressRun a.addressed na).control.pc = .returned := by rw [had,hab]; exact hap
  obtain ⟨ta,_,ha⟩ := render_exit a na has hap'
  let e : State := {a with addressed := ab,stage := .emit}
  have hae : run a 0 0 ta = e := by simpa only [had,hab] using ha
  have he : emitted e = some (frameTape (eventROM s.base.retained.actual.fields op slot) i) := by
    change some ab.control.latch = _
    exact congrArg some hbit
  let q : State := {e with stage := .returned,committed := true}
  have heq : run e 0 0 2 = q := by simp [run,step,e,q]
  have hrq : returnedRuntime q = some d := by
    rw [returned_code q (optionalRuntimeCodec (some d)) rfl htape,optionalRuntimeCodec.symm_apply_apply]
  have hoq : returnedOperation q = some op := by
    change some (operationCodec.symm a.operation) = _
    rw [hop,operationCodec.symm_apply_apply]
  let t := t0+ta+2
  refine ⟨t,q,?_,rfl,hrq,hoq,t0+ta,by dsimp [t]; omega,?_⟩
  · dsimp only [t]
    rw [run_add,run_add,ht0,hae,heq]
  · rw [run_add,ht0,hae]
    exact he


private theorem commit_after_render (p : State) (op : Operation) (d : Runtime)
    (hp : p.stage = .render) (ht : p.runtime.tape = word (optionalRuntimeCodec (some d)))
    (ho : p.operation = operationCodec op) (n : ℕ)
    (ha : (addressRun p.addressed n).control.pc = .returned) :
    ∃ t, ∃ q : State, run p 0 0 t = q ∧ q.stage = .returned ∧
      returnedRuntime q = some d ∧ returnedOperation q = some op := by
  obtain ⟨t,_,he⟩ := render_exit p n hp ha
  let e : State := {p with addressed := addressRun p.addressed n,stage := .emit}
  let q : State := {e with stage := .returned,committed := true}
  have heq : run e 0 0 2 = q := by simp [run,step,e,q]
  refine ⟨t+2,q,?_,rfl,?_,?_⟩
  · rw [run_add,he,heq]
  · rw [returned_code q (optionalRuntimeCodec (some d)) rfl ht,optionalRuntimeCodec.symm_apply_apply]
  · change some (operationCodec.symm p.operation) = _
    rw [ho,operationCodec.symm_apply_apply]

/-- The renderer query is still the preprepared read-zero row. This entry does
not assert that the live Read port has compiled the corresponding event row. -/
def sourceEntry (s : TransferSnapshot) (slot : Fin 6) (i : Fin frameWidth) : State :=
  {prepared s (.read 0) slot i with stage := .acquire}



private theorem acquisition_commit (s : TransferSnapshot) (x : Letter) (slot : Fin 6)
    (i : Fin frameWidth) (d : Runtime) (hd : runtimeStep s.base.retained.actual (.read x) = some d) :
    ∃ t, ∃ q : State,
      run (step (sourceEntry s slot i) x 0) 0 0 t = q ∧ q.stage = .returned ∧
      returnedRuntime q = some d ∧ returnedOperation q = some (.read x) := by
  let p := step (sourceEntry s slot i) x 0
  have hps : p.stage = .nativeKey := rfl
  have hpk : p.nativeKey = keyEntry (word (runtimeCodec s.base.retained.actual))
      (operationCodec (.read x)) := rfl
  obtain ⟨t,a,ha,has,hat,haa,hao,hac⟩ := native_render p s.base.retained.actual (.read x) d
    hps hpk rfl rfl rfl hd
  let c := context s (.read 0)
  obtain ⟨n,b,hb,hbp,_⟩ := (charged_address_execution c).2.2.2.2 slot i
  have haddr : a.addressed = addressEntry
      (literalInstallStep^[motorTime programWidth] (literalInstallStart c)) (frameKey c slot) i := haa
  have hap : (addressRun a.addressed n).control.pc = .returned := by rw [haddr,hb]; exact hbp
  obtain ⟨t',q,hq,hqs,hqr,hqo⟩ := commit_after_render a (.read x) d has hat hao n hap
  refine ⟨t+t',q,?_,hqs,hqr,hqo⟩
  rw [run_add,ha,hq]

/-- A finite deterministic return distance is external analysis of the complete
snapshot. No clock, stream index or rank is a stored instruction input. -/
def Returns (s : State) : Prop := ∃ t, (run s 0 0 t).stage = .returned

noncomputable def rank (s : State) : ℕ := by
  classical
  exact if h : Returns s then Nat.find h else 0

private theorem run_step (s : State) (n : ℕ) : run (step s 0 0) 0 0 n = run s 0 0 (n+1) := by
  simp only [run,Function.iterate_succ_apply]

private theorem returns_after (s : State) (h : Returns s) (n : ℕ) : Returns (run s 0 0 n) := by
  obtain ⟨t,ht⟩ := h
  by_cases hn : n ≤ t
  · refine ⟨t-n,?_⟩
    rw [← run_add,show n+(t-n) = t by omega]
    exact ht
  · have hn' : t ≤ n := by omega
    have hf : step (run s 0 0 t) 0 0 = run s 0 0 t := by simp [step,ht]
    refine ⟨0,?_⟩
    rw [show n = t+(n-t) by omega,run_add]
    have hi : run (run s 0 0 t) 0 0 (n-t) = run s 0 0 t :=
      Function.iterate_fixed (f := fun q => step q 0 0) hf (n-t)
    rw [hi]
    exact ht

private theorem rank_step (s : State) (h : Returns s) (hp : s.stage ≠ .returned) :
    rank (step s 0 0) < rank s := by
  have hz : 0 < Nat.find h := by
    by_contra hn
    have he : Nat.find h = 0 := by omega
    have hs := Nat.find_spec h
    rw [he] at hs
    exact hp hs
  have ht : (run (step s 0 0) 0 0 (Nat.find h-1)).stage = .returned := by
    rw [run_step,show Nat.find h-1+1 = Nat.find h by omega]
    exact Nat.find_spec h
  have hs : Returns (step s 0 0) := ⟨Nat.find h-1,ht⟩
  rw [rank,dif_pos hs,rank,dif_pos h]
  have := Nat.find_min' hs ht
  omega

private theorem no_fault (s : State) (h : Returns s) : s.stage ≠ .fault := by
  intro hp
  obtain ⟨t,ht⟩ := h
  have hf : step s 0 0 = s := by simp [step,hp]
  have hs : run s 0 0 t = s := Function.iterate_fixed hf t
  rw [hs,hp] at ht
  cases ht



namespace CurrentBank

private theorem tape_word {n : ℕ} (a : Fin n) :
    (fun i : Fin n => tapeBit a i.val) = word a := by
  funext i
  simp only [tapeBit,bitCode,word,List.getElem?_append,List.length_replicate,
    List.getElem?_replicate]
  split <;> simp_all <;> split <;> simp_all

private def rowMatrix {k n : ℕ} (table : Fin k → Fin n) (i : Fin (k*(k+n))) : Bool :=
  let p := (finProdFinEquiv (m := k) (n := k+n)).symm i
  Fin.append (word p.1) (word (table p.1)) p.2

private theorem row_serialization {k n : ℕ} (table : Fin k → Fin n) :
    (List.ofFn (fun r => bitCode r ++ bitCode (table r))).flatten =
      List.ofFn (rowMatrix table) := by
  conv_rhs => rw [List.ofFn_mul]
  congr 1
  congr 1
  funext r
  rw [← tape_list r,← tape_list (table r),tape_word,tape_word,← List.ofFn_fin_append]
  congr 1
  funext j
  unfold rowMatrix
  have hp : (finProdFinEquiv (m := k) (n := k+n)).symm
      ⟨r.val*(k+n)+j.val,by have := r.isLt; have := j.isLt; nlinarith⟩ = (r,j) := by
    apply (finProdFinEquiv (m := k) (n := k+n)).injective
    simp only [Equiv.apply_symm_apply]
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val]
    ring
  rw [hp]

private theorem dictionary_bit {k n : ℕ} (rows : Vector (Fin k × Fin n) k)
    (table : Fin k → Fin n) (hb : ∀ r, readRow rows r = (r,table r))
    (r : Fin k) (j : Fin (k+n)) :
    ((rows.toList.map (fun v => bitCode v.1 ++ bitCode v.2)).flatten)[r.val*(k+n)+j.val]?.getD false =
      Fin.append (word r) (word (table r)) j := by
  have hm : rows.toList.map (fun v => bitCode v.1 ++ bitCode v.2) =
      List.ofFn (fun r : Fin k => bitCode r ++ bitCode (table r)) := by
    rw [← List.ofFn_getElem_eq_map]
    simp only [Vector.length_toList]
    congr 1
    funext a
    simpa only [readRow,Vector.getElem_toList,Fin.coe_cast] using
      congrArg (fun v : Fin k × Fin n => bitCode v.1 ++ bitCode v.2) (hb a)
  rw [hm,row_serialization]
  have hn : r.val*(k+n)+j.val < k*(k+n) := by
    have := r.isLt
    have := j.isLt
    nlinarith
  rw [List.getElem?_ofFn]
  simp only [hn,↓reduceDIte,Option.getD_some,rowMatrix]
  have hp : (finProdFinEquiv (m := k) (n := k+n)).symm
      ⟨r.val*(k+n)+j.val,hn⟩ = (r,j) := by
    apply (finProdFinEquiv (m := k) (n := k+n)).injective
    simp only [Equiv.apply_symm_apply]
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val]
    ring
  rw [hp]

private theorem query_motion {k m : ℕ} (s : Key k m) :
    (keyStep s).query = s.query ∨
      ((keyStep s).query.val = s.query.val+1 ∧ s.query.val < k*m) := by
  unfold keyStep
  repeat' first | split | simp_all

private theorem build_key_projection (s : State) : (buildKey s).key = keyStep s.key := by
  unfold buildKey
  dsimp only
  repeat' first | split | rfl

private theorem build_key_bits (s : State)
    (hs : ∀ i, s.query i = decide (i.val < s.key.query.val)) :
    ∀ i, (buildKey s).query i = decide (i.val < (buildKey s).key.query.val) := by
  intro i
  rw [build_key_projection]
  obtain hsame | ⟨hsucc,hbound⟩ := query_motion s.key
  · unfold buildKey
    simp only [hsame]
    split <;> simp_all
  · unfold buildKey
    simp only [hbound,↓reduceDIte,hsucc,↓reduceIte]
    by_cases he : i = (⟨s.key.query.val,hbound⟩ : Fin (runtimeSize*4))
    · subst i
      simp [Function.update]
    · rw [Function.update_of_ne he,hs]
      have hn : i.val ≠ s.key.query.val := by intro h; exact he (Fin.ext h)
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega

private theorem build_key_run (s : State) (n : ℕ)
    (hs : ∀ i, s.query i = decide (i.val < s.key.query.val)) :
    (buildKey^[n] s).key = keyRun s.key n ∧
      ∀ i, (buildKey^[n] s).query i = decide (i.val < (keyRun s.key n).query.val) := by
  induction n with
  | zero => exact ⟨rfl,hs⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hk : (buildKey (buildKey^[n] s)).key = keyRun s.key (n+1) := by
      rw [build_key_projection,ih.1]
      exact (Function.iterate_succ_apply' keyStep n s.key).symm
    refine ⟨hk,?_⟩
    have h := build_key_bits (buildKey^[n] s) (by rw [ih.1]; exact ih.2)
    rw [hk] at h
    exact h

private theorem captured_key (s : State) (z : Runtime) (op : Operation)
    (hk : s.key = keyEntry (word (runtimeCodec z)) (operationCodec op))
    (hq : ∀ i, s.query i = false) :
    (buildKey^[keyTime (runtimeCodec z) (operationCodec op)] s).key.pc = 4 ∧
    ∀ i, (buildKey^[keyTime (runtimeCodec z) (operationCodec op)] s).query i =
      word (nativeKeyCodec (z,op)) i := by
  have hstart : ∀ i, s.query i = decide (i.val < s.key.query.val) := by
    rw [hk]
    simpa only [keyEntry,Fin.val_zero,not_lt_zero',decide_false] using hq
  have h := build_key_run s (keyTime (runtimeCodec z) (operationCodec op)) hstart
  have he := key_execution (runtimeCodec z) (operationCodec op)
  rw [hk] at h
  refine ⟨by rw [h.1]; exact he.1,?_⟩
  intro i
  rw [h.2 i,he.2]
  have hv : (nativeKeyCodec (z,op)).val = (operationCodec op).val+4*(runtimeCodec z).val := rfl
  simp only [word,hv]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

private theorem native_bit_correct (s : State)
    (hi : s.addressed.outer.installation.tape = programTape)
    (r : Fin (runtimeSize*4)) (j : Fin (runtimeSize*5+1)) :
    nativeBit s r j =
      if h : j.val < runtimeSize*4 then word r ⟨j.val,h⟩
      else word (nativeTable r) ⟨j.val-runtimeSize*4,by have := j.isLt; omega⟩ := by
  unfold nativeBit
  rw [hi]
  unfold programTape rawProgramTape
  have hb : 864+r.val*(runtimeSize*5+1)+j.val < B0 := by
    unfold B0 snapshotWidth residentWidth
    have := r.isLt
    have := j.isLt
    nlinarith
  simp only [Fin.addCases,Fin.cast_mk,hb,↓reduceDIte]
  change residentCode[864+r.val*(runtimeSize*5+1)+j.val]?.getD false = _
  have hn : r.val*(runtimeSize*5+1)+j.val < installedNative.code.length := by
    rw [installedNative.codeLength]
    have := r.isLt
    have := j.isLt
    nlinarith
  unfold residentCode
  rw [List.append_assoc,List.append_assoc,List.append_assoc]
  have hl : instructionCode.length = 48 := by simp [instructionCode,instructionGraph,bitCode]
  have hc : constantsCode.length = 816 := by simp [constantsCode,bit_code_length]
  rw [List.getElem?_append_right (by rw [hl]; omega),hl]
  rw [List.getElem?_append_right (by rw [hc]; omega),hc]
  have he : 864+r.val*(runtimeSize*5+1)+j.val-48-816 =
      r.val*(runtimeSize*5+1)+j.val := by omega
  rw [he,List.getElem?_append_left hn,installedNative.serialization]
  have ht : ∀ a, readRow installedNative.rows a = (a,nativeTable a) := by
    intro a
    have h := installedNative.binding a
    have hf : nativeTable a = nativeRowValue a := by
      simpa only [nativeTable,nativeDictionary] using congrArg Prod.snd h
    rw [hf]
    exact h
  have hw : runtimeSize*5+1 = runtimeSize*4+(runtimeSize+1) := by omega
  let j' : Fin (runtimeSize*4+(runtimeSize+1)) := ⟨j.val,by rw [← hw]; exact j.isLt⟩
  have hh := dictionary_bit installedNative.rows nativeTable ht r j'
  have he' : r.val*(runtimeSize*5+1)+j.val = r.val*(runtimeSize*4+(runtimeSize+1))+j'.val := by
    exact congrArg (fun v : ℕ => r.val*v+j.val) hw
  rw [he']
  rw [hh]
  by_cases hj : j.val < runtimeSize*4
  · have hj' : j' = Fin.castAdd (runtimeSize+1) (⟨j.val,hj⟩ : Fin (runtimeSize*4)) := Fin.ext rfl
    rw [hj',Fin.append_left]
    simp only [hj,↓reduceDIte]
  · have hb' : j.val-runtimeSize*4 < runtimeSize+1 := by have := j.isLt; omega
    have hj' : j' = Fin.natAdd (runtimeSize*4) (⟨j.val-runtimeSize*4,hb'⟩ : Fin (runtimeSize+1)) := by
      apply Fin.ext
      change j.val = runtimeSize*4+(j.val-runtimeSize*4)
      omega
    rw [hj',Fin.append_right]
    simp only [hj,↓reduceDIte]

private theorem field_rom (s : State) (z : Runtime)
    (hp : s.pre.tape = word (runtimeCodec z)) :
    fieldROM s = word (fieldsCodec z.fields) := by
  funext i
  rw [fieldROM,hp]
  apply Bool.eq_iff_iff.mpr
  simp only [word,decide_eq_true_eq]
  have hval : (runtimeCodec z).val = (monitorCodec z.monitor).val*4+(modeCodec z.mode).val+
      (fieldsCodec z.fields).val*(6023*4) := by
    change (finProdFinEquiv (fieldsCodec z.fields,
      finProdFinEquiv (monitorCodec z.monitor,modeCodec z.mode))).val = _
    simp only [finProdFinEquiv_apply_val]
    omega
  rw [hval]
  have hm := (monitorCodec z.monitor).isLt
  have hd := (modeCodec z.mode).isLt
  omega

private theorem scan_stable (s : State) :
    (scanStep s).actual = s.actual ∧ (scanStep s).role = s.role := by
  unfold scanStep
  dsimp only
  repeat' first | split | exact ⟨rfl,rfl⟩

private theorem key_stable (s : State) :
    (buildKey s).actual = s.actual ∧ (buildKey s).role = s.role := by
  unfold buildKey
  dsimp only
  repeat' first | split | exact ⟨rfl,rfl⟩

private theorem actual_step (s : State) (hr : s.role = true) :
    (step s).actual = s.actual := by
  unfold step
  simp only [hr,↓reduceIte]
  split <;> (repeat' first | rfl | split | exact (scan_stable s).1 | exact (key_stable s).1)

private theorem role_step (s : State) : (step s).role = s.role := by
  unfold step
  split <;> (repeat' first | rfl | split | exact (scan_stable s).2 | exact (key_stable s).2)

private theorem actual_cuts (s : State) (hr : s.role = true) (n : ℕ) :
    (run s n).actual = s.actual ∧ (run s n).role = true := by
  induction n with
  | zero => exact ⟨rfl,hr⟩
  | succ n ih =>
    rw [run,Function.iterate_succ_apply']
    exact ⟨(actual_step _ ih.2).trans ih.1,(role_step _).trans ih.2⟩

def opcodeTape (p : Fin 4) : Fin 12 → Bool := fun i =>
  (bitCode (instructionGraph[p.val]).1 ++ bitCode (instructionGraph[p.val]).2.1 ++
    bitCode (instructionGraph[p.val]).2.2)[i.val]?.getD false

private theorem instruction_bit (p : Fin 4) (i : Fin 12) :
    instructionCode[p.val*12+i.val]?.getD false = opcodeTape p i := by
  fin_cases p <;> fin_cases i <;> rfl

private theorem opcode_rom (s : State)
    (hi : s.addressed.outer.installation.tape = programTape) :
    opcodeROM s = opcodeTape s.native.pc := by
  funext i
  unfold opcodeROM
  rw [hi]
  unfold programTape rawProgramTape
  have hb : s.native.pc.val*12+i.val < B0 := by
    have := s.native.pc.isLt
    have := i.isLt
    unfold B0 snapshotWidth residentWidth runtimeSize
    omega
  simp only [Fin.addCases,Fin.cast_mk,hb,↓reduceDIte]
  change residentCode[s.native.pc.val*12+i.val]?.getD false = _
  unfold residentCode
  rw [List.append_assoc,List.append_assoc,List.append_assoc]
  have hl : instructionCode.length = 48 := by simp [instructionCode,instructionGraph,bitCode]
  rw [List.getElem?_append_left (by rw [hl]; have := s.native.pc.isLt; have := i.isLt; omega)]
  exact instruction_bit s.native.pc i

private theorem opcode_exit (s : State) (n : ℕ) (hs : s.phase = 13)
    (he : (motorRun (opcodeROM s) s.opcodes n).pc = .halt) :
    ∃ t ≤ n+1, run s t =
      {s with opcodes := motorRun (opcodeROM s) s.opcodes n,phase := 2} := by
  induction n generalizing s with
  | zero =>
    have hp : s.opcodes.pc = .halt := he
    refine ⟨1,by omega,?_⟩
    simp [run,step,hs,hp,motorRun]
  | succ n ih =>
    by_cases hp : s.opcodes.pc = .halt
    · have hfix : motorStep (opcodeROM s) s.opcodes = s.opcodes := by simp [motorStep,hp]
      refine ⟨1,by omega,?_⟩
      simp [run,step,hs,hp,motorRun,Function.iterate_fixed hfix]
    · let q : State := {s with opcodes := motorStep (opcodeROM s) s.opcodes}
      have hq : step s = q := by simp [q,step,hs,hp]
      have hrom : opcodeROM q = opcodeROM s := rfl
      have hqs : q.phase = 13 := hs
      have hqe : (motorRun (opcodeROM q) q.opcodes n).pc = .halt := by
        rw [motorRun,Function.iterate_succ_apply] at he
        exact he
      obtain ⟨t,ht,heq⟩ := ih q hqs hqe
      refine ⟨t+1,by omega,?_⟩
      rw [run,Function.iterate_succ_apply,hq]
      change run q t = _
      rw [heq]
      simp only [q,hrom,motorRun,Function.iterate_succ_apply]

private theorem opcode_decode (p : Fin 4) :
    decodeOpcode (opcodeTape p) 0 = (instructionGraph[p.val]).1 ∧
    decodeOpcode (opcodeTape p) 1 = (instructionGraph[p.val]).2.1 ∧
    decodeOpcode (opcodeTape p) 2 = (instructionGraph[p.val]).2.2 := by
  fin_cases p <;> decide

set_option maxHeartbeats 50000 in


private theorem native_scan_refines (s : State)
    (hi : s.addressed.outer.installation.tape = programTape)
    (hq : s.query = word s.native.query)
    (hop : s.opcodes.tape = opcodeTape s.native.pc) :
    (scanStep s).native = installedGraphStep nativeTable s.native := by
  have key_bit (r : Fin (runtimeSize*4)) (i : ℕ) (h : i < runtimeSize*4) :
      nativeBit s r ⟨i,by unfold runtimeSize at *; omega⟩ = tapeBit r i := by
    rw [native_bit_correct s hi]
    simp only [h,↓reduceDIte]
    exact (congrFun (tape_word r) ⟨i,h⟩).symm
  have payload_bit (r : Fin (runtimeSize*4)) (i : ℕ) (h : i < runtimeSize+1) :
      nativeBit s r ⟨runtimeSize*4+i,by unfold runtimeSize at *; omega⟩ = tapeBit (nativeTable r) i := by
    rw [native_bit_correct s hi]
    have hn : ¬ runtimeSize*4+i < runtimeSize*4 := by omega
    simp only [hn,↓reduceDIte,Nat.add_sub_cancel_left]
    exact (congrFun (tape_word (nativeTable r)) ⟨i,h⟩).symm
  have query_bit (i : ℕ) (h : i < runtimeSize*4) :
      s.query ⟨i,h⟩ = tapeBit s.native.query i := by
    rw [hq]
    exact (congrFun (tape_word s.native.query) ⟨i,h⟩).symm
  have hd := opcode_decode s.native.pc
  have hpall (p : Fin 4) : (instructionGraph[p.val]).1 = p := by
    fin_cases p <;> rfl
  have hp := hpall s.native.pc
  unfold installedGraphStep
  rw [hp]
  change (scanStep s).native = scannerStep nativeTable s.native
  unfold scanStep scannerStep
  simp only [hop,hd.1,hd.2.1,hd.2.2,hp]
  by_cases hr : s.native.row.val < runtimeSize*4
  · simp only [hr,↓reduceDIte]
    by_cases hpc : s.native.pc = 0
    · simp only [hpc,↓reduceIte]
      by_cases hc : s.native.cursor.val < runtimeSize*4
      · simp only [hc,↓reduceDIte,query_bit,key_bit]
      · simp only [hc,↓reduceDIte]
        split <;> rfl
    · simp only [hpc,↓reduceIte]
      by_cases hpc' : s.native.pc = 1
      · simp only [hpc',↓reduceIte]
        by_cases hc : s.native.cursor.val < runtimeSize+1
        · simp only [hc,↓reduceDIte,payload_bit]
        · simp only [hc,↓reduceDIte]
          rfl
      · simp only [hpc',↓reduceIte]
  · simp only [hr,↓reduceDIte]
    rfl

private theorem run_add (s : State) (m n : ℕ) :
    run s (m+n) = run (run s m) n := by
  simp only [run,Nat.add_comm m n,Function.iterate_add_apply]

private theorem pre_exit (s : State) (n : ℕ) (hs : s.phase = 0)
    (he : (motorRun (bank s) s.pre n).pc = .halt) :
    ∃ t ≤ n+1, run s t =
      {s with pre := motorRun (bank s) s.pre n,phase := 1,key := keyEntry (motorRun (bank s) s.pre n).tape s.operation} := by
  induction n generalizing s with
  | zero =>
    have hp : s.pre.pc = .halt := he
    refine ⟨1,by omega,?_⟩
    simp [run,step,hs,hp,motorRun]
  | succ n ih =>
    by_cases hp : s.pre.pc = .halt
    · have hfix : motorStep (bank s) s.pre = s.pre := by simp [motorStep,hp]
      refine ⟨1,by omega,?_⟩
      simp [run,step,hs,hp,motorRun,Function.iterate_fixed hfix]
    · let q : State := {s with pre := motorStep (bank s) s.pre}
      have hq : step s = q := by simp [q,step,hs,hp]
      have hbank : bank q = bank s := rfl
      have hqs : q.phase = 0 := hs
      have hqe : (motorRun (bank q) q.pre n).pc = .halt := by
        rw [motorRun,Function.iterate_succ_apply] at he
        exact he
      obtain ⟨t,ht,heq⟩ := ih q hqs hqe
      refine ⟨t+1,by omega,?_⟩
      rw [run,Function.iterate_succ_apply,hq]
      change run q t = _
      rw [heq]
      simp only [q,hbank,motorRun,Function.iterate_succ_apply]

private theorem build_phase (s : State) : (buildKey s).phase = s.phase := by
  unfold buildKey
  dsimp only
  repeat' first | split | rfl

private theorem build_exit (s : State) (n : ℕ) (hs : s.phase = 1)
    (he : (buildKey^[n] s).key.pc = 4)
    (hb : (buildKey^[n] s).key.query.val < runtimeSize*4) :
    ∃ t ≤ n+1, run s t =
      {(buildKey^[n] s) with phase := 13,native := scannerEntry ⟨(buildKey^[n] s).key.query.val,hb⟩} := by
  induction n generalizing s with
  | zero =>
    have hp : s.key.pc = 4 := he
    change s.key.query.val < runtimeSize*4 at hb
    refine ⟨1,by omega,?_⟩
    simp [run,step,hs,hp,hb]
  | succ n ih =>
    by_cases hp : s.key.pc = 4
    · have hkey : keyStep s.key = s.key := by simp [keyStep,hp]
      have hfix : buildKey s = s := by
        unfold buildKey
        simp only [hkey]
        split <;> simp
      have hi := Function.iterate_fixed hfix (n+1)
      have hb' : s.key.query.val < runtimeSize*4 := by simpa [hi] using hb
      refine ⟨1,by omega,?_⟩
      simp [run,step,hs,hp,hb',hi]
    · by_cases hf : s.key.pc = 5
      · have hkey : keyStep s.key = s.key := by simp [keyStep,hf]
        have hfix : buildKey s = s := by
          unfold buildKey
          simp only [hkey]
          split <;> simp
        have hi := Function.iterate_fixed hfix (n+1)
        have he' : s.key.pc = 4 := by simpa [hi] using he
        have : (5 : Fin 6) = 4 := hf.symm.trans he'
        cases this
      · let q := buildKey s
        have hq : step s = q := by simp [q,step,hs,hp,hf]
        have hqs : q.phase = 1 := (build_phase s).trans hs
        have hqe : (buildKey^[n] q).key.pc = 4 := by
          rw [Function.iterate_succ_apply] at he
          exact he
        have hqb : (buildKey^[n] q).key.query.val < runtimeSize*4 := by
          rw [Function.iterate_succ_apply] at hb
          exact hb
        obtain ⟨t,ht,heq⟩ := ih q hqs hqe hqb
        refine ⟨t+1,by omega,?_⟩
        rw [run,Function.iterate_succ_apply,hq]
        change run q t = _
        rw [heq]
        simp only [q,Function.iterate_succ_apply]

private theorem build_key_frame (s : State) (n : ℕ) :
    (buildKey^[n] s).actual = s.actual ∧
    (buildKey^[n] s).synthetic = s.synthetic ∧
    (buildKey^[n] s).operation = s.operation ∧
    (buildKey^[n] s).addressed = s.addressed ∧
    (buildKey^[n] s).opcodes = s.opcodes ∧ (buildKey^[n] s).role = s.role := by
  have stable (u : State) : (buildKey u).actual = u.actual ∧
      (buildKey u).synthetic = u.synthetic ∧ (buildKey u).operation = u.operation ∧
      (buildKey u).addressed = u.addressed ∧ (buildKey u).opcodes = u.opcodes ∧
      (buildKey u).role = u.role := by
    unfold buildKey
    dsimp only
    repeat' first | split | exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  induction n with
  | zero => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨(stable _).1.trans ih.1,(stable _).2.1.trans ih.2.1,
      (stable _).2.2.1.trans ih.2.2.1,(stable _).2.2.2.1.trans ih.2.2.2.1,
      (stable _).2.2.2.2.1.trans ih.2.2.2.2.1,
      (stable _).2.2.2.2.2.trans ih.2.2.2.2.2⟩

private def WorkSame (s q : State) : Prop :=
  q.pre = s.pre ∧ q.result = s.result ∧ q.fields = s.fields ∧
    q.slot = s.slot ∧ q.offset = s.offset

private theorem build_key_work (s : State) (n : ℕ) : WorkSame s (buildKey^[n] s) := by
  have stable (q : State) : WorkSame q (buildKey q) := by
    unfold WorkSame buildKey
    dsimp only
    repeat' first | split | exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  induction n with
  | zero => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨(stable _).1.trans ih.1,(stable _).2.1.trans ih.2.1,
      (stable _).2.2.1.trans ih.2.2.1,(stable _).2.2.2.1.trans ih.2.2.2.1,
      (stable _).2.2.2.2.trans ih.2.2.2.2⟩

private theorem key_query (p : State) (z : Runtime) (op : Operation)
    (hs : p.phase = 1)
    (hk : p.key = keyEntry (word (runtimeCodec z)) (operationCodec op))
    (hzero : ∀ i, p.query i = false) :
    ∃ t, ∃ q : State, run p t = q ∧ q.phase = 13 ∧
      q.query = word (nativeKeyCodec (z,op)) ∧
      q.native = scannerEntry (nativeKeyCodec (z,op)) ∧
      q.actual = p.actual ∧ q.synthetic = p.synthetic ∧
      q.operation = p.operation ∧ q.addressed = p.addressed ∧
      q.opcodes = p.opcodes ∧ q.role = p.role ∧ WorkSame p q := by
  let nk := keyTime (runtimeCodec z) (operationCodec op)
  have hd := captured_key p z op hk hzero
  have hrun := build_key_run p nk (by intro i; rw [hk]; simp [keyEntry,hzero])
  have hb : (buildKey^[nk] p).key.query.val < runtimeSize*4 := by
    rw [hrun.1,hk,(key_execution (runtimeCodec z) (operationCodec op)).2]
    have := (runtimeCodec z).isLt
    have := (operationCodec op).isLt
    omega
  obtain ⟨tk,_,htk⟩ := build_exit p nk hs hd.1 hb
  let q : State := {(buildKey^[nk] p) with
    phase := 13
    native := scannerEntry ⟨(buildKey^[nk] p).key.query.val,hb⟩}
  have hval : (⟨(buildKey^[nk] p).key.query.val,hb⟩ : Fin (runtimeSize*4)) =
      nativeKeyCodec (z,op) := by
    apply Fin.ext
    change (buildKey^[nk] p).key.query.val = (nativeKeyCodec (z,op)).val
    rw [hrun.1,hk,(key_execution (runtimeCodec z) (operationCodec op)).2]
    change (runtimeCodec z).val*4+(operationCodec op).val =
      (finProdFinEquiv (runtimeCodec z,operationCodec op)).val
    simp only [finProdFinEquiv_apply_val]
    omega
  have hf := build_key_frame p nk
  exact ⟨tk,q,htk,rfl,funext hd.2,congrArg scannerEntry hval,
    hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,hf.2.2.2.2.2,build_key_work p nk⟩

private theorem bank_query (image : TransferSnapshot) (a c : Fin runtimeSize → Bool)
    (role : Bool) (z : Runtime) (op : Operation)
    (hbank : (if role then c else a) = word (runtimeCodec z)) :
    ∃ t, ∃ q : State,
      run (entry image a c role (operationCodec op)) t = q ∧ q.phase = 13 ∧
      q.query = word (nativeKeyCodec (z,op)) ∧
      q.native = scannerEntry (nativeKeyCodec (z,op)) ∧
      q.actual = a ∧ q.synthetic = c ∧ q.operation = operationCodec op ∧
      q.addressed.outer = image ∧ q.opcodes = motorEntry 12 ∧ q.role = role ∧
      q.pre.tape = word (runtimeCodec z) ∧ q.result = motorEntry (runtimeSize+1) ∧
      q.fields = motorEntry 793800 ∧ q.slot = 0 ∧ q.offset = ⟨0,by unfold frameWidth; omega⟩ := by
  let s := entry image a c role (operationCodec op)
  let n := copyTime runtimeSize
  have hp := motor_return (word (runtimeCodec z))
  have hm : motorRun (bank s) s.pre n =
      motorRun (word (runtimeCodec z)) (motorEntry runtimeSize) n := by
    change motorRun (if role then c else a) (motorEntry runtimeSize) n = _
    rw [hbank]
  obtain ⟨tp,_,htp⟩ := pre_exit s n rfl (by rw [hm]; exact hp.1)
  let p : State := {s with
    pre := motorRun (bank s) s.pre n
    phase := 1
    key := keyEntry (motorRun (bank s) s.pre n).tape s.operation}
  have hpre : p.pre.tape = word (runtimeCodec z) := by
    change (motorRun (bank s) s.pre n).tape = _
    rw [hm]
    exact hp.2
  have hk : p.key = keyEntry (word (runtimeCodec z)) (operationCodec op) := by
    change keyEntry p.pre.tape s.operation = _
    rw [hpre]
    rfl
  obtain ⟨tk,q,htk,hphase,hquery,hnative,ha,hc,hop,haddr,hcode,hrole,hwork⟩ :=
    key_query p z op rfl hk (by intro i; rfl)
  refine ⟨tp+tk,q,?_,hphase,hquery,hnative,ha,hc,hop,?_,hcode,hrole,?_,
    hwork.2.1,hwork.2.2.1,hwork.2.2.2.1,hwork.2.2.2.2⟩
  · rw [run_add,htp,htk]
  · exact congrArg AddressState.outer haddr
  · rw [hwork.1]
    exact hpre


private def writeCheckpoint (s : State) (j : ℕ) (hj : j ≤ runtimeSize) : State :=
  {s with
    phase := 9
    bankProbe := ⟨j,by omega⟩
    actual := if s.role then s.actual else
      fun i => if i.val < j then s.result.tape ⟨i.val+1,by have := i.isLt; omega⟩ else s.actual i,
    synthetic := if s.role then
      fun i => if i.val < j then s.result.tape ⟨i.val+1,by have := i.isLt; omega⟩ else s.synthetic i
      else s.synthetic,
    bankLatch := if j = 0 then s.bankLatch else
      s.result.tape ⟨j,by omega⟩}



private theorem bank_read_step (s : State) (hs : s.phase = 9)
    (hp : s.bankProbe.val < runtimeSize) :
    step s = {s with
      phase := 10
      bankLatch := s.result.tape ⟨s.bankProbe.val+1,by omega⟩} := by
  simp [step,hs,hp]

private theorem bank_write_step (s : State) (hs : s.phase = 10)
    (hp : s.bankProbe.val < runtimeSize) :
    step s = if s.role then
      {s with
        phase := 9
        synthetic := Function.update s.synthetic ⟨s.bankProbe.val,hp⟩ s.bankLatch,
        bankProbe := ⟨s.bankProbe.val+1,by omega⟩}
    else {s with
      phase := 9
      actual := Function.update s.actual ⟨s.bankProbe.val,hp⟩ s.bankLatch,
      bankProbe := ⟨s.bankProbe.val+1,by omega⟩} := by
  simp [step,hs,hp]

private theorem write_cycle (s : State) (j : ℕ) (hj : j < runtimeSize) :
    run (writeCheckpoint s j (by omega)) 2 = writeCheckpoint s (j+1) (by omega) := by
  let p := writeCheckpoint s j (Nat.le_of_lt hj)
  have hread := bank_read_step p rfl (show p.bankProbe.val < runtimeSize from hj)
  let q : State := {p with
    phase := 10
    bankLatch := p.result.tape ⟨p.bankProbe.val+1,by change j+1 < runtimeSize+1; omega⟩}
  have hwrite := bank_write_step q rfl (show q.bankProbe.val < runtimeSize from hj)
  change step (step p) = writeCheckpoint s (j+1) (by omega)
  rw [hread,hwrite]
  dsimp only [q,p,writeCheckpoint]
  by_cases hr : s.role = true <;> simp only [hr,Bool.false_eq_true,↓reduceIte,
    Nat.add_eq_zero,Nat.one_ne_zero,and_false] <;>
    apply State.ext <;> try rfl
  · dsimp only
    funext i
    by_cases he : i.val = j
    · have hi : i = (⟨j,hj⟩ : Fin runtimeSize) := Fin.ext he
      subst i
      simp [Function.update_self,hj]
    · rw [Function.update_of_ne (by intro h; exact he (congrArg Fin.val h))]
      have hi : (i.val < j+1) ↔ (i.val < j) := by omega
      simp only [hi]
  · dsimp only
    funext i
    by_cases he : i.val = j
    · have hi : i = (⟨j,hj⟩ : Fin runtimeSize) := Fin.ext he
      subst i
      simp [Function.update_self,hj]
    · rw [Function.update_of_ne (by intro h; exact he (congrArg Fin.val h))]
      have hi : (i.val < j+1) ↔ (i.val < j) := by omega
      simp only [hi]

private theorem write_prefix (s : State) (j : ℕ) (hj : j ≤ runtimeSize) :
    run (writeCheckpoint s 0 (Nat.zero_le _)) (2*j) = writeCheckpoint s j hj := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2*(j+1) = 2*j+2 by omega,run_add,ih (by omega)]
    exact write_cycle s j (by omega)

private theorem result_drop (z : Runtime) :
    (fun i : Fin runtimeSize => word (optionalRuntimeCodec (some z))
      ⟨i.val+1,by have := i.isLt; omega⟩) = word (runtimeCodec z) := by
  funext i
  have h : (optionalRuntimeCodec (some z)).val = (runtimeCodec z).val+1 := by
    change ((finSuccEquiv runtimeSize).symm (some (runtimeCodec z))).val = _
    rw [finSuccEquiv_symm_some]
    rfl
  simp only [word,h,Fin.val_mk]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

private def WritePhase (s : State) : Prop :=
  s.phase = 9 ∨ s.phase = 10 ∨ s.phase = 11 ∨ s.phase = 12

private theorem write_phase_step (s : State) (hs : WritePhase s) : WritePhase (step s) := by
  rcases hs with hs | hs | hs | hs <;>
    simp [WritePhase,step,hs] <;> repeat' first | split | simp_all

private theorem write_quiet (s : State) (hs : WritePhase s) (n : ℕ) : trace s n = [] := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have hout : output s = none := by
      rcases hs with hs | hs | hs | hs <;> simp [output,hs]
    simp only [trace,hout,Option.toList_none,List.nil_append]
    exact ih (step s) (write_phase_step s hs)

private theorem write_complete (s : State) (d : Runtime)
    (hs : s.phase = 9) (hp : s.bankProbe = 0)
    (ht : s.result.tape = word (optionalRuntimeCodec (some d))) :
    ∃ t, ∃ q : State, run s t = q ∧ q.phase = 11 ∧
      q.actual = (if s.role then s.actual else word (runtimeCodec d)) ∧
      q.synthetic = (if s.role then word (runtimeCodec d) else s.synthetic) ∧
      q.operation = s.operation ∧ q.role = s.role ∧
      q.addressed.outer = s.addressed.outer ∧ trace s t = [] := by
  have he : writeCheckpoint s 0 (Nat.zero_le _) = s := by
    apply State.ext <;> simp [writeCheckpoint,hp,hs]
  let q := {writeCheckpoint s runtimeSize le_rfl with phase := (11 : Fin 14)}
  have hq : run s (2*runtimeSize+1) = q := by
    rw [run_add,← he,write_prefix s runtimeSize le_rfl]
    simp [run,step,writeCheckpoint,q]
  refine ⟨2*runtimeSize+1,q,hq,rfl,?_,?_,rfl,rfl,rfl,
    write_quiet s (Or.inl hs) _⟩
  · cases hr : s.role
    · funext i
      simp only [q,writeCheckpoint,hr,Bool.false_eq_true,↓reduceIte,i.isLt,ht]
      exact congrFun (result_drop d) i
    · simp [q,writeCheckpoint,hr]
  · cases hr : s.role
    · simp [q,writeCheckpoint,hr]
    · funext i
      simp only [q,writeCheckpoint,hr,↓reduceIte,i.isLt,ht]
      exact congrFun (result_drop d) i

private theorem write_return (s : State) (d : Runtime)
    (hs : s.phase = 9) (hp : s.bankProbe = 0)
    (ht : s.result.tape = word (optionalRuntimeCodec (some d))) :
    ∃ t, ∃ q : State, run s t = q ∧ q.phase = 11 ∧
      bank q = word (runtimeCodec d) ∧ q.operation = s.operation ∧
      (s.role = true → q.actual = s.actual) := by
  obtain ⟨t,q,hq,hphase,ha,hc,ho,hr,_,_⟩ := write_complete s d hs hp ht
  refine ⟨t,q,hq,hphase,?_,ho,?_⟩
  · unfold bank
    rw [hr,ha,hc]
    cases hrole : s.role <;> simp
  · intro hrole
    simpa only [hrole,↓reduceIte] using ha


/-- A proof invariant for the copied payload; the table occurs only in this
specification. The controller itself reads the installed physical tape. -/
private def PayloadGood (v : Scanner (runtimeSize*4) (runtimeSize+1))
    (bits : Fin (runtimeSize+1) → Bool) : Prop :=
  ∀ r : Fin (runtimeSize*4), v.row.val = r.val →
    (v.pc = 1 → v.cursor.val ≤ runtimeSize+1 ∧
      v.accumulator.val = min v.cursor.val (nativeTable r).val ∧
      ∀ i : Fin (runtimeSize+1), i.val < v.cursor.val →
        bits i = tapeBit (nativeTable r) i.val) ∧
    (v.pc = 2 → v.accumulator.val = (nativeTable r).val ∧
      bits = word (nativeTable r))

private def payloadNext (v : Scanner (runtimeSize*4) (runtimeSize+1))
    (bits : Fin (runtimeSize+1) → Bool) : Fin (runtimeSize+1) → Bool :=
  if hr : v.row.val < runtimeSize*4 then
    if v.pc = 1 then
      if hc : v.cursor.val < runtimeSize+1 then
        Function.update bits ⟨v.cursor.val,hc⟩
          (tapeBit (nativeTable ⟨v.row.val,hr⟩) v.cursor.val)
      else bits
    else bits
  else bits

private theorem payload_good_step (v : Scanner (runtimeSize*4) (runtimeSize+1))
    (bits : Fin (runtimeSize+1) → Bool) (hgood : PayloadGood v bits) :
    PayloadGood (scannerStep nativeTable v) (payloadNext v bits) := by
  by_cases hr : v.row.val < runtimeSize*4
  · by_cases hp0 : v.pc = 0
    · by_cases hc : v.cursor.val < runtimeSize*4
      · simpa [PayloadGood,scannerStep,payloadNext,hr,hp0,hc,instructionGraph]
      · by_cases he : v.equalFlag = true
        · simp only [scannerStep,payloadNext,hr,↓reduceDIte,hp0,↓reduceIte,hc,he,
            instructionGraph]
          intro r hrow
          constructor
          · intro _
            exact ⟨by simp,by simp,fun i hi => (by change i.val < 0 at hi; omega : False).elim⟩
          · intro h
            cases h
        · simp [PayloadGood,scannerStep,payloadNext,hr,hp0,hc,he,instructionGraph]
    · by_cases hp1 : v.pc = 1
      · let r : Fin (runtimeSize*4) := ⟨v.row.val,hr⟩
        obtain ⟨hcursor,hacc,hprefix⟩ := (hgood r rfl).1 hp1
        by_cases hc : v.cursor.val < runtimeSize+1
        · have ht : tapeBit (nativeTable r) v.cursor.val =
              decide (v.cursor.val < (nativeTable r).val) := by
            exact congrFun (tape_word (nativeTable r)) ⟨v.cursor.val,hc⟩
          simp only [scannerStep,payloadNext,hr,↓reduceDIte,hp0,hp1,↓reduceIte,hc]
          intro r' hrow
          have heq : r' = r := Fin.ext hrow.symm
          subst r'
          constructor
          · intro _
            refine ⟨?_,?_,?_⟩
            · change v.cursor.val+1 ≤ runtimeSize+1
              omega
            · change min (runtimeSize+1)
                (v.accumulator.val + if tapeBit (nativeTable r) v.cursor.val then 1 else 0) =
                min (v.cursor.val+1) (nativeTable r).val
              rw [hacc,ht]
              simp only [decide_eq_true_eq]
              split <;> omega
            · intro i hi
              change i.val < v.cursor.val+1 at hi
              change Function.update bits ⟨v.cursor.val,hc⟩
                (tapeBit (nativeTable r) v.cursor.val) i = tapeBit (nativeTable r) i.val
              by_cases he : i = (⟨v.cursor.val,hc⟩ : Fin (runtimeSize+1))
              · subst i
                exact Function.update_self _ _ _
              · rw [Function.update_of_ne he]
                apply hprefix
                have hn : i.val ≠ v.cursor.val := by intro h; exact he (Fin.ext h)
                omega
          · intro h
            cases h
        · have he : v.cursor.val = runtimeSize+1 := by omega
          have ha : v.accumulator.val = (nativeTable r).val := by
            rw [hacc,he,Nat.min_eq_right (Nat.le_of_lt (nativeTable r).isLt)]
          have hb : v.accumulator.val < runtimeSize+1 := by rw [ha]; exact (nativeTable r).isLt
          have hpayload : bits = word (nativeTable r) := by
            funext i
            exact (hprefix i (by rw [he]; exact i.isLt)).trans
              (congrFun (tape_word (nativeTable r)) i)
          simp only [scannerStep,payloadNext,hr,↓reduceDIte,hp0,hp1,↓reduceIte,hc,hb,
            instructionGraph]
          intro r' hrow
          have heq : r' = r := Fin.ext hrow.symm
          subst r'
          constructor
          · intro h
            cases h
          · intro _
            exact ⟨ha,hpayload⟩
      · simpa only [scannerStep,payloadNext,hr,↓reduceDIte,hp0,hp1,↓reduceIte]
          using hgood
  · simp [PayloadGood,scannerStep,payloadNext,hr,instructionGraph]

private theorem graph_query (v : Scanner (runtimeSize*4) (runtimeSize+1)) :
    (installedGraphStep nativeTable v).query = v.query := by
  unfold installedGraphStep scannerStep
  dsimp only
  repeat' first | rfl | split

private theorem installed_payload_step (s : State)
    (hi : s.addressed.outer.installation.tape = programTape)
    (hop : s.opcodes.tape = opcodeTape s.native.pc) :
    (scanStep s).payload = payloadNext s.native s.payload := by
  have hd := opcode_decode s.native.pc
  have hp (p : Fin 4) : (instructionGraph[p.val]).1 = p := by fin_cases p <;> rfl
  unfold scanStep payloadNext
  simp only [hop,hd.1,hd.2.1,hd.2.2,hp]
  by_cases hr : s.native.row.val < runtimeSize*4
  · simp only [hr,↓reduceDIte]
    by_cases h0 : s.native.pc = 0
    · have h1 : ¬ s.native.pc = 1 := by rw [h0]; decide
      simp only [h0,h1,↓reduceIte]
      repeat' first | rfl | split | contradiction
    · simp only [h0,↓reduceIte]
      by_cases h1 : s.native.pc = 1
      · simp only [h1,↓reduceIte]
        by_cases hc : s.native.cursor.val < runtimeSize+1
        · simp only [hc,↓reduceDIte]
          congr 1
          rw [native_bit_correct s hi]
          have hn : ¬ runtimeSize*4+s.native.cursor.val < runtimeSize*4 := by omega
          simp only [hn,↓reduceDIte,Nat.add_sub_cancel_left]
          exact (congrFun (tape_word (nativeTable ⟨s.native.row.val,hr⟩))
            ⟨s.native.cursor.val,hc⟩).symm
        · simp only [hc,↓reduceDIte]
      · simp only [h1,↓reduceIte]
  · simp only [hr,↓reduceDIte]

private def NativeFrame (s q : State) : Prop :=
  q = {s with native := q.native,payload := q.payload,phase := q.phase,opcodes := q.opcodes}

private theorem native_frame_trans {s p q : State}
    (hsp : NativeFrame s p) (hpq : NativeFrame p q) : NativeFrame s q := by
  unfold NativeFrame at *
  rw [hpq,hsp]

private theorem scan_frame (s : State) : NativeFrame s (scanStep s) := by
  unfold NativeFrame scanStep
  dsimp only
  repeat' first | rfl | split

private theorem opcode_frame (s : State) (hs : s.phase = 13)
    (hp : s.opcodes = motorEntry 12)
    (hi : s.addressed.outer.installation.tape = programTape) :
    ∃ t, ∃ q : State, run s t = q ∧ q.phase = 2 ∧
      q.native = s.native ∧ q.payload = s.payload ∧
      q.opcodes.tape = opcodeTape s.native.pc ∧ NativeFrame s q := by
  have hrom := opcode_rom s hi
  have hm := motor_return (opcodeTape s.native.pc)
  have he : (motorRun (opcodeROM s) s.opcodes (copyTime 12)).pc = .halt := by
    rw [hp,hrom]
    exact hm.1
  obtain ⟨t,_,ht⟩ := opcode_exit s (copyTime 12) hs he
  let q : State := {s with
    opcodes := motorRun (opcodeROM s) s.opcodes (copyTime 12)
    phase := 2}
  refine ⟨t,q,ht,rfl,rfl,rfl,?_,rfl⟩
  change (motorRun (opcodeROM s) s.opcodes (copyTime 12)).tape = opcodeTape s.native.pc
  rw [hp,hrom]
  exact hm.2

private theorem scan_cycle (s : State) (hs : s.phase = 2)
    (hi : s.addressed.outer.installation.tape = programTape)
    (hq : s.query = word s.native.query)
    (hop : s.opcodes.tape = opcodeTape s.native.pc)
    (hg : PayloadGood s.native s.payload) (h2 : s.native.pc ≠ 2) (h3 : s.native.pc ≠ 3) :
    ∃ t, ∃ q : State, run s t = q ∧ q.phase = 2 ∧
      q.native = installedGraphStep nativeTable s.native ∧
      PayloadGood q.native q.payload ∧ NativeFrame s q ∧
      q.opcodes.tape = opcodeTape q.native.pc := by
  let p : State := {scanStep s with phase := 13,opcodes := motorEntry 12}
  have hs1 : step s = p := by simp [step,hs,h2,h3,p]
  have hsp : NativeFrame s p := native_frame_trans (scan_frame s) rfl
  have hpimage : p.addressed.outer.installation.tape = programTape :=
    (congrArg (fun v => v.addressed.outer.installation.tape) hsp).trans hi
  obtain ⟨t,q,ht,hphase,hnative,hpayload,htape,hpq⟩ := opcode_frame p rfl rfl hpimage
  have hn : q.native = installedGraphStep nativeTable s.native :=
    hnative.trans (native_scan_refines s hi hq hop)
  have hgood : PayloadGood q.native q.payload := by
    rw [hn,hpayload]
    change PayloadGood (installedGraphStep nativeTable s.native) (scanStep s).payload
    have hp (p : Fin 4) : (instructionGraph[p.val]).1 = p := by fin_cases p <;> rfl
    rw [installedGraphStep,hp,installed_payload_step s hi hop]
    exact payload_good_step s.native s.payload hg
  refine ⟨1+t,q,?_,hphase,hn,hgood,native_frame_trans hsp hpq,?_⟩
  · rw [run_add]
    change run (step s) t = q
    rw [hs1,ht]
  · rw [hnative]
    exact htape

private theorem scan_exit (s : State) (n : ℕ) (hs : s.phase = 2)
    (hi : s.addressed.outer.installation.tape = programTape)
    (hq : s.query = word s.native.query)
    (hop : s.opcodes.tape = opcodeTape s.native.pc)
    (hg : PayloadGood s.native s.payload) (hsa : ScannerSafe s.native)
    (he : ((installedGraphStep nativeTable)^[n] s.native).pc = 2) :
    ∃ t, ∃ q : State, run s t = q ∧ q.phase = 3 ∧
      q.native = (installedGraphStep nativeTable)^[n] s.native ∧
      PayloadGood q.native q.payload ∧ NativeFrame s q ∧ ScannerSafe q.native := by
  induction n generalizing s with
  | zero =>
    have hp : s.native.pc = 2 := he
    refine ⟨1,{s with phase := 3},?_,rfl,rfl,hg,rfl,hsa⟩
    simp [run,step,hs,hp]
  | succ n ih =>
    by_cases h2 : s.native.pc = 2
    · have hf := graph_terminal nativeTable s.native (Or.inl ⟨h2,hsa h2⟩)
      have hfix := Function.iterate_fixed hf (n+1)
      refine ⟨1,{s with phase := 3},?_,rfl,hfix.symm,hg,rfl,hsa⟩
      simp [run,step,hs,h2]
    · by_cases h3 : s.native.pc = 3
      · have hf := graph_terminal nativeTable s.native (Or.inr h3)
        rw [Function.iterate_fixed hf] at he
        have : (3 : Fin 4) = 2 := h3.symm.trans he
        cases this
      · obtain ⟨tc,c,hc,hphase,hnative,hgood,hframe,hopcode⟩ :=
          scan_cycle s hs hi hq hop hg h2 h3
        have himage : c.addressed.outer.installation.tape = programTape :=
          (congrArg (fun v => v.addressed.outer.installation.tape) hframe).trans hi
        have hquery : c.query = word c.native.query := by
          have hqframe : c.query = s.query := by
            have hf := congrArg State.query (show c = _ from hframe)
            exact hf
          rw [hqframe,hnative,graph_query]
          exact hq
        have hsafe : ScannerSafe c.native := by
          rw [hnative]
          exact scanner_safe_step nativeTable s.native hsa
        have hend : ((installedGraphStep nativeTable)^[n] c.native).pc = 2 := by
          rw [hnative]
          rw [Function.iterate_succ_apply] at he
          exact he
        obtain ⟨tr,r,hr,hret,hrnative,hrgood,hrframe,hrsafe⟩ :=
          ih c hphase himage hquery hopcode hgood hsafe hend
        refine ⟨tc+tr,r,?_,hret,?_,hrgood,native_frame_trans hframe hrframe,hrsafe⟩
        · rw [run_add,hc,hr]
        · rw [hrnative,hnative]
          exact (Function.iterate_succ_apply _ n s.native).symm


private theorem result_exit (s : State) (n : ℕ) (hs : s.phase = 3)
    (hb : s.payload 0 = true)
    (he : (motorRun s.payload s.result n).pc = .halt) :
    ∃ t, run s t = {s with result := motorRun s.payload s.result n,phase := 4} := by
  induction n generalizing s with
  | zero =>
    have hp : s.result.pc = .halt := he
    refine ⟨1,?_⟩
    simp [run,step,hs,hb,hp,motorRun]
  | succ n ih =>
    by_cases hp : s.result.pc = .halt
    · have hf : motorStep s.payload s.result = s.result := by simp [motorStep,hp]
      refine ⟨1,?_⟩
      simp [run,step,hs,hb,hp,motorRun,Function.iterate_fixed hf]
    · let q : State := {s with result := motorStep s.payload s.result}
      have hq : step s = q := by simp [q,step,hs,hb,hp]
      have heq : (motorRun q.payload q.result n).pc = .halt := by
        rw [motorRun,Function.iterate_succ_apply] at he
        exact he
      obtain ⟨t,ht⟩ := ih q hs hb heq
      refine ⟨t+1,?_⟩
      rw [run,Function.iterate_succ_apply,hq]
      change run q t = _
      rw [ht]
      simp only [q,motorRun,Function.iterate_succ_apply]

private theorem fields_exit (s : State) (n : ℕ) (hs : s.phase = 4)
    (he : (motorRun (fieldROM s) s.fields n).pc = .halt) :
    ∃ t, run s t = {s with
      fields := motorRun (fieldROM s) s.fields n
      phase := 5
      row := keyEntry (motorRun (fieldROM s) s.fields n).tape
        ⟨s.operation.val*6+s.slot.val,by
          have := s.operation.isLt; have := s.slot.isLt; omega⟩} := by
  induction n generalizing s with
  | zero =>
    have hp : s.fields.pc = .halt := he
    refine ⟨1,?_⟩
    simp [run,step,hs,hp,motorRun]
  | succ n ih =>
    by_cases hp : s.fields.pc = .halt
    · have hf : motorStep (fieldROM s) s.fields = s.fields := by simp [motorStep,hp]
      refine ⟨1,?_⟩
      simp [run,step,hs,hp,motorRun,Function.iterate_fixed hf]
    · let q : State := {s with fields := motorStep (fieldROM s) s.fields}
      have hq : step s = q := by simp [q,step,hs,hp]
      have hrom : fieldROM q = fieldROM s := rfl
      have heq : (motorRun (fieldROM q) q.fields n).pc = .halt := by
        rw [motorRun,Function.iterate_succ_apply] at he
        exact he
      obtain ⟨t,ht⟩ := ih q hs heq
      refine ⟨t+1,?_⟩
      rw [run,Function.iterate_succ_apply,hq]
      change run q t = _
      rw [ht]
      simp only [q,hrom,motorRun,Function.iterate_succ_apply]


private def PreparedFrame (s q : State) : Prop :=
  q = {s with result := q.result,fields := q.fields,row := q.row,phase := q.phase}

private theorem prepare_event (r : State) (z d : Runtime)
    (hrphase : r.phase = 3)
    (hresult : r.payload = word (optionalRuntimeCodec (some d)))
    (hrpre : r.pre.tape = word (runtimeCodec z))
    (hrres : r.result = motorEntry (runtimeSize+1))
    (hrfields : r.fields = motorEntry 793800) :
    ∃ t, ∃ f : State, run r t = f ∧ f.phase = 5 ∧
      f.result.tape = word (optionalRuntimeCodec (some d)) ∧
      f.fields.tape = word (fieldsCodec z.fields) ∧
      f.row = keyEntry (word (fieldsCodec z.fields))
        ⟨r.operation.val*6+r.slot.val,by
          have := r.operation.isLt; have := r.slot.isLt; omega⟩ ∧ PreparedFrame r f := by
  have hrbit : r.payload ⟨0,by omega⟩ = true := by
    rw [hresult]
    simp [word,optionalRuntimeCodec,finSuccEquiv]
  have hm := motor_return (word (optionalRuntimeCodec (some d)))
  have hrmotor : motorRun r.payload r.result (copyTime (runtimeSize+1)) =
      motorRun (word (optionalRuntimeCodec (some d)))
        (motorEntry (runtimeSize+1)) (copyTime (runtimeSize+1)) := by rw [hresult,hrres]
  obtain ⟨tr,htr⟩ := result_exit r (copyTime (runtimeSize+1))
    hrphase hrbit (by rw [hrmotor]; exact hm.1)
  let u : State := {r with
    result := motorRun r.payload r.result (copyTime (runtimeSize+1)),phase := 4}
  have hures : u.result.tape = word (optionalRuntimeCodec (some d)) := by
    change (motorRun r.payload r.result (copyTime (runtimeSize+1))).tape = _
    rw [hrmotor]
    exact hm.2
  have hrom : fieldROM u =
      word (fieldsCodec z.fields) := field_rom u z hrpre
  have hmf := motor_return (word (fieldsCodec z.fields))
  have hfmotor : motorRun (fieldROM u) u.fields (copyTime 793800) =
      motorRun (word (fieldsCodec z.fields)) (motorEntry 793800)
        (copyTime 793800) := by rw [hrom]; change motorRun _ r.fields _ = _; rw [hrfields]
  obtain ⟨tf,htf⟩ := fields_exit u (copyTime 793800) rfl
    (by rw [hfmotor]; exact hmf.1)
  let f : State := {u with
    fields := motorRun (fieldROM u) u.fields (copyTime 793800)
    phase := 5
    row := keyEntry
      (motorRun (fieldROM u) u.fields (copyTime 793800)).tape
      ⟨u.operation.val*6+u.slot.val,by have := u.operation.isLt; have := u.slot.isLt; omega⟩}
  have hffields : f.fields.tape = word (fieldsCodec z.fields) := by
    change (motorRun (fieldROM u) u.fields (copyTime 793800)).tape = _
    rw [hfmotor]
    exact hmf.2
  refine ⟨tr+tf,f,?_,rfl,hures,hffields,?_,rfl⟩
  · rw [run_add,htr,htf]
  · change keyEntry f.fields.tape _ = _
    rw [hffields]


private theorem trace_add (s : State) (m n : ℕ) :
    trace s (m+n) = trace s m ++ trace (run s m) n := by
  induction m generalizing s with
  | zero => simp [trace,run]
  | succ m ih =>
    simp only [Nat.succ_add,trace,ih,run,Function.iterate_succ_apply,
      List.append_assoc]

private theorem row_exit (s : State) (n : ℕ) (hs : s.phase = 5)
    (he : (keyRun s.row n).pc = 4)
    (hb : (keyRun s.row n).query.val < frameKeyWidth) :
    ∃ t, run s t = {s with
      row := keyRun s.row n
      phase := 6
      addressed := addressEntry s.addressed.outer
        ⟨(keyRun s.row n).query.val,hb⟩ s.offset} ∧ trace s t = [] := by
  induction n generalizing s with
  | zero =>
    have hp : s.row.pc = 4 := he
    change s.row.query.val < frameKeyWidth at hb
    refine ⟨1,?_,?_⟩
    · simp [run,step,hs,hp,hb,keyRun]
    · simp [trace,output,hs]
  | succ n ih =>
    by_cases hp : s.row.pc = 4
    · have hf : keyStep s.row = s.row := by simp [keyStep,hp]
      have hfix := Function.iterate_fixed hf (n+1)
      have hb' : s.row.query.val < frameKeyWidth := by simpa [keyRun,hfix] using hb
      refine ⟨1,?_,?_⟩
      · simp [run,step,hs,hp,hb',keyRun,hfix]
      · simp [trace,output,hs]
    · by_cases hf : s.row.pc = 5
      · have hfix : keyStep s.row = s.row := by simp [keyStep,hf]
        have hx : s.row.pc = 4 := by simpa [keyRun,Function.iterate_fixed hfix] using he
        have : (5 : Fin 6) = 4 := hf.symm.trans hx
        cases this
      · let q : State := {s with row := keyStep s.row}
        have hq : step s = q := by simp [step,hs,hp,hf,q]
        have heq : (keyRun q.row n).pc = 4 := by
          rw [keyRun,Function.iterate_succ_apply] at he
          exact he
        have hbq : (keyRun q.row n).query.val < frameKeyWidth := by
          rw [keyRun,Function.iterate_succ_apply] at hb
          exact hb
        obtain ⟨t,ht,htt⟩ := ih q hs heq hbq
        refine ⟨t+1,?_,?_⟩
        · rw [run,Function.iterate_succ_apply,hq]
          change run q t = _
          rw [ht]
          simp only [q,keyRun,Function.iterate_succ_apply]
        · simp [trace,output,hs,hq,htt]

private theorem address_exit (s : State) (n : ℕ) (hs : s.phase = 6)
    (he : (addressRun s.addressed n).control.pc = .returned) :
    ∃ t, run s t = {s with addressed := addressRun s.addressed n,phase := 7} ∧ trace s t = [] := by
  induction n generalizing s with
  | zero =>
    have hp : s.addressed.control.pc = .returned := he
    refine ⟨1,?_,?_⟩
    · simp [run,step,hs,hp,addressRun]
    · simp [trace,output,hs]
  | succ n ih =>
    by_cases hp : s.addressed.control.pc = .returned
    · have hf : addressStep s.addressed = s.addressed := by simp [addressStep,hp]
      refine ⟨1,?_,?_⟩
      · simp [run,step,hs,hp,addressRun,Function.iterate_fixed hf]
      · simp [trace,output,hs]
    · by_cases hf : s.addressed.control.pc = .fault
      · have hfix : addressStep s.addressed = s.addressed := by simp [addressStep,hf]
        have hi := Function.iterate_fixed hfix (n+1)
        change (addressStep^[n+1] s.addressed).control.pc = .returned at he
        rw [hi] at he
        have : AddressPC.fault = .returned := hf.symm.trans he
        cases this
      · let q : State := {s with addressed := addressStep s.addressed}
        have hq : step s = q := by simp [step,hs,hp,hf,q]
        have heq : (addressRun q.addressed n).control.pc = .returned := by
          rw [addressRun,Function.iterate_succ_apply] at he
          exact he
        obtain ⟨t,ht,htt⟩ := ih q hs heq
        refine ⟨t+1,?_,?_⟩
        · rw [run,Function.iterate_succ_apply,hq]
          change run q t = _
          rw [ht]
          simp only [q,addressRun,Function.iterate_succ_apply]
        · simp [trace,output,hs,hq,htt]

private def EmissionFrame (s q : State) : Prop :=
  q = {s with row := q.row,addressed := q.addressed,phase := q.phase}

private theorem row_emit (s : State) (f : FiniteFields) (op : Operation)
    (hs : s.phase = 5) (ho : s.operation = operationCodec op)
    (hi : s.addressed.outer.installation.tape = programTape)
    (hr : s.row = keyEntry (word (fieldsCodec f))
      ⟨s.operation.val*6+s.slot.val,by have := s.operation.isLt; have := s.slot.isLt; omega⟩) :
    ∃ t, ∃ q : State, run s t = q ∧ q.phase = 7 ∧
      output q = some (frameTape (eventROM f op s.slot) s.offset) ∧
      q.row.query.val = (fieldsCodec f).val*24 +
        (s.operation.val*6+s.slot.val) ∧
      EmissionFrame s q ∧ q.addressed.outer = s.addressed.outer ∧ trace s t = [] := by
  let b : Fin 24 := ⟨s.operation.val*6+s.slot.val,by
    have := s.operation.isLt; have := s.slot.isLt; omega⟩
  let n := keyTime (fieldsCodec f) b
  have hk := key_execution (fieldsCodec f) b
  have hpc : (keyRun s.row n).pc = 4 := by rw [hr]; exact hk.1
  have hv : (keyRun s.row n).query.val = (fieldsCodec f).val*24+b.val := by
    rw [hr]; exact hk.2
  have hb : (keyRun s.row n).query.val < frameKeyWidth := by
    rw [hv]
    have := (fieldsCodec f).isLt
    have := b.isLt
    unfold frameKeyWidth
    omega
  obtain ⟨tr,htr,httr⟩ := row_exit s n hs hpc hb
  let p : State := {s with
    row := keyRun s.row n
    phase := 6
    addressed := addressEntry s.addressed.outer ⟨(keyRun s.row n).query.val,hb⟩ s.offset}
  obtain ⟨ta,a,ha,hap,hao,hprobe,hal,_⟩ := address_execution s.addressed.outer
    ⟨(keyRun s.row n).query.val,hb⟩ s.offset
  have hpa : (addressRun p.addressed ta).control.pc = .returned := by rw [ha]; exact hap
  obtain ⟨te,hte,htte⟩ := address_exit p ta rfl hpa
  let q : State := {p with addressed := addressRun p.addressed ta,phase := 7}
  let model : TransferSnapshot := {s.addressed.outer with
    base := {s.addressed.outer.base with
      retained := {s.addressed.outer.base.retained with
        pre := {s.addressed.outer.base.retained.pre with fields := f},operation := op}}}
  have hkey : (⟨(keyRun s.row n).query.val,hb⟩ : Fin frameKeyWidth) = frameKey model s.slot := by
    apply Fin.ext
    rw [hv]
    change (fieldsCodec f).val*24+(s.operation.val*6+s.slot.val) =
      (finProdFinEquiv (fieldsCodec f,finProdFinEquiv (operationCodec op,s.slot))).val
    rw [ho]
    simp only [finProdFinEquiv_apply_val]
    omega
  have hbit : a.control.latch = frameTape (eventROM f op s.slot) s.offset := by
    rw [hal,hi,hkey]
    change programTape (addressIndex (frameKey model s.slot) s.offset) = _
    rw [address_frame_index]
    exact congrFun (program_frame model.base s.slot) s.offset
  have hrowquery : q.row.query.val = (fieldsCodec f).val*24 +
      (s.operation.val*6+s.slot.val) := by
    change (keyRun s.row n).query.val = _
    exact hv
  refine ⟨tr+te,q,?_,rfl,?_,hrowquery,rfl,?_,?_⟩
  · rw [run_add,htr,hte]
  · change some (addressRun p.addressed ta).control.latch = _
    rw [ha,hbit]
  · change (addressRun p.addressed ta).outer = s.addressed.outer
    rw [ha,hao]
  · rw [trace_add,htr,httr,htte]
    rfl

/-- The working frame may change only the renderer's finite controls. -/
private def RenderFrame (s q : State) : Prop :=
  q = {s with
    row := q.row,addressed := q.addressed,phase := q.phase,offset := q.offset,slot := q.slot,bankProbe := q.bankProbe}

private theorem render_frame_trans {s p q : State}
    (hsp : RenderFrame s p) (hpq : RenderFrame p q) : RenderFrame s q := by
  unfold RenderFrame at *
  rw [hpq,hsp]

private theorem offset_emit (s : State) (f : FiniteFields) (op : Operation)
    (hs : s.phase = 7) (ho : s.operation = operationCodec op)
    (hi : s.addressed.outer.installation.tape = programTape)
    (hrow : s.row.query.val = (fieldsCodec f).val*24+
      (s.operation.val*6+s.slot.val))
    (hoff : s.offset.val+1 < frameWidth) :
    ∃ t, ∃ q : State, run s t = q ∧ q.phase = 7 ∧
      q.offset.val = s.offset.val+1 ∧ q.slot = s.slot ∧
      output q = some (frameTape (eventROM f op s.slot)
        ⟨s.offset.val+1,hoff⟩) ∧
      q.row = s.row ∧ RenderFrame s q ∧
      q.addressed.outer = s.addressed.outer ∧
      trace s t = [s.addressed.control.latch] := by
  have hq : s.row.query.val < frameKeyWidth := by
    rw [hrow]
    have hf := (fieldsCodec f).isLt
    have ho' := s.operation.isLt
    have hs' := s.slot.isLt
    unfold frameKeyWidth
    omega
  let next : Fin frameWidth := ⟨s.offset.val+1,hoff⟩
  let p : State := {s with
    phase := 6,offset := next,addressed := addressEntry s.addressed.outer ⟨s.row.query.val,hq⟩ next}
  have hsp : run s 2 = p := by
    simp [run,Function.iterate_succ_apply',step,hs,p,next,hq,hoff]
  obtain ⟨ta,a,ha,hap,hao,_,hal,_⟩ := address_execution s.addressed.outer
    ⟨s.row.query.val,hq⟩ next
  have hpa : (addressRun p.addressed ta).control.pc = .returned := by
    change (addressRun (addressEntry s.addressed.outer ⟨s.row.query.val,hq⟩ next) ta).control.pc = _
    rw [ha]
    exact hap
  obtain ⟨te,he,htte⟩ := address_exit p ta rfl hpa
  let q : State := {p with addressed := addressRun p.addressed ta,phase := 7}
  let model : TransferSnapshot := {s.addressed.outer with
    base := {s.addressed.outer.base with
      retained := {s.addressed.outer.base.retained with
        pre := {s.addressed.outer.base.retained.pre with fields := f},operation := op}}}
  have hkey : (⟨s.row.query.val,hq⟩ : Fin frameKeyWidth) = frameKey model s.slot := by
    apply Fin.ext
    rw [hrow]
    change (fieldsCodec f).val*24+(s.operation.val*6+s.slot.val) =
      (finProdFinEquiv (fieldsCodec f,
        finProdFinEquiv (operationCodec op,s.slot))).val
    rw [ho]
    simp only [finProdFinEquiv_apply_val]
    omega
  have hbit : a.control.latch = frameTape (eventROM f op s.slot) next := by
    rw [hal,hi,hkey]
    change programTape (addressIndex (frameKey model s.slot) next) = _
    rw [address_frame_index]
    exact congrFun (program_frame model.base s.slot) next
  refine ⟨2+te,q,?_,rfl,rfl,rfl,?_,rfl,rfl,?_,?_⟩
  · rw [run_add,hsp,he]
  · change some (addressRun p.addressed ta).control.latch = _
    rw [ha,hbit]
  · change (addressRun p.addressed ta).outer = s.addressed.outer
    rw [ha,hao]
  · rw [trace_add,hsp,htte,List.append_nil]
    simp [trace,output,step,hs]

private def bitsFrom {w : ℕ} (rom : Fin w → Bool) (j n : ℕ)
    (h : j+n ≤ w) : List Bool :=
  List.ofFn (fun i : Fin n => rom ⟨j+i.val,by have := i.isLt; omega⟩)

private theorem bits_from_succ {w : ℕ} (rom : Fin w → Bool) (j n : ℕ)
    (h : j+(n+1) ≤ w) :
    bitsFrom rom j (n+1) h = rom ⟨j,by omega⟩ ::
      bitsFrom rom (j+1) n (by omega) := by
  unfold bitsFrom
  rw [List.ofFn_succ]
  congr 1
  congr 1
  funext i
  congr 1
  apply Fin.ext
  simp [Fin.tail]
  omega

private theorem finish_frame (n : ℕ) (s : State) (f : FiniteFields) (op : Operation)
    (hs : s.phase = 7) (ho : s.operation = operationCodec op)
    (hi : s.addressed.outer.installation.tape = programTape)
    (hrow : s.row.query.val = (fieldsCodec f).val*24+
      (s.operation.val*6+s.slot.val))
    (hout : output s = some (frameTape (eventROM f op s.slot) s.offset))
    (hn : s.offset.val+(n+1) = frameWidth) :
    ∃ t, ∃ q : State, run s t = q ∧ q.phase = 8 ∧
      q.offset.val+1 = frameWidth ∧ q.slot = s.slot ∧ q.row = s.row ∧
      RenderFrame s q ∧ q.addressed.outer = s.addressed.outer ∧
      trace s t = bitsFrom (frameTape (eventROM f op s.slot))
        s.offset.val (n+1) (by omega) := by
  induction n generalizing s with
  | zero =>
    refine ⟨1,{s with phase := 8},?_,rfl,?_,rfl,rfl,rfl,rfl,?_⟩
    · simp [run,step,hs]
    · omega
    · simpa [trace,bitsFrom,List.ofFn_succ] using hout
  | succ n ih =>
    have hoff : s.offset.val+1 < frameWidth := by omega
    obtain ⟨ta,p,hp,hps,hpo,hpslot,hpout,hpr,hpf,hpa,hpt⟩ :=
      offset_emit s f op hs ho hi hrow hoff
    have hpop : p.operation = operationCodec op :=
      (congrArg State.operation hpf).trans ho
    have hpimage : p.addressed.outer.installation.tape = programTape := by
      rw [hpa]; exact hi
    have hprow : p.row.query.val = (fieldsCodec f).val*24+
        (p.operation.val*6+p.slot.val) := by
      rw [hpr,hpslot,hpop,← ho]
      exact hrow
    have hpoutput : output p = some (frameTape (eventROM f op p.slot) p.offset) := by
      rw [hpslot]
      have hoffeq : p.offset = ⟨s.offset.val+1,hoff⟩ := Fin.ext hpo
      rw [hoffeq]
      exact hpout
    obtain ⟨tb,q,hq,hqs,hqo,hqslot,hqr,hqf,hqa,hqt⟩ :=
      ih p hps hpop hpimage hprow hpoutput (by omega)
    refine ⟨ta+tb,q,?_,hqs,hqo,hqslot.trans hpslot,hqr.trans hpr,
      render_frame_trans hpf hqf,hqa.trans hpa,?_⟩
    · rw [run_add,hp,hq]
    · rw [trace_add,hp,hpt,hqt]
      conv_rhs => rw [bits_from_succ]
      have hl : s.addressed.control.latch =
          frameTape (eventROM f op s.slot) s.offset := by
        simpa [output,hs] using hout
      simp only [List.singleton_append,hl,hpslot,hpo]

private theorem render_slot (s : State) (f : FiniteFields) (op : Operation)
    (hs : s.phase = 5) (ho : s.operation = operationCodec op)
    (hi : s.addressed.outer.installation.tape = programTape)
    (hr : s.row = keyEntry (word (fieldsCodec f))
      ⟨s.operation.val*6+s.slot.val,by have := s.operation.isLt; have := s.slot.isLt; omega⟩)
    (hoff : s.offset.val = 0) :
    ∃ t, ∃ q : State, run s t = q ∧ q.phase = 8 ∧
      q.offset.val+1 = frameWidth ∧ q.slot = s.slot ∧
      q.row.query.val = (fieldsCodec f).val*24+
        (s.operation.val*6+s.slot.val) ∧
      RenderFrame s q ∧ q.addressed.outer = s.addressed.outer ∧
      trace s t = bitCode (frameCodec (eventROM f op s.slot)) := by
  obtain ⟨tr,p,hp,hphase,hout,hrow,hframe,houter,hquiet⟩ := row_emit s f op hs ho hi hr
  have hpoff : p.offset = s.offset := by
    have h := congrArg State.offset hframe
    exact h
  have hpof : p.offset.val = 0 := (congrArg Fin.val hpoff).trans hoff
  have hpop : p.operation = operationCodec op := (congrArg State.operation hframe).trans ho
  have hpslot : p.slot = s.slot := by
    have h := congrArg State.slot hframe
    exact h
  have hpimage : p.addressed.outer.installation.tape = programTape := by rw [houter]; exact hi
  have hprow : p.row.query.val = (fieldsCodec f).val*24+
      (p.operation.val*6+p.slot.val) := by
    rw [hpslot,hpop,← ho]; exact hrow
  have hpoutput : output p = some (frameTape (eventROM f op p.slot) p.offset) := by
    rw [hpslot,hpoff]
    exact hout
  obtain ⟨tc,q,hq,hqphase,hqoff,hqslot,hqrow,hqframe,hqouter,htrace⟩ :=
    finish_frame (frameWidth-1) p f op hphase hpop hpimage hprow hpoutput
      (by rw [hpof]; unfold frameWidth; omega)
  have hpframe : RenderFrame s p := by
    change p = _
    rw [hframe]
  refine ⟨tr+tc,q,?_,hqphase,hqoff,hqslot.trans hpslot,?_,
    render_frame_trans hpframe hqframe,hqouter.trans houter,?_⟩
  · rw [run_add,hp,hq]
  · rw [hqrow]; exact hrow
  · rw [trace_add,hp,hquiet,List.nil_append,htrace,hpslot]
    have hw : frameWidth-1+1 = frameWidth := by unfold frameWidth; omega
    have he : bitsFrom (frameTape (eventROM f op s.slot))
        p.offset.val (frameWidth-1+1) (by omega) =
        List.ofFn (frameTape (eventROM f op s.slot)) := by
      simp only [hpof,hw,bitsFrom,Nat.zero_add,Fin.val_cast,Fin.eta]
    rw [he]
    exact tape_list (frameCodec (eventROM f op s.slot))

private def framesFrom (f : FiniteFields) (op : Operation) (j n : ℕ)
    (h : j+n ≤ 6) : List Bool :=
  (List.ofFn (fun i : Fin n => bitCode (frameCodec
    (eventROM f op ⟨j+i.val,by have := i.isLt; omega⟩)))).flatten

private theorem frames_from_succ (f : FiniteFields) (op : Operation) (j n : ℕ)
    (h : j+(n+1) ≤ 6) :
    framesFrom f op j (n+1) h = bitCode (frameCodec (eventROM f op ⟨j,by omega⟩)) ++
      framesFrom f op (j+1) n (by omega) := by
  unfold framesFrom
  rw [List.ofFn_succ,List.flatten_cons]
  congr 1
  congr 1
  congr 1
  funext i
  congr 3
  apply Fin.ext
  simp [Fin.tail]
  omega

private theorem render_remaining (n : ℕ) (s : State) (f : FiniteFields) (op : Operation)
    (hs : s.phase = 5) (ho : s.operation = operationCodec op)
    (hi : s.addressed.outer.installation.tape = programTape)
    (hr : s.row = keyEntry (word (fieldsCodec f))
      ⟨s.operation.val*6+s.slot.val,by have := s.operation.isLt; have := s.slot.isLt; omega⟩)
    (hfields : s.fields.tape = word (fieldsCodec f)) (hoff : s.offset.val = 0)
    (hn : s.slot.val+(n+1) = 6) :
    ∃ t, ∃ q : State, run s t = q ∧ q.phase = 9 ∧ q.bankProbe = 0 ∧
      RenderFrame s q ∧ q.addressed.outer = s.addressed.outer ∧
      trace s t = framesFrom f op s.slot.val (n+1) (by omega) := by
  induction n generalizing s with
  | zero =>
    obtain ⟨tr,p,hp,hphase,hoffp,hslot,hrow,hframe,houter,htrace⟩ :=
      render_slot s f op hs ho hi hr hoff
    have hq : p.row.query.val < frameKeyWidth := by
      rw [hrow]
      have hf := (fieldsCodec f).isLt
      have hop := s.operation.isLt
      have hsl := s.slot.isLt
      unfold frameKeyWidth
      omega
    have hnext : ¬ p.offset.val+1 < frameWidth := by omega
    have hlast : ¬ p.slot.val+1 < 6 := by rw [hslot]; omega
    have hstep : step p = {p with phase := 9,bankProbe := 0} := by
      simp [step,hphase,hq,hnext,hlast]
    refine ⟨tr+1,{p with phase := 9,bankProbe := 0},?_,rfl,rfl,
      render_frame_trans hframe rfl,houter,?_⟩
    · rw [run_add,hp]
      exact hstep
    · rw [trace_add,hp,htrace,frames_from_succ]
      simp [trace,output,hphase,framesFrom]
  | succ n ih =>
    obtain ⟨tr,p,hp,hphase,hoffp,hslot,hrow,hframe,houter,htrace⟩ :=
      render_slot s f op hs ho hi hr hoff
    have hq : p.row.query.val < frameKeyWidth := by
      rw [hrow]
      have hf := (fieldsCodec f).isLt
      have hop := s.operation.isLt
      have hsl := s.slot.isLt
      unfold frameKeyWidth
      omega
    have hnext : ¬ p.offset.val+1 < frameWidth := by omega
    have hslotnext : p.slot.val+1 < 6 := by rw [hslot]; omega
    let next : State := {p with
      phase := 5
      slot := ⟨p.slot.val+1,hslotnext⟩
      offset := ⟨0,by unfold frameWidth; omega⟩
      row := keyEntry p.fields.tape
        ⟨p.operation.val*6+(p.slot.val+1),by have := p.operation.isLt; omega⟩}
    have hstep : step p = next := by
      simp [step,hphase,hq,hnext,hslotnext,next]
    have hpfields : p.fields.tape = word (fieldsCodec f) :=
      (congrArg (fun q => q.fields.tape) hframe).trans hfields
    have hpop : p.operation = operationCodec op := (congrArg State.operation hframe).trans ho
    have hnimage : next.addressed.outer.installation.tape = programTape := by
      change p.addressed.outer.installation.tape = _
      rw [houter]; exact hi
    have hnrow : next.row = keyEntry (word (fieldsCodec f))
        ⟨next.operation.val*6+next.slot.val,by
          have := next.operation.isLt; have := next.slot.isLt; omega⟩ := by
      change keyEntry p.fields.tape _ = _
      rw [hpfields]
    obtain ⟨tt,q,hret,hqphase,hprobe,hqframe,hqouter,hqtrace⟩ :=
      ih next rfl hpop hnimage hnrow hpfields rfl (by
        change p.slot.val+1+(n+1) = 6
        rw [hslot]
        omega)
    have hpnext : RenderFrame p next := rfl
    refine ⟨tr+1+tt,q,?_,hqphase,hprobe,
      render_frame_trans hframe (render_frame_trans hpnext hqframe),
      hqouter.trans houter,?_⟩
    · rw [run_add,run_add,hp]
      change run (step p) tt = q
      rw [hstep,hret]
    · rw [trace_add,trace_add,hp,htrace,run_add,hp]
      change bitCode (frameCodec (eventROM f op s.slot)) ++
        trace p 1 ++ trace (step p) tt = _
      rw [hstep,hqtrace]
      have hquiet : trace p 1 = [] := by simp [trace,output,hphase]
      rw [hquiet,List.append_nil]
      conv_rhs => rw [frames_from_succ]
      simp only [next,hslot,Fin.val_mk]

private theorem render_all (s : State) (f : FiniteFields) (op : Operation)
    (hs : s.phase = 5) (ho : s.operation = operationCodec op)
    (hi : s.addressed.outer.installation.tape = programTape)
    (hr : s.row = keyEntry (word (fieldsCodec f))
      ⟨s.operation.val*6+s.slot.val,by have := s.operation.isLt; have := s.slot.isLt; omega⟩)
    (hfields : s.fields.tape = word (fieldsCodec f))
    (hoff : s.offset.val = 0) (hslot : s.slot = 0) :
    ∃ t, ∃ q : State, run s t = q ∧ q.phase = 9 ∧ q.bankProbe = 0 ∧
      RenderFrame s q ∧ q.addressed.outer = s.addressed.outer ∧
      trace s t = (List.ofFn (fun slot : Fin 6 =>
        bitCode (frameCodec (eventROM f op slot)))).flatten := by
  obtain ⟨t,q,ht,hphase,hprobe,hframe,houter,htrace⟩ :=
    render_remaining 5 s f op hs ho hi hr hfields hoff (by rw [hslot]; rfl)
  refine ⟨t,q,ht,hphase,hprobe,hframe,houter,?_⟩
  simpa only [hslot,Fin.val_zero,framesFrom,Nat.zero_add,Fin.eta] using htrace

private theorem render_commit (s : State) (z d : Runtime) (op : Operation)
    (hs : s.phase = 5) (ho : s.operation = operationCodec op)
    (hi : s.addressed.outer.installation.tape = programTape)
    (hr : s.row = keyEntry (word (fieldsCodec z.fields))
      ⟨s.operation.val*6+s.slot.val,by have := s.operation.isLt; have := s.slot.isLt; omega⟩)
    (hfields : s.fields.tape = word (fieldsCodec z.fields))
    (hoff : s.offset.val = 0) (hslot : s.slot = 0)
    (hresult : s.result.tape = word (optionalRuntimeCodec (some d))) :
    ∃ t, ∃ q : State, run s t = q ∧ q.phase = 11 ∧
      q.actual = (if s.role then s.actual else word (runtimeCodec d)) ∧
      q.synthetic = (if s.role then word (runtimeCodec d) else s.synthetic) ∧
      q.operation = s.operation ∧ q.role = s.role ∧
      q.addressed.outer = s.addressed.outer ∧
      trace s t = (List.ofFn (fun slot : Fin 6 =>
        bitCode (frameCodec (eventROM z.fields op slot)))).flatten := by
  obtain ⟨tr,p,hp,hphase,hprobe,hframe,houter,htrace⟩ :=
    render_all s z.fields op hs ho hi hr hfields hoff hslot
  have hpresult : p.result.tape = word (optionalRuntimeCodec (some d)) :=
    (congrArg (fun q => q.result.tape) hframe).trans hresult
  obtain ⟨tw,q,hq,hqphase,ha,hc,hop,hrole,hqouter,hquiet⟩ :=
    write_complete p d hphase hprobe hpresult
  have hpa : p.actual = s.actual := by
    have h := congrArg State.actual hframe
    exact h
  have hpc : p.synthetic = s.synthetic := by
    have h := congrArg State.synthetic hframe
    exact h
  have hpr : p.role = s.role := by
    have h := congrArg State.role hframe
    exact h
  have hpo : p.operation = s.operation := by
    have h := congrArg State.operation hframe
    exact h
  refine ⟨tr+tw,q,?_,hqphase,?_,?_,hop.trans hpo,hrole.trans hpr,
    hqouter.trans houter,?_⟩
  · rw [run_add,hp,hq]
  · simpa only [hpa,hpr] using ha
  · simpa only [hpc,hpr] using hc
  · rw [trace_add,hp,htrace,hquiet,List.append_nil]

private theorem slot_monotone (s : State) : s.slot.val ≤ (step s).slot.val := by
  have hn : (scanStep s).slot = s.slot := by
    have h := congrArg State.slot (scan_frame s)
    exact h
  have hk : (buildKey s).slot = s.slot := by
    have h := (build_key_work s 1).2.2.2.1
    exact h
  unfold step
  split <;> repeat' first | exact le_rfl | split | omega | simpa only [hn,hk] using (Nat.le_refl s.slot.val)
  change s.slot.val ≤ s.slot.val+1
  omega

private def PastRender (s : State) : Prop :=
  0 < s.slot.val ∨ s.phase = 6 ∨ s.phase = 7 ∨ s.phase = 8 ∨
    s.phase = 9 ∨ s.phase = 10 ∨ s.phase = 11 ∨ s.phase = 12

private theorem past_render_step (s : State) (hs : PastRender s) : PastRender (step s) := by
  rcases hs with hslot | hs | hs | hs | hs | hs | hs | hs
  · exact Or.inl (Nat.lt_of_lt_of_le hslot (slot_monotone s))
  all_goals
    simp [PastRender,step,hs] <;> repeat' first | split | simp_all
  change 0 < s.slot.val+1
  omega

private theorem past_render_cuts (s : State) (hs : PastRender s) (n : ℕ) :
    PastRender (run s n) := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [run,Function.iterate_succ_apply']
    exact past_render_step (run s n) ih

private theorem preparing_quiet (s p : State) (t : ℕ) (hp : run s t = p)
    (hphase : p.phase = 5) (hslot : p.slot = 0) : trace s t = [] := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    have hs : s.phase ≠ 7 := by
      intro h
      have hpast := past_render_cuts s (Or.inr (Or.inr (Or.inl h))) (t+1)
      rw [hp] at hpast
      simp [PastRender,hphase,hslot] at hpast
    have hret : run (step s) t = p := by
      rw [run,Function.iterate_succ_apply] at hp
      exact hp
    simp only [trace,output,if_neg hs,Option.toList_none,List.nil_append]
    exact ih (step s) hret

private theorem retired_no_fault (s : State) (t : ℕ)
    (ht : (run s t).phase = 11) (n : ℕ) : (run s n).phase ≠ 12 := by
  intro hf
  by_cases hn : n ≤ t
  · have hfix : step (run s n) = run s n := by simp [step,hf]
    have heq : run s t = run (run s n) (t-n) := by
      rw [← run_add]
      congr 1
      omega
    rw [heq,run,Function.iterate_fixed hfix] at ht
    have he : (12 : Fin 14) = 11 := hf.symm.trans ht
    cases he
  · have hfix : step (run s t) = run s t := by simp [step,ht]
    have heq : run s n = run (run s t) (n-t) := by
      rw [← run_add]
      congr 1
      omega
    rw [heq,run,Function.iterate_fixed hfix,ht] at hf
    cases hf


end CurrentBank

end LiveProducer

namespace LiveProducer.Current

@[ext] structure State where
  saved : LiveProducer.State
  current : CurrentBank.State
  acquiring : Bool
  deriving DecidableEq

def actualRequest (s : State) : Bool := s.acquiring && !s.current.role
def freshRequest (_ : State) : Bool := false

def step (s : State) (source fresh : Letter) : State :=
  if s.acquiring then
    if s.current.role then {s with acquiring := false,current := {s.current with phase := 12}}
    else {s with acquiring := false,current := {s.current with operation := Fin.castAdd 2 source}}
  else {s with current := CurrentBank.step s.current}

def output (s : State) : Option Bool := if s.acquiring then none else CurrentBank.output s.current

def run (s : State) (source fresh : Letter) (ticks : ℕ) : State :=
  (fun q => step q source fresh)^[ticks] s

def entry (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) (role : Bool) (operation : Fin 4) : State :=
  ⟨saved,CurrentBank.entry image a c role operation,false⟩

def sourceEntry (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) : State :=
  {entry saved image a c false 0 with acquiring := true}

@[irreducible] def code (s : State) : List Bool :=
  LiveProducer.code s.saved ++ CurrentBank.code s.current ++ [s.acquiring]

def width : ℕ := LiveProducer.stateWidth+CurrentBank.width+1
@[irreducible] def staticImage : List Bool := LiveProducer.staticImage ++
  (List.ofFn (fun i : Fin 14 => bitCode i)).flatten ++
  (List.ofFn (fun i : Fin 2 => bitCode i)).flatten

def staticWidth : ℕ := LiveProducer.staticWidth+196+4
private theorem static_length : staticImage.length = staticWidth := by
  simp only [staticImage,staticWidth,List.length_append,LiveProducer.static_length,
    LiveProducer.opcode_length]

def bound : ℕ := programWidth+staticWidth+width+1

private theorem code_length (s : State) : (code s).length = width := by
  simp only [code,width,List.length_append,LiveProducer.code_length,CurrentBank.code_length,
    List.length_cons,List.length_nil]

private theorem code_injective : Function.Injective code := by
  intro s t h
  simp only [code,List.append_assoc] at h
  obtain ⟨hlegacy,h⟩ := split_block (LiveProducer.code s.saved) (LiveProducer.code t.saved) _ _
    LiveProducer.stateWidth (LiveProducer.code_length _) (LiveProducer.code_length _) h
  obtain ⟨hcurrent,hbool⟩ := split_block (CurrentBank.code s.current) (CurrentBank.code t.current) _ _
    CurrentBank.width (CurrentBank.code_length _) (CurrentBank.code_length _) h
  exact State.ext (LiveProducer.code_encoding hlegacy) (CurrentBank.code_injective hcurrent)
    (by simpa only [List.cons.injEq,and_true] using hbool)

private theorem charged (s : State) :
    programImage.length+staticImage.length+(code s).length < bound := by
  simp only [programImage,List.length_ofFn,static_length,code_length,bound]
  omega

private theorem passive_run (s : State) (hs : s.acquiring = false) (a b : Letter) (n : ℕ) :
    run s a b n = {s with current := CurrentBank.run s.current n} := by
  induction n with
  | zero => simp [run,CurrentBank.run]
  | succ n ih =>
    rw [run,Function.iterate_succ_apply']
    change step (run s a b n) a b = _
    rw [ih]
    simp only [step,hs,Bool.false_eq_true,↓reduceIte,CurrentBank.run,Function.iterate_succ_apply']

private theorem acquisition (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) (x y : Letter) :
    step (sourceEntry saved image a c) x y = entry saved image a c false (operationCodec (.read x)) := by
  rfl

private theorem ports (s : State) (a b c d : Letter) (h : actualRequest s = false) :
    step s a b = step s c d := by
  unfold actualRequest at h
  unfold step
  cases ha : s.acquiring <;> cases hr : s.current.role <;> simp_all

private theorem fetch_work (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) (role : Bool) (z : Runtime) (op : Operation)
    (himage : image.installation.tape = programTape)
    (hbank : (if role then c else a) = word (runtimeCodec z)) :
    ∃ t, ∃ q : State,
      run (entry saved image a c role (operationCodec op)) 0 0 t = q ∧
      q.acquiring = false ∧ q.current.phase = 2 ∧
      q.current.query = word (nativeKeyCodec (z,op)) ∧
      q.current.native = scannerEntry (nativeKeyCodec (z,op)) ∧
      q.current.opcodes.tape = CurrentBank.opcodeTape 0 ∧
      q.current.actual = a ∧ q.current.synthetic = c ∧
      q.current.operation = operationCodec op ∧ q.current.role = role ∧
      q.current.addressed.outer.installation.tape = programTape ∧
      q.current.pre.tape = word (runtimeCodec z) ∧
      q.current.result = motorEntry (runtimeSize+1) ∧
      q.current.fields = motorEntry 793800 ∧ q.current.slot = 0 ∧ q.current.offset = ⟨0,by unfold frameWidth; omega⟩ := by
  obtain ⟨tp,p,hp,hphase,hquery,hnative,ha,hc,hop,haddr,hcode,hrole,hpre,hres,hfields,hslot,hoff⟩ :=
    CurrentBank.bank_query image a c role z op hbank
  have hi : p.addressed.outer.installation.tape = programTape := by rw [haddr]; exact himage
  obtain ⟨tf,f,hf,hfphase,hfn,hpayload,hftape,hframe⟩ :=
    CurrentBank.opcode_frame p hphase hcode hi
  have hfq : f.query = p.query := by
    have h := congrArg CurrentBank.State.query hframe
    exact h
  have hfa : f.actual = p.actual := by
    have h := congrArg CurrentBank.State.actual hframe
    exact h
  have hfc : f.synthetic = p.synthetic := by
    have h := congrArg CurrentBank.State.synthetic hframe
    exact h
  have hfo : f.operation = p.operation := by
    have h := congrArg CurrentBank.State.operation hframe
    exact h
  have hfr : f.role = p.role := by
    have h := congrArg CurrentBank.State.role hframe
    exact h
  have hfad : f.addressed = p.addressed := by
    have h := congrArg CurrentBank.State.addressed hframe
    exact h
  have hrolef : f.role = role := hfr.trans hrole
  have hif : f.addressed.outer.installation.tape = programTape := by rw [hfad]; exact hi
  let start := entry saved image a c role (operationCodec op)
  let q : State := {start with current := f}
  refine ⟨tp+tf,q,?_,rfl,hfphase,hfq.trans hquery,hfn.trans hnative,?_,
    hfa.trans ha,hfc.trans hc,hfo.trans hop,hrolef,hif,?_,?_,?_,?_,?_⟩
  · have hfull : CurrentBank.run start.current (tp+tf) = f := by
      change CurrentBank.run (CurrentBank.entry image a c role (operationCodec op)) (tp+tf) = f
      rw [CurrentBank.run_add,hp,hf]
    rw [passive_run start rfl 0 0 (tp+tf),hfull]
  · simpa only [hnative,scannerEntry] using hftape
  · exact (congrArg (fun v => v.pre.tape) (show f = {p with native := f.native,payload := f.payload,phase := f.phase,opcodes := f.opcodes} from hframe)).trans hpre
  · exact (congrArg CurrentBank.State.result (show f = {p with native := f.native,payload := f.payload,phase := f.phase,opcodes := f.opcodes} from hframe)).trans hres
  · exact (congrArg CurrentBank.State.fields (show f = {p with native := f.native,payload := f.payload,phase := f.phase,opcodes := f.opcodes} from hframe)).trans hfields
  · exact (congrArg CurrentBank.State.slot (show f = {p with native := f.native,payload := f.payload,phase := f.phase,opcodes := f.opcodes} from hframe)).trans hslot
  · exact (congrArg CurrentBank.State.offset (show f = {p with native := f.native,payload := f.payload,phase := f.phase,opcodes := f.opcodes} from hframe)).trans hoff

private theorem paid_fetch (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) (role : Bool) (z : Runtime) (op : Operation)
    (himage : image.installation.tape = programTape)
    (hbank : (if role then c else a) = word (runtimeCodec z)) :
    ∃ t, ∃ q : State,
      run (entry saved image a c role (operationCodec op)) 0 0 t = q ∧
      q.acquiring = false ∧ q.current.phase = 2 ∧
      q.current.query = word (nativeKeyCodec (z,op)) ∧
      q.current.native = scannerEntry (nativeKeyCodec (z,op)) ∧
      q.current.opcodes.tape = CurrentBank.opcodeTape 0 ∧
      q.current.actual = a ∧ q.current.synthetic = c ∧
      q.current.operation = operationCodec op ∧ q.current.role = role ∧
      q.current.addressed.outer.installation.tape = programTape := by
  obtain ⟨t,q,hr,ha,hp,hq,hn,ho,hactual,hsynthetic,hop,hrole,hi,_⟩ :=
    fetch_work saved image a c role z op himage hbank
  exact ⟨t,q,hr,ha,hp,hq,hn,ho,hactual,hsynthetic,hop,hrole,hi⟩
end LiveProducer.Current

/-- A current physical bank supplies an unprepared query and paid resident
opcode fetch. Conditional scanner and writeback relations do not assert the
full native retirement or canonical-ready execution chain. -/
theorem current_bank_paid_fetch (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) (role : Bool) (z : Runtime) (op : Operation) :
    Function.Injective LiveProducer.Current.code ∧
    (∀ q : LiveProducer.Current.State, programImage.length+LiveProducer.Current.staticImage.length+
      (LiveProducer.Current.code q).length < LiveProducer.Current.bound) ∧
    (image.installation.tape = programTape →
      (if role then c else a) = LiveProducer.word (runtimeCodec z) →
      ∃ t, ∃ q : LiveProducer.Current.State,
        LiveProducer.Current.run (LiveProducer.Current.entry saved image a c role (operationCodec op)) 0 0 t = q ∧
        q.acquiring = false ∧ q.current.phase = 2 ∧
        q.current.query = LiveProducer.word (nativeKeyCodec (z,op)) ∧
        q.current.native = scannerEntry (nativeKeyCodec (z,op)) ∧
        q.current.opcodes.tape = LiveProducer.CurrentBank.opcodeTape 0 ∧
        q.current.actual = a ∧ q.current.synthetic = c ∧
        q.current.operation = operationCodec op ∧ q.current.role = role ∧
        q.current.addressed.outer.installation.tape = programTape) ∧
    (∀ q : LiveProducer.CurrentBank.State,
      q.addressed.outer.installation.tape = programTape →
      q.query = LiveProducer.word q.native.query →
      q.opcodes.tape = LiveProducer.CurrentBank.opcodeTape q.native.pc →
      (LiveProducer.CurrentBank.scanStep q).native = installedGraphStep nativeTable q.native) ∧
    (∀ (q : LiveProducer.CurrentBank.State) (n : ℕ), q.role = true →
      (LiveProducer.CurrentBank.run q n).actual = q.actual) ∧
    (∀ (q : LiveProducer.CurrentBank.State) (d : Runtime),
      q.phase = 9 → q.bankProbe = 0 →
      q.result.tape = LiveProducer.word (optionalRuntimeCodec (some d)) →
      ∃ t, ∃ r : LiveProducer.CurrentBank.State,
        LiveProducer.CurrentBank.run q t = r ∧ r.phase = 11 ∧
        LiveProducer.CurrentBank.bank r = LiveProducer.word (runtimeCodec d) ∧
        r.operation = q.operation ∧ (q.role = true → r.actual = q.actual)) ∧
    (∀ q : LiveProducer.CurrentBank.State,
      q.pre.tape = LiveProducer.word (runtimeCodec z) →
      LiveProducer.CurrentBank.fieldROM q = LiveProducer.word (fieldsCodec z.fields)) ∧
    (∀ (x y : Letter),
      LiveProducer.Current.step (LiveProducer.Current.sourceEntry saved image a c) x y =
        LiveProducer.Current.entry saved image a c false (operationCodec (.read x))) ∧
    (∀ (q : LiveProducer.Current.State) (a b c d : Letter),
      LiveProducer.Current.actualRequest q = false →
      LiveProducer.Current.step q a b = LiveProducer.Current.step q c d) := by
  exact ⟨LiveProducer.Current.code_injective,LiveProducer.Current.charged,
    LiveProducer.Current.paid_fetch saved image a c role z op,
    LiveProducer.CurrentBank.native_scan_refines,
    (fun q n h => (LiveProducer.CurrentBank.actual_cuts q h n).1),
    LiveProducer.CurrentBank.write_return,(fun q => LiveProducer.CurrentBank.field_rom q z),
    LiveProducer.Current.acquisition saved image a c,LiveProducer.Current.ports⟩


/-- The unprepared physical-bank path scans the installed native payload,
copies its result and old fields, and exposes the matching first event bit.
The acquisition clause binds both Read values to the actual captured Operation. -/
theorem current_bank_native_payload (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) (role : Bool) (z d : Runtime) (op : Operation)
    (himage : image.installation.tape = programTape)
    (hbank : (if role then c else a) = LiveProducer.word (runtimeCodec z))
    (hd : runtimeStep z op = some d) :
    ∃ t, ∃ q : LiveProducer.Current.State,
      LiveProducer.Current.run (LiveProducer.Current.entry saved image a c role (operationCodec op)) 0 0 t = q ∧
      q.acquiring = false ∧ q.current.phase = 5 ∧
      q.current.payload = LiveProducer.word (optionalRuntimeCodec (some d)) ∧
      q.current.native.pc = 2 ∧ q.current.actual = a ∧ q.current.synthetic = c ∧
      q.current.operation = operationCodec op ∧ q.current.role = role ∧
      q.current.addressed.outer.installation.tape = programTape ∧
      q.current.result.tape = LiveProducer.word (optionalRuntimeCodec (some d)) ∧
      q.current.pre.tape = LiveProducer.word (runtimeCodec z) ∧
      q.current.fields.tape = LiveProducer.word (fieldsCodec z.fields) ∧
      q.current.slot = 0 ∧ q.current.offset = ⟨0,by unfold frameWidth; omega⟩ ∧
      q.current.row = LiveProducer.keyEntry (LiveProducer.word (fieldsCodec z.fields))
        ⟨(operationCodec op).val*6,by have := (operationCodec op).isLt; omega⟩ ∧
      (∀ (x y : Letter), role = false → op = .read x →
        LiveProducer.Current.run
          (LiveProducer.Current.step (LiveProducer.Current.sourceEntry saved image a c) x y)
          0 0 t = q) ∧
      ∃ n, ∃ r : LiveProducer.Current.State,
        LiveProducer.Current.run q 0 0 n = r ∧ r.current.phase = 7 ∧
        LiveProducer.Current.output r = some
          (frameTape (eventROM z.fields op 0) ⟨0,by unfold frameWidth; omega⟩) ∧
        r.current.actual = a ∧ r.current.synthetic = c := by
  obtain ⟨tp,p,hp,hacq,hphase,hquery,hnative,hopcode,ha,hc,hop,hrole,himagep,hpre,hres,hfields,hslot,hoff⟩ :=
    LiveProducer.Current.fetch_work saved image a c role z op himage hbank
  obtain ⟨n,v,hv,hpc,hacc⟩ := LiveProducer.native_endpoint z op d hd
  have he : ((installedGraphStep nativeTable)^[n] p.current.native).pc = 2 := by
    rw [hnative,hv]
    exact hpc
  have hgood : LiveProducer.CurrentBank.PayloadGood p.current.native p.current.payload := by
    rw [hnative]
    simp [LiveProducer.CurrentBank.PayloadGood,scannerEntry]
  have hsafe : LiveProducer.ScannerSafe p.current.native := by
    rw [hnative]
    simp [LiveProducer.ScannerSafe,scannerEntry]
  have hquery' : p.current.query = LiveProducer.word p.current.native.query := by
    rw [hnative]
    exact hquery
  have hopcode' : p.current.opcodes.tape =
      LiveProducer.CurrentBank.opcodeTape p.current.native.pc := by
    rw [hnative]
    exact hopcode
  obtain ⟨tn,r,hr,hrphase,hrnative,hrgood,hrframe,hrsafe⟩ :=
    LiveProducer.CurrentBank.scan_exit p.current n hphase himagep hquery' hopcode' hgood hsafe he
  have hrpc : r.native.pc = 2 := by rw [hrnative]; exact he
  let row : Fin (runtimeSize*4) := ⟨r.native.row.val,hrsafe hrpc⟩
  obtain ⟨hvalue,hbits⟩ := (hrgood row rfl).2 hrpc
  have hracc : r.native.accumulator.val = (optionalRuntimeCodec (some d)).val := by
    rw [hrnative,hnative,hv]
    exact hacc
  have htable : nativeTable row = optionalRuntimeCodec (some d) :=
    Fin.ext (hvalue.symm.trans hracc)
  have hresult : r.payload = LiveProducer.word (optionalRuntimeCodec (some d)) := by
    rw [hbits,htable]
  have hrpre : r.pre.tape = LiveProducer.word (runtimeCodec z) :=
    (congrArg (fun v => v.pre.tape) (show r = {p.current with native := r.native,payload := r.payload,phase := r.phase,opcodes := r.opcodes} from hrframe)).trans hpre
  have hrres : r.result = motorEntry (runtimeSize+1) :=
    (congrArg LiveProducer.CurrentBank.State.result (show r = {p.current with native := r.native,payload := r.payload,phase := r.phase,opcodes := r.opcodes} from hrframe)).trans hres
  have hrfields : r.fields = motorEntry 793800 :=
    (congrArg LiveProducer.CurrentBank.State.fields (show r = {p.current with native := r.native,payload := r.payload,phase := r.phase,opcodes := r.opcodes} from hrframe)).trans hfields
  have hrslot : r.slot = 0 :=
    (congrArg LiveProducer.CurrentBank.State.slot (show r = {p.current with native := r.native,payload := r.payload,phase := r.phase,opcodes := r.opcodes} from hrframe)).trans hslot
  have hroff : r.offset = ⟨0,by unfold frameWidth; omega⟩ :=
    (congrArg LiveProducer.CurrentBank.State.offset (show r = {p.current with native := r.native,payload := r.payload,phase := r.phase,opcodes := r.opcodes} from hrframe)).trans hoff
  obtain ⟨tf,f,htf,hfphase,hfresult,hffields,hfrow,hfframe⟩ :=
    LiveProducer.CurrentBank.prepare_event r z d hrphase hresult hrpre hrres hrfields
  have hret : LiveProducer.CurrentBank.run p.current (tn+tf) = f := by
    rw [LiveProducer.CurrentBank.run_add,hr,htf]
  let q : LiveProducer.Current.State := {p with current := f}
  have hrop : r.operation = operationCodec op :=
    (congrArg LiveProducer.CurrentBank.State.operation (show r = {p.current with native := r.native,payload := r.payload,phase := r.phase,opcodes := r.opcodes} from hrframe)).trans hop
  have hmain : LiveProducer.Current.run
      (LiveProducer.Current.entry saved image a c role (operationCodec op))
      0 0 (tp+(tn+tf)) = q := by
    rw [LiveProducer.Current.run,Nat.add_comm tp (tn+tf),Function.iterate_add_apply]
    change LiveProducer.Current.run
      (LiveProducer.Current.run (LiveProducer.Current.entry saved image a c role (operationCodec op))
        0 0 tp) 0 0 (tn+tf) = q
    rw [hp,LiveProducer.Current.passive_run p hacq 0 0 (tn+tf),hret]
  refine ⟨tp+(tn+tf),q,hmain,hacq,hfphase,?_,?_,?_,?_,?_,?_,?_,
    hfresult,?_,hffields,?_,?_,?_,?_,?_⟩
  · exact (congrArg LiveProducer.CurrentBank.State.payload hfframe).trans hresult
  · exact (congrArg (fun v => v.native.pc) hfframe).trans hrpc
  · exact (congrArg LiveProducer.CurrentBank.State.actual hfframe).trans
      ((congrArg LiveProducer.CurrentBank.State.actual hrframe).trans ha)
  · exact (congrArg LiveProducer.CurrentBank.State.synthetic hfframe).trans
      ((congrArg LiveProducer.CurrentBank.State.synthetic hrframe).trans hc)
  · exact (congrArg LiveProducer.CurrentBank.State.operation hfframe).trans hrop
  · exact (congrArg LiveProducer.CurrentBank.State.role hfframe).trans
      ((congrArg LiveProducer.CurrentBank.State.role hrframe).trans hrole)
  · exact (congrArg (fun v => v.addressed.outer.installation.tape) hfframe).trans
      ((congrArg (fun v => v.addressed.outer.installation.tape) hrframe).trans himagep)
  · exact (congrArg (fun v => v.pre.tape) hfframe).trans hrpre
  · exact (congrArg LiveProducer.CurrentBank.State.slot hfframe).trans hrslot
  · exact (congrArg LiveProducer.CurrentBank.State.offset hfframe).trans hroff
  · rw [hfrow]
    congr 1
    apply Fin.ext
    change r.operation.val*6+r.slot.val = (operationCodec op).val*6
    rw [hrop,hrslot]
    simp
  · intro x y hrf hopread
    simpa only [hrf,hopread,LiveProducer.Current.acquisition] using hmain
  · have hfop : f.operation = operationCodec op :=
      (congrArg LiveProducer.CurrentBank.State.operation hfframe).trans hrop
    have hfslot : f.slot = 0 :=
      (congrArg LiveProducer.CurrentBank.State.slot hfframe).trans hrslot
    have hfoff : f.offset = ⟨0,by unfold frameWidth; omega⟩ :=
      (congrArg LiveProducer.CurrentBank.State.offset hfframe).trans hroff
    have hfimage : f.addressed.outer.installation.tape = programTape :=
      (congrArg (fun v => v.addressed.outer.installation.tape) hfframe).trans
        ((congrArg (fun v => v.addressed.outer.installation.tape) hrframe).trans himagep)
    have hfkey : f.row = LiveProducer.keyEntry (LiveProducer.word (fieldsCodec z.fields))
        ⟨f.operation.val*6+f.slot.val,by
          have := f.operation.isLt; have := f.slot.isLt; omega⟩ := by
      rw [hfrow]
      congr 1
      apply Fin.ext
      change r.operation.val*6+r.slot.val = f.operation.val*6+f.slot.val
      rw [hrop,hrslot,hfop,hfslot]
    obtain ⟨te,e,he,hephase,heoutput,_,heframe,heouter,_⟩ :=
      LiveProducer.CurrentBank.row_emit f z.fields op hfphase hfop hfimage hfkey
    let returned : LiveProducer.Current.State := {q with current := e}
    refine ⟨te,returned,?_,hephase,?_,?_,?_⟩
    · rw [LiveProducer.Current.passive_run q hacq 0 0 te,he]
    · change (if p.acquiring then none else LiveProducer.CurrentBank.output e) = _
      rw [hacq]
      simpa only [Bool.false_eq_true,↓reduceIte,hfslot,hfoff] using heoutput
    · exact (congrArg LiveProducer.CurrentBank.State.actual heframe).trans
        ((congrArg LiveProducer.CurrentBank.State.actual hfframe).trans
          ((congrArg LiveProducer.CurrentBank.State.actual hrframe).trans ha))
    · exact (congrArg LiveProducer.CurrentBank.State.synthetic heframe).trans
        ((congrArg LiveProducer.CurrentBank.State.synthetic hfframe).trans
          ((congrArg LiveProducer.CurrentBank.State.synthetic hrframe).trans hc))


/-- The unprepared physical-bank producer streams all six original frame
words in order and then writes the entire successor Runtime to the selected
physical bank. Phase eleven is retained work, not canonical Ready. -/
theorem current_bank_original_frames (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) (role : Bool) (z d : Runtime) (op : Operation)
    (himage : image.installation.tape = programTape)
    (hbank : (if role then c else a) = LiveProducer.word (runtimeCodec z))
    (hd : runtimeStep z op = some d) :
    ∃ tp, ∃ p : LiveProducer.Current.State, ∃ tr, ∃ q : LiveProducer.Current.State,
      LiveProducer.Current.run
        (LiveProducer.Current.entry saved image a c role (operationCodec op)) 0 0 tp = p ∧
      p.acquiring = false ∧ p.current.phase = 5 ∧
      LiveProducer.Current.run p 0 0 tr = q ∧ q.current.phase = 11 ∧
      q.current.actual = (if role then a else LiveProducer.word (runtimeCodec d)) ∧
      q.current.synthetic = (if role then LiveProducer.word (runtimeCodec d) else c) ∧
      q.current.operation = operationCodec op ∧ q.current.role = role ∧
      q.current.addressed.outer.installation.tape = programTape ∧
      LiveProducer.CurrentBank.trace p.current tr =
        (List.ofFn (fun slot : Fin 6 => bitCode
          (frameCodec (eventROM z.fields op slot)))).flatten ∧
      LiveProducer.CurrentBank.trace
        (LiveProducer.CurrentBank.entry image a c role (operationCodec op)) (tp+tr) =
        (List.ofFn (fun slot : Fin 6 => bitCode
          (frameCodec (eventROM z.fields op slot)))).flatten ∧
      (∀ k, k ≤ tp+tr → ∃ suffix : List Bool,
        (List.ofFn (fun slot : Fin 6 => bitCode
          (frameCodec (eventROM z.fields op slot)))).flatten =
          LiveProducer.CurrentBank.trace
            (LiveProducer.CurrentBank.entry image a c role (operationCodec op)) k ++ suffix) ∧
      (∀ n, (LiveProducer.CurrentBank.run
        (LiveProducer.CurrentBank.entry image a c role (operationCodec op)) n).phase ≠ 12 ∧
        (role = true → (LiveProducer.CurrentBank.run
          (LiveProducer.CurrentBank.entry image a c role (operationCodec op)) n).actual = a)) ∧
      ((List.ofFn (fun slot : Fin 6 => decodeFrame
        (bitCode (frameCodec (eventROM z.fields op slot))))).filterMap id).map original =
          eventBlock z.fields op ∧
      (∀ (x y : Letter), role = false → op = .read x →
        LiveProducer.Current.run
          (LiveProducer.Current.step (LiveProducer.Current.sourceEntry saved image a c) x y)
          0 0 (tp+tr) = q) := by
  obtain ⟨tp,p,hp,hacq,hphase,_,_,ha,hc,hop,hrole,hi,hresult,_,hfields,hslot,hoff,hrow,hread,_⟩ :=
    current_bank_native_payload saved image a c role z d op himage hbank hd
  have hr : p.current.row = LiveProducer.keyEntry (LiveProducer.word (fieldsCodec z.fields))
      ⟨p.current.operation.val*6+p.current.slot.val,by
        have := p.current.operation.isLt; have := p.current.slot.isLt; omega⟩ := by
    rw [hrow]
    congr 1
    apply Fin.ext
    simp only [hop,hslot,Fin.val_mk,Fin.val_zero,Nat.add_zero]
  obtain ⟨tr,r,hrun,hrphase,hra,hrc,hro,hrr,hri,htrace⟩ :=
    LiveProducer.CurrentBank.render_commit p.current z d op hphase hop hi hr hfields
      (by rw [hoff]) hslot hresult
  let q : LiveProducer.Current.State := {p with current := r}
  have hq : LiveProducer.Current.run p 0 0 tr = q := by
    rw [LiveProducer.Current.passive_run p hacq 0 0 tr,hrun]
  have hpre : LiveProducer.CurrentBank.run
      (LiveProducer.CurrentBank.entry image a c role (operationCodec op)) tp = p.current := by
    have h := congrArg LiveProducer.Current.State.current hp
    rw [LiveProducer.Current.passive_run _ rfl 0 0 tp] at h
    exact h
  have hquiet := LiveProducer.CurrentBank.preparing_quiet _ p.current tp hpre hphase hslot
  have hwhole : LiveProducer.CurrentBank.trace
      (LiveProducer.CurrentBank.entry image a c role (operationCodec op)) (tp+tr) =
      (List.ofFn (fun slot : Fin 6 => bitCode
        (frameCodec (eventROM z.fields op slot)))).flatten := by
    rw [LiveProducer.CurrentBank.trace_add,hpre,hquiet,List.nil_append,htrace]
  have htotal : LiveProducer.CurrentBank.run
      (LiveProducer.CurrentBank.entry image a c role (operationCodec op)) (tp+tr) = r := by
    rw [LiveProducer.CurrentBank.run_add,hpre,hrun]
  refine ⟨tp,p,tr,q,hp,hacq,hphase,hq,hrphase,?_,?_,hro.trans hop,hrr.trans hrole,
    ?_,htrace,hwhole,?_,?_,?_,?_⟩
  · simpa only [ha,hrole] using hra
  · simpa only [hc,hrole] using hrc
  · exact (congrArg (fun v => v.installation.tape) hri).trans hi
  · intro k hk
    refine ⟨LiveProducer.CurrentBank.trace
      (LiveProducer.CurrentBank.run
        (LiveProducer.CurrentBank.entry image a c role (operationCodec op)) k) (tp+tr-k),?_⟩
    rw [← LiveProducer.CurrentBank.trace_add,show k+(tp+tr-k)=tp+tr by omega,hwhole]
  · intro n
    constructor
    · exact LiveProducer.CurrentBank.retired_no_fault _ (tp+tr)
        (by rw [htotal]; exact hrphase) n
    · intro hroletrue
      exact (LiveProducer.CurrentBank.actual_cuts _ hroletrue n).1
  · simp only [decode_code]
    exact (six_slot_original_events z.fields op).2.2
  · intro x y hr hx
    rw [LiveProducer.Current.run,Nat.add_comm tp tr,Function.iterate_add_apply]
    change LiveProducer.Current.run
      (LiveProducer.Current.run
        (LiveProducer.Current.step (LiveProducer.Current.sourceEntry saved image a c) x y)
        0 0 tp) 0 0 tr = q
    rw [hread x y hr hx,hq]


namespace LiveProducer.Return

set_option maxRecDepth 10000

def scratchWidth : ℕ := (runtimeSize) + ((runtimeSize+1) + ((runtimeSize) + ((runtimeSize*4) + ((runtimeSize+1) + ((runtimeSize+1) + ((runtimeSize+2) + ((793800) + ((793801) + ((793800) + ((12) + ((13) + ((frameKeyWidth) + ((frameWidth) + ((programWidth) + ((programWidth+1) + ((14) + ((15))))))))))))))))))

def controlCount : ℕ := 50

/-- A successor controller around the retained native segment. Only its current
core is cleared; the saved service and outer installation context are retained. -/

@[ext] structure State where
  current : Current.State
  menu : Motor 14
  pc : Fin 9
  cursor : Fin (scratchWidth+1)
  control : Fin (controlCount+1)
  deriving DecidableEq

abbrev Cell := Fin (runtimeSize) ⊕ Fin (runtimeSize+1) ⊕ Fin (runtimeSize) ⊕ Fin (runtimeSize*4) ⊕ Fin (runtimeSize+1) ⊕ Fin (runtimeSize+1) ⊕ Fin (runtimeSize+2) ⊕ Fin (793800) ⊕ Fin (793801) ⊕ Fin (793800) ⊕ Fin (12) ⊕ Fin (13) ⊕ Fin (frameKeyWidth) ⊕ Fin (frameWidth) ⊕ Fin (programWidth) ⊕ Fin (programWidth+1) ⊕ Fin (14) ⊕ Fin (15)


def cellCodec : Cell ≃ Fin scratchWidth := (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (sumFin (Equiv.refl _) (Equiv.refl _))))))))))))))))))

def readCell (s : State) : Cell → Bool
  | (.inl i) => s.current.current.pre.tape i
  | (.inr (.inl i)) => s.current.current.pre.headBits i
  | (.inr (.inr (.inl i))) => s.current.current.key.tape i
  | (.inr (.inr (.inr (.inl i)))) => s.current.current.query i
  | (.inr (.inr (.inr (.inr (.inl i))))) => s.current.current.payload i
  | (.inr (.inr (.inr (.inr (.inr (.inl i)))))) => s.current.current.result.tape i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))) => s.current.current.result.headBits i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))) => s.current.current.fields.tape i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))) => s.current.current.fields.headBits i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))) => s.current.current.row.tape i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))) => s.current.current.opcodes.tape i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))) => s.current.current.opcodes.headBits i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))))) => s.current.current.addressed.key i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))))) => s.current.current.addressed.offset i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))))))) => s.current.current.addressed.head.tape i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))))))) => s.current.current.addressed.head.headBits i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))))))))) => s.menu.tape i
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr i))))))))))))))))) => s.menu.headBits i

/-- One physical scratch cell is written. No Runtime is decoded or assigned. -/

def clearCell (s : State) : Cell → State
  | (.inl i) => {s with current := {s.current with current := {s.current.current with pre := {s.current.current.pre with tape := Function.update s.current.current.pre.tape i false}}}}
  | (.inr (.inl i)) => {s with current := {s.current with current := {s.current.current with pre := {s.current.current.pre with headBits := Function.update s.current.current.pre.headBits i false}}}}
  | (.inr (.inr (.inl i))) => {s with current := {s.current with current := {s.current.current with key := {s.current.current.key with tape := Function.update s.current.current.key.tape i false}}}}
  | (.inr (.inr (.inr (.inl i)))) => {s with current := {s.current with current := {s.current.current with query := Function.update s.current.current.query i false}}}
  | (.inr (.inr (.inr (.inr (.inl i))))) => {s with current := {s.current with current := {s.current.current with payload := Function.update s.current.current.payload i false}}}
  | (.inr (.inr (.inr (.inr (.inr (.inl i)))))) => {s with current := {s.current with current := {s.current.current with result := {s.current.current.result with tape := Function.update s.current.current.result.tape i false}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))) => {s with current := {s.current with current := {s.current.current with result := {s.current.current.result with headBits := Function.update s.current.current.result.headBits i false}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))) => {s with current := {s.current with current := {s.current.current with fields := {s.current.current.fields with tape := Function.update s.current.current.fields.tape i false}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))) => {s with current := {s.current with current := {s.current.current with fields := {s.current.current.fields with headBits := Function.update s.current.current.fields.headBits i false}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))) => {s with current := {s.current with current := {s.current.current with row := {s.current.current.row with tape := Function.update s.current.current.row.tape i false}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))) => {s with current := {s.current with current := {s.current.current with opcodes := {s.current.current.opcodes with tape := Function.update s.current.current.opcodes.tape i false}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))) => {s with current := {s.current with current := {s.current.current with opcodes := {s.current.current.opcodes with headBits := Function.update s.current.current.opcodes.headBits i false}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))))) => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with key := Function.update s.current.current.addressed.key i false}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))))) => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with offset := Function.update s.current.current.addressed.offset i false}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))))))) => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with head := {s.current.current.addressed.head with tape := Function.update s.current.current.addressed.head.tape i false}}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))))))) => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with head := {s.current.current.addressed.head with headBits := Function.update s.current.current.addressed.head.headBits i false}}}}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))))))))) => {s with menu := {s.menu with tape := Function.update s.menu.tape i false}}
  | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr i))))))))))))))))) => {s with menu := {s.menu with headBits := Function.update s.menu.headBits i false}}

private def zeroOffset : Fin frameWidth := ⟨0,by unfold frameWidth; omega⟩

/-- Every case is a paid finite rail-control set. These are still macro rail
instructions, separate from the single-bit scratch writes. -/

def setControl (s : State) (tag : Fin controlCount) : State :=
  match tag.val with
  | 0 => {s with current := {s.current with current := {s.current.current with pre := {s.current.current.pre with probe := 0}}}}
  | 1 => {s with current := {s.current with current := {s.current.current with pre := {s.current.current.pre with pc := .seek}}}}
  | 2 => {s with current := {s.current with current := {s.current.current with pre := {s.current.current.pre with latch := false}}}}
  | 3 => {s with current := {s.current with current := {s.current.current with result := {s.current.current.result with probe := 0}}}}
  | 4 => {s with current := {s.current with current := {s.current.current with result := {s.current.current.result with pc := .seek}}}}
  | 5 => {s with current := {s.current with current := {s.current.current with result := {s.current.current.result with latch := false}}}}
  | 6 => {s with current := {s.current with current := {s.current.current with fields := {s.current.current.fields with probe := 0}}}}
  | 7 => {s with current := {s.current with current := {s.current.current with fields := {s.current.current.fields with pc := .seek}}}}
  | 8 => {s with current := {s.current with current := {s.current.current with fields := {s.current.current.fields with latch := false}}}}
  | 9 => {s with current := {s.current with current := {s.current.current with opcodes := {s.current.current.opcodes with probe := 0}}}}
  | 10 => {s with current := {s.current with current := {s.current.current with opcodes := {s.current.current.opcodes with pc := .seek}}}}
  | 11 => {s with current := {s.current with current := {s.current.current with opcodes := {s.current.current.opcodes with latch := false}}}}
  | 12 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with head := {s.current.current.addressed.head with probe := 0}}}}}
  | 13 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with head := {s.current.current.addressed.head with pc := .seek}}}}}
  | 14 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with head := {s.current.current.addressed.head with latch := false}}}}}
  | 15 => {s with current := {s.current with current := {s.current.current with key := {s.current.current.key with tail := 0}}}}
  | 16 => {s with current := {s.current with current := {s.current.current with key := {s.current.current.key with probe := 0}}}}
  | 17 => {s with current := {s.current with current := {s.current.current with key := {s.current.current.key with carry := 0}}}}
  | 18 => {s with current := {s.current with current := {s.current.current with key := {s.current.current.key with query := 0}}}}
  | 19 => {s with current := {s.current with current := {s.current.current with key := {s.current.current.key with pc := 0}}}}
  | 20 => {s with current := {s.current with current := {s.current.current with row := {s.current.current.row with tail := 0}}}}
  | 21 => {s with current := {s.current with current := {s.current.current with row := {s.current.current.row with probe := 0}}}}
  | 22 => {s with current := {s.current with current := {s.current.current with row := {s.current.current.row with carry := 0}}}}
  | 23 => {s with current := {s.current with current := {s.current.current with row := {s.current.current.row with query := 0}}}}
  | 24 => {s with current := {s.current with current := {s.current.current with row := {s.current.current.row with pc := 0}}}}
  | 25 => {s with current := {s.current with current := {s.current.current with native := {s.current.current.native with query := ⟨0,by unfold runtimeSize; omega⟩}}}}
  | 26 => {s with current := {s.current with current := {s.current.current with native := {s.current.current.native with row := 0}}}}
  | 27 => {s with current := {s.current with current := {s.current.current with native := {s.current.current.native with cursor := 0}}}}
  | 28 => {s with current := {s.current with current := {s.current.current with native := {s.current.current.native with accumulator := 0}}}}
  | 29 => {s with current := {s.current with current := {s.current.current with native := {s.current.current.native with equalFlag := true}}}}
  | 30 => {s with current := {s.current with current := {s.current.current with native := {s.current.current.native with pc := 0}}}}
  | 31 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with control := {s.current.current.addressed.control with baseProbe := 0}}}}}
  | 32 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with control := {s.current.current.addressed.control with keyProbe := 0}}}}}
  | 33 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with control := {s.current.current.addressed.control with strideProbe := 0}}}}}
  | 34 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with control := {s.current.current.addressed.control with offsetProbe := 0}}}}}
  | 35 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with control := {s.current.current.addressed.control with pc := .baseTest}}}}}
  | 36 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with control := {s.current.current.addressed.control with returnBase := true}}}}}
  | 37 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with control := {s.current.current.addressed.control with returnStride := false}}}}}
  | 38 => {s with current := {s.current with current := {s.current.current with addressed := {s.current.current.addressed with control := {s.current.current.addressed.control with latch := false}}}}}
  | 39 => {s with current := {s.current with current := {s.current.current with role := false}}}
  | 40 => {s with current := {s.current with current := {s.current.current with operation := 0}}}
  | 41 => {s with current := {s.current with current := {s.current.current with slot := 0}}}
  | 42 => {s with current := {s.current with current := {s.current.current with offset := zeroOffset}}}
  | 43 => {s with current := {s.current with current := {s.current.current with bankProbe := 0}}}
  | 44 => {s with current := {s.current with current := {s.current.current with bankLatch := false}}}
  | 45 => {s with current := {s.current with current := {s.current.current with phase := 0}}}
  | 46 => {s with current := {s.current with acquiring := false}}
  | 47 => {s with menu := {s.menu with probe := 0}}
  | 48 => {s with menu := {s.menu with pc := .seek}}
  | 49 => {s with menu := {s.menu with latch := false}}
  | _ => s

/-- The menu taps the last bit of each control block in the committed bank.
The arithmetic tap map is a macro, and the fourteen copied bits are paid. -/
def menuROM (s : State) (i : Fin 14) : Bool :=
  s.current.current.actual ⟨(i.val+1)*(56700*(6023*4))-1,by
    have := i.isLt
    unfold runtimeSize
    omega⟩

def menuClass (tape : Fin 14 → Bool) : Fin 4 :=
  if tape 12 then 3 else if tape 11 then 2 else if tape 10 then 1 else 0

def actualRequest (s : State) : Bool :=
  if s.pc = 0 then Current.actualRequest s.current else decide (s.pc = 7)
def freshRequest (_ : State) : Bool := false

/-- Zero executes the unchanged Current segment; one acknowledges its return;
two erases scratch; three sets rail controls; four is core-ready; five copies
committed control; six dispatches that copied menu; seven acquires; eight stops. -/

def step (s : State) (source fresh : Letter) : State :=
  match s.pc.val with
  | 0 => if s.current.current.phase = 11 then {s with pc := 1}
    else {s with current := Current.step s.current source fresh}
  | 1 => {s with pc := 2,cursor := 0}
  | 2 => if h : s.cursor.val < scratchWidth then
      {(clearCell s (cellCodec.symm ⟨s.cursor.val,h⟩)) with
        cursor := ⟨s.cursor.val+1,by omega⟩}
    else {s with pc := 3,control := 0}
  | 3 => if h : s.control.val < controlCount then
      {(setControl s ⟨s.control.val,h⟩) with control := ⟨s.control.val+1,by omega⟩}
    else {s with pc := 4,cursor := 0,control := 0}
  | 4 => {s with pc := 5}
  | 5 => if s.menu.pc = .halt then {s with pc := 6}
    else {s with menu := motorStep (menuROM s) s.menu}
  | 6 => match (menuClass s.menu.tape).val with
      | 0 => {s with pc := 7}
      | 1 => {s with pc := 0,current := {s.current with current := {s.current.current with operation := 2}}}
      | 2 => {s with pc := 0,current := {s.current with current := {s.current.current with operation := 3}}}
      | _ => {s with pc := 8}
  | 7 => {s with pc := 0, current := {s.current with
      current := {s.current.current with operation := Fin.castAdd 2 source}}}
  | _ => s


private theorem current_ports (s : Current.State) (a b c d : Letter)
    (h : Current.actualRequest s = false) : Current.step s a b = Current.step s c d := by
  cases ha : s.acquiring <;> cases hr : s.current.role <;>
    simp [Current.actualRequest,Current.step,ha,hr] at h ⊢

private theorem ports (s : State) (a b c d : Letter)
    (h : actualRequest s = false) : step s a b = step s c d := by
  have hlt := s.pc.isLt
  interval_cases hp : s.pc.val
  · have hpc : s.pc = 0 := Fin.ext hp
    have hh : Current.actualRequest s.current = false := by
      simpa only [actualRequest,hpc,↓reduceIte] using h
    simp only [step,hp]
    split
    · simp only [step,hp] <;> rfl
    · rw [current_ports s.current a b c d hh]
  · simp only [step,hp] <;> rfl
  · simp only [step,hp] <;> rfl
  · simp only [step,hp] <;> rfl
  · simp only [step,hp] <;> rfl
  · simp only [step,hp] <;> rfl
  · simp only [step,hp] <;> rfl
  · have hpc : s.pc = 7 := Fin.ext hp
    simp [actualRequest,hpc] at h
  · simp only [step,hp] <;> rfl

@[irreducible] def run (s : State) (source fresh : Letter) (n : ℕ) : State :=
  (fun q => step q source fresh)^[n] s

def entry (s : Current.State) : State := ⟨s,motorEntry 14,0,0,0⟩

def coreReady (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) : State :=
  ⟨Current.entry saved image a c false 0,motorEntry 14,4,0,0⟩

private noncomputable def cellDecidableEq : DecidableEq Cell := Classical.decEq Cell
attribute [local instance] cellDecidableEq


private theorem read_clear (s : State) (c d : Cell) :
    readCell (clearCell s c) d = if d = c then false else readCell s d := by
  rcases c with i | i | i | i | i | i | i | i | i | i | i | i | i | i | i | i | i | i <;> rcases d with j | j | j | j | j | j | j | j | j | j | j | j | j | j | j | j | j | j <;>
    simp [readCell,clearCell,Function.update_apply]

private theorem clear_frame (s : State) (c : Cell) :
    (clearCell s c).current.saved = s.current.saved ∧
    (clearCell s c).current.current.actual = s.current.current.actual ∧
    (clearCell s c).current.current.synthetic = s.current.current.synthetic ∧
    (clearCell s c).current.current.addressed.outer = s.current.current.addressed.outer ∧
    (clearCell s c).pc = s.pc ∧ (clearCell s c).cursor = s.cursor ∧
    (clearCell s c).control = s.control := by
  rcases c with i | i | i | i | i | i | i | i | i | i | i | i | i | i | i | i | i | i <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem run_zero (s : State) (a b : Letter) : run s a b 0 = s := by
  simp only [run,Function.iterate_zero,id_eq]

private theorem run_one (s : State) (a b : Letter) : run s a b 1 = step s a b := by
  simp only [run,Function.iterate_one]

private theorem run_succ (s : State) (a b : Letter) (n : ℕ) :
    run s a b (n+1) = step (run s a b n) a b := by
  simp only [run,Function.iterate_succ_apply']

private theorem run_cons (s : State) (a b : Letter) (n : ℕ) :
    run s a b (n+1) = run (step s a b) a b n := by
  simp only [run,Function.iterate_succ_apply]

private theorem run_add (s : State) (a b : Letter) (m n : ℕ) :
    run s a b (m+n) = run (run s a b m) a b n := by
  simp only [run,Nat.add_comm m n,Function.iterate_add_apply]


def output (s : State) : Option Bool :=
  if s.pc = 0 then Current.output s.current else none

def trace (s : State) (a b : Letter) : ℕ → List Bool
  | 0 => []
  | n+1 => (output s).toList ++ trace (step s a b) a b n


/-- A pointwise prefix-erasure invariant for the actual single-cell loop. -/

private theorem erased_prefix (s : State) (hpc : s.pc = 2) (hc : s.cursor = 0)
    (n : ℕ) (hn : n ≤ scratchWidth) :
    let q := run s 0 0 n
    q.pc = 2 ∧ q.cursor.val = n ∧
    q.current.saved = s.current.saved ∧
    q.current.current.actual = s.current.current.actual ∧
    q.current.current.synthetic = s.current.current.synthetic ∧
    q.current.current.addressed.outer = s.current.current.addressed.outer ∧
    (∀ i : Fin scratchWidth, readCell q (cellCodec.symm i) =
      if i.val < n then false else readCell s (cellCodec.symm i)) := by
  induction n with
  | zero =>
      simp only [run,Function.iterate_zero,id_eq,hpc,hc,Fin.val_zero,
        not_lt_zero',↓reduceIte,true_and]
      exact fun _ => trivial
  | succ n ih =>
      have hh := ih (by omega)
      let p := run s 0 0 n
      have hbound : p.cursor.val < scratchWidth := by rw [hh.2.1]; omega
      let cell : Fin scratchWidth := ⟨p.cursor.val,hbound⟩
      have hs : step p 0 0 =
          {(clearCell p (cellCodec.symm cell)) with cursor := ⟨p.cursor.val+1,by omega⟩} := by
        have hpp : p.pc = 2 := hh.1
        simp [step,hpp,hbound,cell,clear_frame]
      have hf := clear_frame p (cellCodec.symm cell)
      have hrun : run s 0 0 (n+1) =
          {(clearCell p (cellCodec.symm cell)) with cursor := ⟨p.cursor.val+1,by omega⟩} := by
        rw [run_succ]
        exact hs
      rw [hrun]
      dsimp only
      refine ⟨hf.2.2.2.2.1.trans hh.1,?_,hf.1.trans hh.2.2.1,
        hf.2.1.trans hh.2.2.2.1,hf.2.2.1.trans hh.2.2.2.2.1,
        hf.2.2.2.1.trans hh.2.2.2.2.2.1,?_⟩
      · change p.cursor.val+1 = n+1
        rw [hh.2.1]
      · intro i
        change readCell (clearCell p (cellCodec.symm cell)) (cellCodec.symm i) = _
        rw [read_clear,hh.2.2.2.2.2.2 i]
        have he : (cellCodec.symm i = cellCodec.symm cell) ↔ i.val = n := by
          rw [cellCodec.symm.injective.eq_iff,Fin.ext_iff]
          change i.val = p.cursor.val ↔ i.val = n
          rw [hh.2.1]
        simp only [he]
        by_cases h : i.val = n
        · simp [h]
        · have hh : (i.val < n) ↔ (i.val < n+1) := by omega
          simp only [h,↓reduceIte,hh]

private def controlCheckpoint (s : State) (n : ℕ) (hn : n ≤ controlCount) : State :=
  {s with
    current := {s.current with
      current := {s.current.current with
        pre := {s.current.current.pre with
          probe := (if 0 < n then 0 else s.current.current.pre.probe),
          pc := (if 1 < n then .seek else s.current.current.pre.pc),
          latch := (if 2 < n then false else s.current.current.pre.latch)
        },
        result := {s.current.current.result with
          probe := (if 3 < n then 0 else s.current.current.result.probe),
          pc := (if 4 < n then .seek else s.current.current.result.pc),
          latch := (if 5 < n then false else s.current.current.result.latch)
        },
        fields := {s.current.current.fields with
          probe := (if 6 < n then 0 else s.current.current.fields.probe),
          pc := (if 7 < n then .seek else s.current.current.fields.pc),
          latch := (if 8 < n then false else s.current.current.fields.latch)
        },
        opcodes := {s.current.current.opcodes with
          probe := (if 9 < n then 0 else s.current.current.opcodes.probe),
          pc := (if 10 < n then .seek else s.current.current.opcodes.pc),
          latch := (if 11 < n then false else s.current.current.opcodes.latch)
        },
        addressed := {s.current.current.addressed with
          head := {s.current.current.addressed.head with
            probe := (if 12 < n then 0 else s.current.current.addressed.head.probe),
            pc := (if 13 < n then .seek else s.current.current.addressed.head.pc),
            latch := (if 14 < n then false else s.current.current.addressed.head.latch)
          },
          control := {s.current.current.addressed.control with
            baseProbe := (if 31 < n then 0 else s.current.current.addressed.control.baseProbe),
            keyProbe := (if 32 < n then 0 else s.current.current.addressed.control.keyProbe),
            strideProbe := (if 33 < n then 0 else s.current.current.addressed.control.strideProbe),
            offsetProbe := (if 34 < n then 0 else s.current.current.addressed.control.offsetProbe),
            pc := (if 35 < n then .baseTest else s.current.current.addressed.control.pc),
            returnBase := (if 36 < n then true else s.current.current.addressed.control.returnBase),
            returnStride := (if 37 < n then false else s.current.current.addressed.control.returnStride),
            latch := (if 38 < n then false else s.current.current.addressed.control.latch)
          }
        },
        key := {s.current.current.key with
          tail := (if 15 < n then 0 else s.current.current.key.tail),
          probe := (if 16 < n then 0 else s.current.current.key.probe),
          carry := (if 17 < n then 0 else s.current.current.key.carry),
          query := (if 18 < n then 0 else s.current.current.key.query),
          pc := (if 19 < n then 0 else s.current.current.key.pc)
        },
        row := {s.current.current.row with
          tail := (if 20 < n then 0 else s.current.current.row.tail),
          probe := (if 21 < n then 0 else s.current.current.row.probe),
          carry := (if 22 < n then 0 else s.current.current.row.carry),
          query := (if 23 < n then 0 else s.current.current.row.query),
          pc := (if 24 < n then 0 else s.current.current.row.pc)
        },
        native := {s.current.current.native with
          query := (if 25 < n then ⟨0,by unfold runtimeSize; omega⟩ else s.current.current.native.query),
          row := (if 26 < n then 0 else s.current.current.native.row),
          cursor := (if 27 < n then 0 else s.current.current.native.cursor),
          accumulator := (if 28 < n then 0 else s.current.current.native.accumulator),
          equalFlag := (if 29 < n then true else s.current.current.native.equalFlag),
          pc := (if 30 < n then 0 else s.current.current.native.pc)
        },
        role := (if 39 < n then false else s.current.current.role),
        operation := (if 40 < n then 0 else s.current.current.operation),
        slot := (if 41 < n then 0 else s.current.current.slot),
        offset := (if 42 < n then zeroOffset else s.current.current.offset),
        bankProbe := (if 43 < n then 0 else s.current.current.bankProbe),
        bankLatch := (if 44 < n then false else s.current.current.bankLatch),
        phase := (if 45 < n then 0 else s.current.current.phase)
      },
      acquiring := if 46 < n then false else s.current.acquiring},
    menu := {s.menu with
      probe := if 47 < n then 0 else s.menu.probe,
      pc := if 48 < n then .seek else s.menu.pc,
      latch := if 49 < n then false else s.menu.latch},
    pc := 3,control := ⟨n,by omega⟩}




private theorem control_cycle (s : State) (n : ℕ) (hn : n < controlCount) :
    step (controlCheckpoint s n (by omega)) 0 0 = controlCheckpoint s (n+1) (by omega) := by
  have h : n < 50 := hn
  interval_cases n <;> rfl



private theorem control_prefix (s : State) (n : ℕ) (hn : n ≤ controlCount) :
    run {s with pc := 3,control := 0} 0 0 n = controlCheckpoint s n hn := by
  induction n with
  | zero => rw [run_zero]; rfl
  | succ n ih =>
      rw [run_succ]
      change step (run {s with pc := 3,control := 0} 0 0 n) 0 0 = _
      rw [ih (by omega)]
      exact control_cycle s n (by omega)


private def normalized (s : State) : State :=
  {controlCheckpoint s controlCount le_rfl with pc := 4,cursor := 0,control := 0}



private theorem controls_execute (s : State) :
    run {s with pc := 3,control := 0} 0 0 (controlCount+1) = normalized s := by
  rw [run_succ]
  change step (run {s with pc := 3,control := 0} 0 0 controlCount) 0 0 = _
  rw [control_prefix s controlCount le_rfl]
  rfl



private theorem normalized_ready (s : State) (hz : ∀ c, readCell s c = false) :
    normalized s = coreReady s.current.saved s.current.current.addressed.outer
      s.current.current.actual s.current.current.synthetic := by
  apply State.ext
  · apply Current.State.ext
    · rfl
    · apply CurrentBank.State.ext
      · apply AddressState.ext
        · rfl
        · rfl
        · funext i
          exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))))
        · funext i
          exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))))))
        · apply Motor.ext
          · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))))))
          · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))))))))
          · rfl
          · rfl
          · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · apply Motor.ext
        · funext i; exact hz (.inl i)
        · funext i; exact hz (.inr (.inl i))
        · rfl
        · rfl
        · rfl
      · apply Key.ext
        · funext i; exact hz (.inr (.inr (.inl i)))
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
      · funext i; exact hz (.inr (.inr (.inr (.inl i))))
      · rfl
      · funext i; exact hz (.inr (.inr (.inr (.inr (.inl i)))))
      · apply Motor.ext
        · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inl i))))))
        · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))
        · rfl
        · rfl
        · rfl
      · apply Motor.ext
        · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))
        · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))
        · rfl
        · rfl
        · rfl
      · apply Key.ext
        · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · apply Motor.ext
        · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))
        · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))))))))
        · rfl
        · rfl
        · rfl
    · rfl
  · apply Motor.ext
    · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))))))))))))))
    · funext i; exact hz (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr i)))))))))))))))))
    · rfl
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl



private theorem retired_ready (s : State) (hp : s.pc = 0)
    (hr : s.current.current.phase = 11) :
    run s 0 0 (2+scratchWidth+1+(controlCount+1)) =
      coreReady s.current.saved s.current.current.addressed.outer
        s.current.current.actual s.current.current.synthetic := by
  let start : State := {s with pc := 2,cursor := 0}
  have hs : run s 0 0 2 = start := by simp [run,step,hp,hr,start]
  have he := erased_prefix start rfl rfl scratchWidth le_rfl
  generalize heq : run start 0 0 scratchWidth = erased at he
  have hz : ∀ c, readCell erased c = false := by
    intro c
    have h := he.2.2.2.2.2.2 (cellCodec c)
    simpa only [cellCodec.symm_apply_apply,Fin.isLt,↓reduceIte] using h
  have hc : step erased 0 0 = {erased with pc := 3,control := 0} := by
    have hn : ¬ erased.cursor.val < scratchWidth := by rw [he.2.1]; omega
    have hep : erased.pc = 2 := he.1
    simp [step,hep,hn]
  rw [run_add s 0 0 (2+scratchWidth+1) (controlCount+1),
    run_add s 0 0 (2+scratchWidth) 1,run_add s 0 0 2 scratchWidth,hs,heq,run_one]
  change run (step erased 0 0) 0 0 (controlCount+1) = _
  rw [hc,controls_execute,normalized_ready erased hz]
  exact by rw [he.2.2.1,he.2.2.2.2.2.1,he.2.2.2.1,he.2.2.2.2.1]




private theorem menu_rom (s : State) (z : Runtime)
    (ha : s.current.current.actual = word (runtimeCodec z)) :
    menuROM s = word (RarePriorResidentCode.controlCodec z.fields.control) := by
  funext i
  simp only [menuROM,ha,word]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  have hv : (runtimeCodec z).val =
      (RarePriorResidentCode.controlCodec z.fields.control).val*(56700*(6023*4))+
      (registersCodec z.fields.registers).val*(6023*4)+
      (monitorCodec z.monitor).val*4+(modeCodec z.mode).val := by
    change (finProdFinEquiv (finProdFinEquiv
      (RarePriorResidentCode.controlCodec z.fields.control,registersCodec z.fields.registers),
      finProdFinEquiv (monitorCodec z.monitor,modeCodec z.mode))).val = _
    simp only [finProdFinEquiv_apply_val]
    ring
  rw [hv]
  have := (registersCodec z.fields.registers).isLt
  have := (monitorCodec z.monitor).isLt
  have := (modeCodec z.mode).isLt
  omega


private theorem menu_exit (s : State) (n : ℕ) (hp : s.pc = 5)
    (he : (motorRun (menuROM s) s.menu n).pc = .halt) :
    ∃ t ≤ n+1, run s 0 0 t =
      {s with menu := motorRun (menuROM s) s.menu n,pc := 6} := by
  induction n generalizing s with
  | zero =>
      have hh : s.menu.pc = .halt := he
      exact ⟨1,by omega,by simp [run,step,hp,hh,motorRun]⟩
  | succ n ih =>
      by_cases hh : s.menu.pc = .halt
      · have hf : motorStep (menuROM s) s.menu = s.menu := by simp [motorStep,hh]
        exact ⟨1,by omega,by simp [run,step,hp,hh,motorRun,Function.iterate_fixed hf]⟩
      · let q : State := {s with menu := motorStep (menuROM s) s.menu}
        have hq : step s 0 0 = q := by simp [step,hp,hh,q]
        have hqe : (motorRun (menuROM q) q.menu n).pc = .halt := by
          rw [motorRun,Function.iterate_succ_apply] at he
          exact he
        obtain ⟨t,ht,heq⟩ := ih q hp hqe
        refine ⟨t+1,by omega,?_⟩
        rw [run_cons,hq,heq]
        have hrom : menuROM q = menuROM s := rfl
        rw [hrom]
        simp only [q,motorRun,Function.iterate_succ_apply]



private theorem ready_menu (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) (z : Runtime) (ha : a = word (runtimeCodec z)) :
    ∃ t, ∃ q : State, run (coreReady saved image a c) 0 0 t = q ∧ q.pc = 6 ∧
      q.current = (coreReady saved image a c).current ∧
      q.menu.tape = word (RarePriorResidentCode.controlCodec z.fields.control) := by
  let s : State := {coreReady saved image a c with pc := 5}
  have hrom := menu_rom s z ha
  have he := motor_return (word (RarePriorResidentCode.controlCodec z.fields.control))
  have hp : (motorRun (menuROM s) s.menu (copyTime 14)).pc = .halt := by
    rw [hrom]
    exact he.1
  obtain ⟨t,_,ht⟩ := menu_exit s (copyTime 14) rfl hp
  refine ⟨1+t,{s with menu := motorRun (menuROM s) s.menu (copyTime 14),pc := 6},?_,rfl,rfl,?_⟩
  · rw [run_add]
    have hh : run (coreReady saved image a c) 0 0 1 = s := by rw [run_one]; rfl
    rw [hh,ht]
  · change (motorRun (menuROM s) s.menu (copyTime 14)).tape = _
    rw [hrom]
    exact he.2

private theorem current_add (s : Current.State) (m n : ℕ) :
    Current.run s 0 0 (m+n) = Current.run (Current.run s 0 0 m) 0 0 n := by
  simp only [Current.run,Nat.add_comm m n,Function.iterate_add_apply]



private theorem native_prefix (s : State) (hp : s.pc = 0) (n : ℕ)
    (hbefore : ∀ k, k < n → (Current.run s.current 0 0 k).current.phase ≠ 11) :
    run s 0 0 n = {s with current := Current.run s.current 0 0 n} := by
  induction n with
  | zero => simp only [run_zero,Current.run,Function.iterate_zero,id_eq]
  | succ n ih =>
      have hi := ih (fun k hk => hbefore k (by omega))
      rw [run_succ]
      change step (run s 0 0 n) 0 0 = _
      rw [hi]
      have hn := hbefore n (by omega)
      simp only [step,hp,Fin.val_zero,hn,↓reduceIte]
      simp only [Current.run,Function.iterate_succ_apply']




private theorem current_fixed (s : Current.State) (ha : s.acquiring = false)
    (hp : s.current.phase = 11) : Current.step s 0 0 = s := by
  simp only [Current.step,ha,Bool.false_eq_true,↓reduceIte]
  have hf : CurrentBank.step s.current = s.current := by simp [CurrentBank.step,hp]
  rw [hf]
  apply Current.State.ext <;> first | rfl | exact ha.symm

/-- First-return time is proof-side only. The successor executes the retained
segment unchanged through that cut, without storing a clock. -/

private theorem native_join (p q : Current.State) (n : ℕ) (hp : p.acquiring = false)
    (he : Current.run p 0 0 n = q) (hq : q.current.phase = 11) :
    ∃ t, t ≤ n ∧ run (entry p) 0 0 t = entry q ∧
      Current.run p 0 0 t = q ∧
      (∀ k, k < t → (Current.run p 0 0 k).current.phase ≠ 11) := by
  have hex : ∃ t, (Current.run p 0 0 t).current.phase = 11 := ⟨n,by rw [he]; exact hq⟩
  let t := Nat.find hex
  have ht : (Current.run p 0 0 t).current.phase = 11 := Nat.find_spec hex
  have hle : t ≤ n := Nat.find_min' hex (by rw [he]; exact hq)
  have hbefore : ∀ k, k < t → (Current.run p 0 0 k).current.phase ≠ 11 := by
    intro k hk
    exact Nat.find_min hex hk
  have hj := native_prefix (entry p) rfl t hbefore
  have hacq : (Current.run p 0 0 t).acquiring = false := by
    rw [Current.passive_run p hp]; exact hp
  have hf : Current.step (Current.run p 0 0 t) 0 0 = Current.run p 0 0 t := by
    exact current_fixed _ hacq ht
  have heq : Current.run p 0 0 t = q := by
    rw [show n = t+(n-t) by omega,current_add] at he
    rw [Current.run,Function.iterate_fixed hf] at he
    exact he
  refine ⟨t,hle,?_,heq,hbefore⟩
  simpa only [heq,entry] using hj

/-- External original-menu semantics, absent from all transition inputs. -/
def gate (z : Runtime) (source : Letter) : Option Operation :=
  match z.fields.control with
  | .fourth (.pending b) => some (.stop b)
  | .fourth .delivered => none
  | _ => some (.read source)

private def menuRole (c : NativeControl) : Fin 4 :=
  match c with
  | .fourth (.pending b) => if b = 0 then 1 else 2
  | .fourth .delivered => 3
  | _ => 0

private theorem menu_class (c : NativeControl) :
    menuClass (word (RarePriorResidentCode.controlCodec c)) = menuRole c := by
  cases c with
  | seed a => cases a with
      | none => rfl
      | some b => fin_cases b <;> rfl
  | early t phase => fin_cases t <;> cases phase <;> rfl
  | fourth c => cases c with
      | active phase => cases phase <;> rfl
      | pending b => fin_cases b <;> rfl
      | delivered => rfl



private theorem copied_gate (s : State) (z : Runtime) (hp : s.pc = 6)
    (hc : s.menu.tape = word (RarePriorResidentCode.controlCodec z.fields.control))
    (x y : Letter) :
    (gate z x = none → (step s x y).pc = 8 ∧ actualRequest (step s x y) = false) ∧
    (∀ op, gate z x = some op →
      ∃ t : ℕ, (t = 1 ∨ t = 2) ∧
        ∃ q : State, run s x y t = q ∧ q.pc = 0 ∧
          q.current = {s.current with current := {s.current.current with operation := operationCodec op}}) := by
  have hm : menuClass s.menu.tape = menuRole z.fields.control := by rw [hc,menu_class]
  have active (hr : menuRole z.fields.control = 0) (hg : gate z x = some (.read x)) :
      (gate z x = none → (step s x y).pc = 8 ∧ actualRequest (step s x y) = false) ∧
      (∀ op, gate z x = some op → ∃ t : ℕ, (t = 1 ∨ t = 2) ∧
        ∃ q : State, run s x y t = q ∧ q.pc = 0 ∧
          q.current = {s.current with current := {s.current.current with operation := operationCodec op}}) := by
    have hs : step s x y = {s with pc := 7} := by simp only [step,hp,Fin.val_ofNat,hm,hr]; rfl
    constructor
    · intro h; rw [hg] at h; cases h
    · intro op h
      rw [hg] at h
      have ho : op = .read x := (Option.some.inj h).symm
      subst op
      refine ⟨2,Or.inr rfl,
        {s with pc := 0,current := {s.current with current := {s.current.current with operation := Fin.castAdd 2 x}}},
        ?_,rfl,rfl⟩
      rw [run_succ s x y 1,run_one]
      rw [hs]
      rfl
  cases hz : z.fields.control with
  | seed a => exact active (by simp only [hz,menuRole]) (by simp [gate,hz])
  | early t phase => exact active (by simp only [hz,menuRole]) (by simp [gate,hz])
  | fourth c => cases c with
      | active phase => exact active (by simp only [hz,menuRole]) (by simp [gate,hz])
      | pending b =>
          constructor
          · intro h; simp [gate,hz] at h
          · intro op h
            have ho : op = .stop b := (Option.some.inj (by simpa [gate,hz] using h)).symm
            subst op
            refine ⟨1,Or.inl rfl,
              {s with pc := 0,current := {s.current with current := {s.current.current with operation := operationCodec (.stop b)}}},
              ?_,rfl,rfl⟩
            rw [run_one]
            fin_cases b <;> simp only [step,hp,Fin.val_ofNat,hm,hz,menuRole] <;> rfl
      | delivered =>
          constructor
          · intro _
            have hs : step s x y = {s with pc := 8} := by
              simp only [step,hp,Fin.val_ofNat,hm,hz,menuRole]; rfl
            rw [hs]
            exact ⟨rfl,rfl⟩
          · intro op h; simp [gate,hz] at h

/-- The paid menu round retains the whole core-ready bank and launches only
its actual original menu operation. No supplied ready-role selector is used. -/
def MenuRound (r : State) (z : Runtime) : Prop :=
  ∃ t, ∃ m : State, run r 0 0 t = m ∧ m.pc = 6 ∧ m.current = r.current ∧
    m.menu.tape = word (RarePriorResidentCode.controlCodec z.fields.control) ∧
    (∀ x y : Letter,
      (gate z x = none → (step m x y).pc = 8 ∧ actualRequest (step m x y) = false) ∧
      (∀ op, gate z x = some op → ∃ u : ℕ, (u = 1 ∨ u = 2) ∧
        ∃ q : State, run m x y u = q ∧ q.pc = 0 ∧
          q.current = {r.current with current := {r.current.current with operation := operationCodec op}}))

private theorem menu_round (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) (z : Runtime) (ha : a = word (runtimeCodec z)) :
    MenuRound (coreReady saved image a c) z := by
  obtain ⟨t,m,hm,hp,hcurrent,hmenu⟩ := ready_menu saved image a c z ha
  refine ⟨t,m,hm,hp,hcurrent,hmenu,?_⟩
  intro x y
  have h := copied_gate m z hp hmenu x y
  rw [hcurrent] at h
  exact h

@[irreducible] def code (s : State) : List Bool :=
  Current.code s.current ++ motorCode s.menu ++ bitCode s.pc ++
    bitCode s.cursor ++ bitCode s.control

def width : ℕ := Current.width+motorWidth 14+9+(scratchWidth+1)+(controlCount+1)

@[irreducible] def staticImage : List Bool := Current.staticImage ++
  (List.ofFn (fun i : Fin 9 => bitCode i)).flatten ++
  (List.ofFn (fun i : Fin 50 => bitCode i)).flatten

def staticWidth : ℕ := Current.staticWidth+81+2500

private theorem static_length : staticImage.length = staticWidth := by
  simp only [staticImage,staticWidth,List.length_append,Current.static_length,
    LiveProducer.opcode_length]

def bound : ℕ := programWidth+staticWidth+width+1

private theorem code_length (s : State) : (code s).length = width := by
  simp only [code,width,List.length_append,Current.code_length,motor_code_length,bit_code_length]



private theorem code_injective : Function.Injective code := by
  intro s t h
  simp only [code,List.append_assoc] at h
  obtain ⟨hc,h⟩ := split_block (Current.code s.current) (Current.code t.current) _ _
    Current.width (Current.code_length _) (Current.code_length _) h
  obtain ⟨hm,h⟩ := split_block (motorCode s.menu) (motorCode t.menu) _ _
    (motorWidth 14) (motor_code_length _) (motor_code_length _) h
  obtain ⟨hp,h⟩ := split_block (bitCode s.pc) (bitCode t.pc) _ _
    9 (bit_code_length _) (bit_code_length _) h
  obtain ⟨hi,hk⟩ := split_block (bitCode s.cursor) (bitCode t.cursor) _ _
    (scratchWidth+1) (bit_code_length _) (bit_code_length _) h
  apply State.ext
  · exact Current.code_injective hc
  · exact motor_encoding hm
  · exact bit_code_injective hp
  · exact bit_code_injective hi
  · exact bit_code_injective hk


set_option maxHeartbeats 2000000 in
private theorem charged (s : State) :
    programImage.length+staticImage.length+(code s).length < bound := by
  simp only [programImage,List.length_ofFn,static_length,code_length,bound]
  omega

private theorem native_nonretired (s : State) (hp : s.pc = 0)
    (ha : s.current.acquiring = false) (n : ℕ)
    (hn : (Current.run s.current 0 0 n).current.phase ≠ 11) :
    run s 0 0 n = {s with current := Current.run s.current 0 0 n} := by
  apply native_prefix s hp n
  intro k hk hr
  let p := Current.run s.current 0 0 k
  have hpa : p.acquiring = false := by
    change (Current.run s.current 0 0 k).acquiring = false
    rw [Current.passive_run s.current ha]; exact ha
  have hf : Current.step p 0 0 = p := by
    exact current_fixed p hpa hr
  have he : Current.run s.current 0 0 n = p := by
    rw [show n = k+(n-k) by omega,current_add]
    exact Function.iterate_fixed hf (n-k)
  exact hn (by rw [he]; exact hr)



private theorem next_query (s : State) (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) (z : Runtime) (op : Operation)
    (hp : s.pc = 0) (hs : s.current = Current.entry saved image a c false (operationCodec op))
    (ha : a = word (runtimeCodec z)) :
    ∃ t, ∃ q : State, run s 0 0 t = q ∧ q.pc = 0 ∧ q.current.current.phase = 13 ∧
      q.current.current.query = word (nativeKeyCodec (z,op)) ∧
      q.current.current.actual = a ∧ q.current.current.synthetic = c ∧
      q.current.current.operation = operationCodec op := by
  obtain ⟨t,p,ht,hphase,hquery,_,hactual,hsynthetic,hop,_⟩ :=
    CurrentBank.bank_query image a c false z op (by simpa only [Bool.false_eq_true,↓reduceIte] using ha)
  have he : Current.run s.current 0 0 t = {s.current with current := p} := by
    rw [hs,Current.passive_run _ rfl]
    change {Current.entry saved image a c false (operationCodec op) with current := CurrentBank.run (CurrentBank.entry image a c false (operationCodec op)) t} = _
    rw [ht]
  have hacq : s.current.acquiring = false := by rw [hs]; rfl
  have hn : (Current.run s.current 0 0 t).current.phase ≠ 11 := by rw [he]; simp [hphase]
  have hrun := native_nonretired s hp hacq t hn
  refine ⟨t,{s with current := {s.current with current := p}},?_,hp,hphase,hquery,hactual,hsynthetic,hop⟩
  simpa only [he] using hrun

/-- The committed menu and its next bank query are executed on the same core.
The saved service and outer image context are not cleared by this relation. -/
def NextRound (r : State) (z : Runtime) : Prop :=
  ∃ t, ∃ m : State, run r 0 0 t = m ∧ m.pc = 6 ∧ m.current = r.current ∧
    m.menu.tape = word (RarePriorResidentCode.controlCodec z.fields.control) ∧
    (∀ x y : Letter,
      (gate z x = none → (step m x y).pc = 8 ∧ actualRequest (step m x y) = false) ∧
      (∀ op, gate z x = some op → ∃ u : ℕ, (u = 1 ∨ u = 2) ∧
        ∃ q : State, run m x y u = q ∧ q.pc = 0 ∧
          q.current = {r.current with current := {r.current.current with operation := operationCodec op}} ∧
          ∃ v, ∃ f : State, run q 0 0 v = f ∧ f.pc = 0 ∧ f.current.current.phase = 13 ∧
            f.current.current.query = word (nativeKeyCodec (z,op)) ∧
            f.current.current.actual = r.current.current.actual ∧
            f.current.current.synthetic = r.current.current.synthetic ∧
            f.current.current.operation = operationCodec op))




private theorem next_round (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) (z : Runtime) (ha : a = word (runtimeCodec z)) :
    NextRound (coreReady saved image a c) z := by
  obtain ⟨t,m,hm,hp,hcurrent,hmenu,hgate⟩ := menu_round saved image a c z ha
  refine ⟨t,m,hm,hp,hcurrent,hmenu,?_⟩
  intro x y
  constructor
  · exact (hgate x y).1
  · intro op hop
    obtain ⟨u,hu,q,hq,hqp,hqc⟩ := (hgate x y).2 op hop
    refine ⟨u,hu,q,hq,hqp,hqc,?_⟩
    have hentry : q.current = Current.entry saved image a c false (operationCodec op) := by
      rw [hqc]; rfl
    exact next_query q saved image a c z op hqp hentry ha

end LiveProducer.Return

/-- The successor-local return handshake erases every current-core scratch cell
and sets its rail controls before reading the committed bank's original menu.
Saved service and outer image scratch are retained, so this is core-ready only. -/

theorem current_bank_paid_core_return (saved : LiveProducer.State) (image : TransferSnapshot)
    (a c : Fin runtimeSize → Bool) (role : Bool) (z d : Runtime) (op : Operation)
    (himage : image.installation.tape = programTape)
    (hbank : (if role then c else a) = LiveProducer.word (runtimeCodec z))
    (hd : runtimeStep z op = some d) :
    Function.Injective LiveProducer.Return.code ∧
    (∀ s : LiveProducer.Return.State, programImage.length+LiveProducer.Return.staticImage.length+
      (LiveProducer.Return.code s).length < LiveProducer.Return.bound) ∧
    (∀ (s : LiveProducer.Return.State) (x y u v : Letter),
      LiveProducer.Return.actualRequest s = false →
        LiveProducer.Return.step s x y = LiveProducer.Return.step s u v) ∧
    ∃ t, ∃ r : LiveProducer.Return.State,
      LiveProducer.Return.run (LiveProducer.Return.entry
        (LiveProducer.Current.entry saved image a c role (operationCodec op))) 0 0 t = r ∧
      r = LiveProducer.Return.coreReady saved r.current.current.addressed.outer
        (if role then a else LiveProducer.word (runtimeCodec d))
        (if role then LiveProducer.word (runtimeCodec d) else c) ∧
      r.current.current.addressed.outer.installation.tape = programTape ∧
      (∀ w : Runtime, r.current.current.actual = LiveProducer.word (runtimeCodec w) →
        LiveProducer.Return.NextRound r w) := by
  obtain ⟨tp,p,tr,q,hp,hacq,hphase,hq,hret,ha,hc,_,_,hi,_⟩ :=
    current_bank_original_frames saved image a c role z d op himage hbank hd
  have hwhole : LiveProducer.Current.run
      (LiveProducer.Current.entry saved image a c role (operationCodec op)) 0 0 (tp+tr) = q := by
    rw [LiveProducer.Current.run,Nat.add_comm tp tr,Function.iterate_add_apply]
    change LiveProducer.Current.run
      (LiveProducer.Current.run
        (LiveProducer.Current.entry saved image a c role (operationCodec op)) 0 0 tp) 0 0 tr = q
    rw [hp,hq]
  obtain ⟨tn,_,hn,_,_⟩ := LiveProducer.Return.native_join _ q (tp+tr) rfl hwhole hret
  have hsaved : q.saved = saved := by
    have h := congrArg LiveProducer.Current.State.saved hwhole
    rw [LiveProducer.Current.passive_run _ rfl] at h
    exact h.symm
  let ready := LiveProducer.Return.coreReady saved q.current.addressed.outer
    (if role then a else LiveProducer.word (runtimeCodec d))
    (if role then LiveProducer.word (runtimeCodec d) else c)
  have hready : LiveProducer.Return.run (LiveProducer.Return.entry q) 0 0
      (2+LiveProducer.Return.scratchWidth+1+(LiveProducer.Return.controlCount+1)) = ready := by
    rw [LiveProducer.Return.retired_ready _ rfl hret]
    change LiveProducer.Return.coreReady q.saved q.current.addressed.outer q.current.actual q.current.synthetic = ready
    rw [hsaved,ha,hc]
  refine ⟨LiveProducer.Return.code_injective,LiveProducer.Return.charged,LiveProducer.Return.ports,
    tn+(2+LiveProducer.Return.scratchWidth+1+(LiveProducer.Return.controlCount+1)),ready,?_,rfl,hi,?_⟩
  · rw [LiveProducer.Return.run_add,hn,hready]
  · intro w hw
    exact LiveProducer.Return.next_round saved q.current.addressed.outer _ _ w hw


/-- The actual finite tagged producer consumes the unary key, native scanner,
encoded return-word copier and address subroutine on its active commit path.
This is a rail-model source transaction, not original COMPLETE membership:
header/slot scheduling, resident opcode fetch, live renderer-row preparation,
canonical ready reset and the full synthetic service refinement remain open. -/
theorem tagged_source_commit (s : TransferSnapshot) (op : Operation) (slot : Fin 6) (i : Fin frameWidth) :
    Function.Injective LiveProducer.code ∧
    (∀ q : LiveProducer.State, programImage.length+LiveProducer.staticImage.length+
      (LiveProducer.code q).length < LiveProducer.bound) ∧
    (∀ (q : LiveProducer.State) (a b c d : Letter),
      LiveProducer.actualRequest q = false → LiveProducer.freshRequest q = false →
      LiveProducer.step q a b = LiveProducer.step q c d) ∧
    (∀ (q : LiveProducer.State) (a b : Letter) (t : ℕ),
      (LiveProducer.run q a b t).addressed.outer.base.retained = q.addressed.outer.base.retained) ∧
    (∀ d : Runtime, runtimeStep s.base.retained.actual op = some d →
      (∃ t, ∃ q : LiveProducer.State,
        LiveProducer.run (LiveProducer.prepared s op slot i) 0 0 t = q ∧ q.stage = .returned ∧
        LiveProducer.returnedRuntime q = some d ∧ LiveProducer.returnedOperation q = some op ∧
        ∃ u ≤ t, LiveProducer.emitted (LiveProducer.run (LiveProducer.prepared s op slot i) 0 0 u) =
          some (frameTape (eventROM s.base.retained.actual.fields op slot) i)) ∧
      (∀ n : ℕ, let q := LiveProducer.run (LiveProducer.prepared s op slot i) 0 0 n
        q.stage ≠ .fault ∧ (q.stage ≠ .returned →
          LiveProducer.rank (LiveProducer.step q 0 0) < LiveProducer.rank q))) ∧
    (∀ (x : Letter) (d : Runtime), runtimeStep s.base.retained.actual (.read x) = some d →
      ∃ t, ∃ q : LiveProducer.State,
        LiveProducer.run (LiveProducer.step (LiveProducer.sourceEntry s slot i) x 0) 0 0 t = q ∧
        q.stage = .returned ∧ LiveProducer.returnedRuntime q = some d ∧
        LiveProducer.returnedOperation q = some (.read x)) := by
  refine ⟨LiveProducer.code_encoding,LiveProducer.charged,LiveProducer.ports,
    LiveProducer.saved_cuts,?_,
    (fun x d hd => LiveProducer.acquisition_commit s x slot i d hd)⟩
  intro d hd
  have he := LiveProducer.native_commit s op slot i d hd
  refine ⟨he,?_⟩
  obtain ⟨t,q,hq,hqs,_⟩ := he
  have hr : LiveProducer.Returns (LiveProducer.prepared s op slot i) := ⟨t,by rw [hq]; exact hqs⟩
  intro n
  have hn := LiveProducer.returns_after _ hr n
  exact ⟨LiveProducer.no_fault _ hn,LiveProducer.rank_step _ hn⟩


end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
