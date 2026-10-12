/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/EventFrames
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/EventFrames
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite event frames, paused tape copies and exact original history replay. -/

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

theorem copy_cycle {w : ℕ} (rom : Fin w → Bool) (m : ℕ) (hm : m < w) :
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

theorem trace_add {w : ℕ} (rom : Fin w → Bool) (s : CopyState w) (m n : ℕ) :
    copyTrace rom s (m+n) = copyTrace rom s m ++ copyTrace rom (copyRun rom s m) n := by
  induction m generalizing s with
  | zero => simp [copyTrace,copyRun]
  | succ m ih =>
    simp only [Nat.succ_add,copyTrace,ih,copyRun,Function.iterate_succ_apply,
      List.append_assoc]

theorem copy_prefix {w : ℕ} (rom : Fin w → Bool) (m : ℕ) (hm : m ≤ w) :
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

theorem tape_list {n : ℕ} (v : Fin n) :
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

theorem decode_code (e : Option Event) : decodeFrame (bitCode (frameCodec e)) = e := by
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

theorem copy_charge {w : ℕ} (s : CopyState w) : (copyCode s).length = copyWidth w := by
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

def rawProgramTape : Fin (B0+(headerWidth+(eventWidth+(25+64)))) → Bool :=
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

theorem split_block {α : Type} (a b : List α) (u v : List α) (n : ℕ)
    (ha : a.length = n) (hb : b.length = n) (h : a++u = b++v) : a=b ∧ u=v := by
  exact List.append_inj h (ha.trans hb.symm)

theorem snapshot_encoding : Function.Injective snapshot := by
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

theorem program_frame (s : RenderSnapshot) (slot : Fin 6) :
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


end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
