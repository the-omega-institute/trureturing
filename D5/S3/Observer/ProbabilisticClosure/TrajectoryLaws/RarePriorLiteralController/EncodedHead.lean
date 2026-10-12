/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/EncodedHead
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/EncodedHead
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Encoded head scans and carries refine every finite ROM copy checkpoint. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.EventFrames

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option Elab.async false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder NativeFullResidual
open RarePriorFiniteMonitor RarePriorResidentCode RarePriorSerialExecution
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
theorem motor_seek {w : ℕ} (rom : Fin w → Bool) (m : ℕ) (hm : m ≤ w)
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

theorem motor_cycle {w : ℕ} (rom : Fin w → Bool) (m : ℕ) (hm : m < w) :
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

theorem motor_prefix {w : ℕ} (rom : Fin w → Bool) (m : ℕ) (hm : m ≤ w) :
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

theorem thermometer_count (n m : ℕ) (hm : m ≤ n) :
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

theorem head_control_step {w : ℕ} (rom : Fin w → Bool) (s : Motor w)
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

theorem motor_all_cuts {w : ℕ} (rom : Fin w → Bool) (ticks : ℕ) :
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

theorem motor_code_length {w : ℕ} (s : Motor w) : (motorCode s).length = motorWidth w := by
  simp only [motorCode,motorWidth,List.length_append,List.length_ofFn,bit_code_length]

theorem motor_encoding {w : ℕ} : Function.Injective (@motorCode w) := by
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

@[irreducible] def endMask (w : ℕ) : List Bool :=
  List.ofFn (fun i : Fin (w+1) => endCell i)

theorem end_mask_length (w : ℕ) : (endMask w).length = w+1 := by
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

theorem motor_static_length : motorStaticImage.length = motorStaticWidth := by
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


end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
