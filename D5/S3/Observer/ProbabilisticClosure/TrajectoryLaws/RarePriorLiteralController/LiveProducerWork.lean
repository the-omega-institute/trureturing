/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerWork
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerWork
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Current-bank work cycles copy native result fields and prepare original event rows. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.LiveProducerExecution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option Elab.async false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
namespace LiveProducer
namespace CurrentBank
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder NativeFullResidual
open RarePriorFiniteMonitor RarePriorResidentCode RarePriorSerialExecution
open RarePriorFairBitService
private def WorkSame (s q : State) : Prop :=
  q.pre = s.pre ∧ q.result = s.result ∧ q.fields = s.fields ∧
    q.slot = s.slot ∧ q.offset = s.offset

theorem build_key_work (s : State) (n : ℕ) : WorkSame s (buildKey^[n] s) := by
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

theorem bank_query (image : TransferSnapshot) (a c : Fin runtimeSize → Bool)
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

theorem write_complete (s : State) (d : Runtime)
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

theorem write_return (s : State) (d : Runtime)
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
def PayloadGood (v : Scanner (runtimeSize*4) (runtimeSize+1))
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

theorem payload_good_step (v : Scanner (runtimeSize*4) (runtimeSize+1))
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

theorem graph_query (v : Scanner (runtimeSize*4) (runtimeSize+1)) :
    (installedGraphStep nativeTable v).query = v.query := by
  unfold installedGraphStep scannerStep
  dsimp only
  repeat' first | rfl | split

theorem installed_payload_step (s : State)
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

def NativeFrame (s q : State) : Prop :=
  q = {s with native := q.native,payload := q.payload,phase := q.phase,opcodes := q.opcodes}

theorem native_frame_trans {s p q : State}
    (hsp : NativeFrame s p) (hpq : NativeFrame p q) : NativeFrame s q := by
  unfold NativeFrame at *
  rw [hpq,hsp]

theorem scan_frame (s : State) : NativeFrame s (scanStep s) := by
  unfold NativeFrame scanStep
  dsimp only
  repeat' first | rfl | split

theorem opcode_frame (s : State) (hs : s.phase = 13)
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


end CurrentBank
end LiveProducer
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
