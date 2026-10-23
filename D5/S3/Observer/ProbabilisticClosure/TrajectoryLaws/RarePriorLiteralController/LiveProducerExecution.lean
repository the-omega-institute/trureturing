/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerExecution
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerExecution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Installed native payload execution connects source transactions to charged producer cuts. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.LiveProducerSetup

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option Elab.async false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
namespace LiveProducer
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder NativeFullResidual
open RarePriorFiniteMonitor RarePriorResidentCode RarePriorSerialExecution
open RarePriorFairBitService
theorem native_commit (s : TransferSnapshot) (op : Operation) (slot : Fin 6)
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



theorem acquisition_commit (s : TransferSnapshot) (x : Letter) (slot : Fin 6)
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

theorem returns_after (s : State) (h : Returns s) (n : ℕ) : Returns (run s 0 0 n) := by
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

theorem rank_step (s : State) (h : Returns s) (hp : s.stage ≠ .returned) :
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

theorem no_fault (s : State) (h : Returns s) : s.stage ≠ .fault := by
  intro hp
  obtain ⟨t,ht⟩ := h
  have hf : step s 0 0 = s := by simp [step,hp]
  have hs : run s 0 0 t = s := Function.iterate_fixed hf t
  rw [hs,hp] at ht
  cases ht



namespace CurrentBank

theorem tape_word {n : ℕ} (a : Fin n) :
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

theorem build_key_run (s : State) (n : ℕ)
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

theorem captured_key (s : State) (z : Runtime) (op : Operation)
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

theorem native_bit_correct (s : State)
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

theorem field_rom (s : State) (z : Runtime)
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

theorem actual_cuts (s : State) (hr : s.role = true) (n : ℕ) :
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

theorem opcode_rom (s : State)
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

theorem opcode_exit (s : State) (n : ℕ) (hs : s.phase = 13)
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

theorem opcode_decode (p : Fin 4) :
    decodeOpcode (opcodeTape p) 0 = (instructionGraph[p.val]).1 ∧
    decodeOpcode (opcodeTape p) 1 = (instructionGraph[p.val]).2.1 ∧
    decodeOpcode (opcodeTape p) 2 = (instructionGraph[p.val]).2.2 := by
  fin_cases p <;> decide

set_option maxHeartbeats 50000 in


theorem native_scan_refines (s : State)
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

theorem run_add (s : State) (m n : ℕ) :
    run s (m+n) = run (run s m) n := by
  simp only [run,Nat.add_comm m n,Function.iterate_add_apply]

theorem pre_exit (s : State) (n : ℕ) (hs : s.phase = 0)
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

theorem build_exit (s : State) (n : ℕ) (hs : s.phase = 1)
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

theorem build_key_frame (s : State) (n : ℕ) :
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


end CurrentBank
end LiveProducer
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
