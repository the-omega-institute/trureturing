/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerRendering
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerRendering
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Current-bank rendering streams all original frame words and writes the selected bank. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.LiveProducerWork

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

theorem scan_exit (s : State) (n : ℕ) (hs : s.phase = 2)
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

theorem prepare_event (r : State) (z d : Runtime)
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


theorem trace_add (s : State) (m n : ℕ) :
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

theorem row_emit (s : State) (f : FiniteFields) (op : Operation)
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

theorem render_commit (s : State) (z d : Runtime) (op : Operation)
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

theorem preparing_quiet (s p : State) (t : ℕ) (hp : run s t = p)
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

theorem retired_no_fault (s : State) (t : ℕ)
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


end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
