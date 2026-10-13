/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/CurrentAcquisition
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/CurrentAcquisition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Acquired operations reach native payload, original frames and selected-bank writeback. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController.LiveProducerRendering

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option Elab.async false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder NativeFullResidual
open RarePriorFiniteMonitor RarePriorResidentCode RarePriorSerialExecution
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
theorem static_length : staticImage.length = staticWidth := by
  simp only [staticImage,staticWidth,List.length_append,LiveProducer.static_length,
    LiveProducer.opcode_length]

def bound : ℕ := programWidth+staticWidth+width+1

theorem code_length (s : State) : (code s).length = width := by
  simp only [code,width,List.length_append,LiveProducer.code_length,CurrentBank.code_length,
    List.length_cons,List.length_nil]

theorem code_injective : Function.Injective code := by
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

theorem passive_run (s : State) (hs : s.acquiring = false) (a b : Letter) (n : ℕ) :
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



end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController
