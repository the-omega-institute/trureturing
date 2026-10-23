/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal native residuals retain written records and ordered original event blocks. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery
import D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open NativeConditionalControl.Prefix NativeConditionalControl.DepthLaw
open NativeConditionalControl.Tail NativeConditionalControl.Stopping
open FourthSegmentLawRecovery.Residual FourthSegmentLawRecovery.WordLaw
open FourthSegmentLawRecovery.Infinite
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction

/-- Events are generated from the old native fields, never supplied as extra input. -/
inductive OriginalEvent where
  | acquired (x : Letter)
  | rejected (x : Letter)
  | accepted (seed : Letter)
  | completed (index : ℕ) (bit : Letter)
  | written (fields : Registers)
  | latched (snapshot : Option ThirdSnapshot)
  | moved (control : NativeControl)
  | held (fields : Registers)
  | stopped (bit : Letter)
  deriving DecidableEq

instance : Countable OriginalEvent := by
  let code : OriginalEvent →
      Letter ⊕ Letter ⊕ Letter ⊕ (ℕ × Letter) ⊕ Registers ⊕
        Option ThirdSnapshot ⊕ NativeControl ⊕ Registers ⊕ Letter := fun e => match e with
    | .acquired x => .inl x
    | .rejected x => .inr (.inl x)
    | .accepted x => .inr (.inr (.inl x))
    | .completed n b => .inr (.inr (.inr (.inl (n,b))))
    | .written r => .inr (.inr (.inr (.inr (.inl r))))
    | .latched b => .inr (.inr (.inr (.inr (.inr (.inl b)))))
    | .moved c => .inr (.inr (.inr (.inr (.inr (.inr (.inl c))))))
    | .held r => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl r)))))))
    | .stopped b => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr b)))))))
  exact Function.Injective.countable (f := code) (by
    intro e f h
    cases e <;> cases f <;> simp_all [code])

/-- The post-write fields retain the old latch until the latch event. -/
def beforeLatch (r : Registers) (t : ℕ) (b : Letter) : Registers :=
  { writeMarker r t b with snapshot := r.snapshot }

/-- A completion writes the records before its latch. The fourth completion holds
    the snapshot, Q-plus and Z and enters the matching pending Stop. -/
def completionEvents (f : FiniteFields) (t : ℕ) (b : Letter) : List OriginalEvent :=
  [.completed t b, .written (beforeLatch f.registers t b)] ++
    (if t = 2 then [.latched (writeMarker f.registers t b).snapshot] else []) ++
    [.moved (completionControl t b), .held (writeMarker f.registers t b)]

def payloadEvents (f : FiniteFields) (t : ℕ) (s : ActivePhase) (x : Letter) :
    List OriginalEvent :=
  match s with
  | .p => if x = 0 then completionEvents f t 0
      else [.moved (payloadControl t .beta), .held f.registers]
  | .beta => if x = 0 then [.moved (payloadControl t .p), .held f.registers]
      else completionEvents f t 1

/-- Literal deterministic blocks for the original paid parser and Stop. -/
def eventBlock (f : FiniteFields) : Operation → List OriginalEvent
  | .stop b => [.stopped b, .moved (.fourth .delivered), .held f.registers]
  | .read x => .acquired x :: match f.control with
    | .seed none => [.moved (.seed (some x)), .held f.registers]
    | .seed (some y) => if x = y then
        [.rejected x, .moved (.seed none), .held f.registers]
      else [.accepted y, .written ({ f.registers with seed := some y, weight := 0, syndrome := some (1+y) }), .moved (payloadControl 0 .p)]
    | .early t s => payloadEvents f t.val s x
    | .fourth (.active s) => payloadEvents f 3 s x
    | .fourth (.pending _) | .fourth .delivered => []

def eventBlocks (f : FiniteFields) : List Operation → List (List OriginalEvent)
  | [] => []
  | op :: ops => eventBlock f op ::
      match finiteStep f op with
      | none => []
      | some d => eventBlocks d ops

/-- The original fields, fixed selector and actual permission menu read from a cut.
    This view introduces no memory or analysis counter. -/
def originalView (f : FiniteFields) :
    ℕ × ℕ × List Letter × Option (Letter × ℕ × ℕ × Fin 5 × Letter) ×
      Bool × Bool × (Operation → Prop) :=
  (2, 4, recoverMarkers f,
    f.registers.snapshot.map fun b => (b.seed, 2, 3, b.weight, b.syndrome),
    decide (0 < completedCount f.control), f.registers.snapshot.isSome,
    fun op => (finiteStep f op).isSome)

/-- Replaying deterministic events updates only the original finite fields. -/
def replayEvent (f : FiniteFields) : OriginalEvent → FiniteFields
  | .written r | .held r => { f with registers := r }
  | .latched b => { f with registers.snapshot := b }
  | .moved c => { f with control := c }
  | _ => f

def replayBlock (f : FiniteFields) (b : List OriginalEvent) : FiniteFields :=
  b.foldl replayEvent f

private theorem eventBlock_replays (f d : FiniteFields) (op : Operation)
    (h : finiteStep f op = some d) : replayBlock f (eventBlock f op) = d := by
  rcases f with ⟨control, r⟩
  cases op with
  | stop b =>
    cases control <;> simp [finiteStep, finiteStop] at h
    rename_i c
    cases c <;> simp [finiteStop] at h
    obtain ⟨_, hd⟩ := h
    subst d
    rfl
  | read x =>
    cases control with
    | seed first =>
      cases first with
      | none =>
        have hd : { control := .seed (some x), registers := r } = d := by
          simpa [finiteStep, finiteRead] using h
        rw [← hd]
        rfl
      | some y =>
        by_cases hx : x = y <;>
          simp [finiteStep, finiteRead, hx] at h <;> subst d <;>
          simp [eventBlock, hx, replayBlock, replayEvent]
    | early t s =>
      have hd : payloadRead ⟨.early t s, r⟩ t.val s x = d := by
        simpa [finiteStep, finiteRead] using h
      rw [← hd]
      cases s <;> by_cases hx : x = 0 <;>
        simp [eventBlock, payloadEvents, payloadRead, hx, replayBlock,
          replayEvent, completionEvents, beforeLatch] <;> split_ifs <;> rfl
    | fourth c =>
      cases c with
      | active s =>
        have hd : payloadRead ⟨.fourth (.active s), r⟩ 3 s x = d := by
          simpa [finiteStep, finiteRead] using h
        rw [← hd]
        cases s <;> by_cases hx : x = 0 <;>
          simp [eventBlock, payloadEvents, payloadRead, hx, replayBlock,
            replayEvent, completionEvents, beforeLatch]
      | pending b => simp [finiteStep, finiteRead] at h
      | delivered => simp [finiteStep, finiteRead] at h

private theorem execute_blocks (c d : AcquiredNativeState) (ops : List Operation)
    (h : execute c ops = some d) :
    (eventBlocks c.source.finiteFields ops).foldl replayBlock c.source.finiteFields =
      d.source.finiteFields := by
  induction ops generalizing c with
  | nil => simpa [execute, eventBlocks] using congrArg (fun e => e.source.finiteFields) (Option.some.inj h)
  | cons op ops ih =>
    obtain ⟨e, he, hd⟩ := Option.bind_eq_some_iff.mp h
    have hf : finiteStep c.source.finiteFields op = some e.source.finiteFields := by
      rw [← finite_projection_commutes, he]
      rfl
    simp only [eventBlocks, hf, List.foldl_cons]
    rw [eventBlock_replays _ _ op hf]
    exact ih e hd

abbrev FullOutput := Option (List Operation × FiniteFields × List (List OriginalEvent))
instance : MeasurableSpace FullOutput := ⊤
instance : MeasurableSingletonClass FullOutput := ⟨fun _ => trivial⟩
abbrev FullTranscript := ℕ → FullOutput

/-- Every finite prefix records its complete original fields and each original block.
    Paid counts and return counters are deliberately absent from this output. -/
def fullTranscript (c : AcquiredNativeState) (ω : Stream) : FullTranscript := fun n =>
  (nativeDrive c ω n).map fun r =>
    (r.1, r.2.1.source.finiteFields, eventBlocks c.source.finiteFields r.1)

/-- Every lawful prefix reconstructs the original held fields and permission menu
    by its actual event blocks, including write-before-latch. -/
theorem full_event_reconstruction (c d : AcquiredNativeState) (ω : Stream)
    (n k : ℕ) (ops : List Operation) (h : nativeDrive c ω n = some (ops, d, k)) :
    fullTranscript c ω n =
      some (ops, d.source.finiteFields, eventBlocks c.source.finiteFields ops) ∧
    (eventBlocks c.source.finiteFields ops).foldl replayBlock c.source.finiteFields =
      d.source.finiteFields ∧
    originalView ((eventBlocks c.source.finiteFields ops).foldl
      replayBlock c.source.finiteFields) = originalView d.source.finiteFields := by
  have he := execute_blocks c d ops ((drive_spec n c d ω ops k).mp h).2.1
  exact ⟨by simp [fullTranscript, h], he, congrArg originalView he⟩

def projectControl (t : FullTranscript) : NativeConditionalControl.Control.Transcript :=
  fun n => (t n).map fun r => (r.1,r.2.1.control)

private theorem project_full (c : AcquiredNativeState) (ω : Stream) :
    projectControl (fullTranscript c ω) = transcript c ω := by
  funext n
  simp [projectControl, fullTranscript, transcript, NativeConditionalControl.Control.visible,
    Option.map_map, Function.comp_def]

/-- Removing an operation removes its entire deterministic event block. -/
def deleteBlock (t : FullTranscript) : FullTranscript := fun n =>
  (t (n+1)).map fun r => (r.1.tail,r.2.1,r.2.2.tail)

theorem full_delete_block (c d : AcquiredNativeState) (ω : Stream) (op : Operation)
    (hn : nextNative c ω = some (op,d)) :
    deleteBlock (fullTranscript c ω) = fullTranscript d (rawTail ω (readCost op)) := by
  have hs : nativeStep c op = some d := by
    unfold nextNative at hn
    obtain ⟨o,ho,he⟩ := Option.bind_eq_some_iff.mp hn
    obtain ⟨f,hf,hfd⟩ := Option.map_eq_some_iff.mp he
    have hp : o = op ∧ f = d := Prod.mk.inj hfd
    simpa [hp.1,hp.2] using hf
  have hf : finiteStep c.source.finiteFields op = some d.source.finiteFields := by
    rw [← finite_projection_commutes,hs]
    rfl
  funext n
  simp [deleteBlock,fullTranscript,nativeDrive,hn,Option.map_map,Function.comp_def,
    eventBlocks,hf]

/-- Legal finite completion words and the unique infinite noncompletion word. -/
def Valid (s : ActivePhase) : RawTail → Prop
  | none => True
  | some w => ∃ b : Letter, WordFamily s b w
abbrev ValidTail (s : ActivePhase) := {t : RawTail // Valid s t}

def tailStream (s : ActivePhase) : RawTail → Stream
  | none => infiniteTail s
  | some w => wordStream w

def fullRenderer (c : AcquiredNativeState) (s : ActivePhase) (t : ValidTail s) : FullTranscript :=
  fullTranscript c (tailStream s t.val)

private theorem stopped_full (c : AcquiredNativeState) (s : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s)) (ω : Stream)
    (w : List Letter) (hw : stoppedReadWord s ω = some w) :
    fullTranscript c ω = fullTranscript c (wordStream w) := by
  have hp := (stopped_word_fiber s ω w).mp hw
  have hq := word_stream_prefix w
  have hw' : stoppedReadWord s (wordStream w) = some w :=
    (stopped_word_fiber s _ w).mpr ⟨hq,hp.2⟩
  have hlast : nativeDrive c ω (w.length+1) = nativeDrive c (wordStream w) (w.length+1) := by
    have hn := native_renderer_eq c s hs ω
    have hn' := native_renderer_eq c s hs (wordStream w)
    simp only [nativeStopped,hw,hw',Option.bind_some] at hn hn'
    exact hn.trans hn'.symm
  obtain ⟨b,d,hf,hd,hdel⟩ := (native_stopped_iff c s hs ω w).mp hw
  funext n
  unfold fullTranscript
  congr 1
  by_cases hn : n ≤ w.length
  · exact drive_prefix_input c ω (wordStream w) n
      (fun i hi => prefix_agrees ω _ w hp.1 hq i (by omega))
  · by_cases he : n = w.length+1
    · exact he ▸ hlast
    · have hh : n = w.length+1+((n-(w.length+1)-1)+1) := by omega
      rw [hh,drive_append c ω (w.length+1),
        drive_append c (wordStream w) (w.length+1),hd,← hlast,hd]
      simp [delivered_positive_none d hdel]

theorem full_renderer_all_paths (c : AcquiredNativeState) (s : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s)) (ω : Stream) :
    fullTranscript c ω = fullTranscript c (tailStream s (stoppedReadWord s ω)) := by
  cases hw : stoppedReadWord s ω with
  | none => simp only [tailStream]; rw [← (noncompletion_fiber s ω).mp hw]
  | some w => exact stopped_full c s hs ω w hw

/-- Read back precisely the letters at the unique delivered cut, or noncompletion. -/
def readbackRaw (t : FullTranscript) : RawTail := by
  classical
  let v := projectControl t
  exact if h : complete v then
    (t (Nat.find h)).map (fun r => readLetters r.1) else none

private theorem readback_measurable : Measurable readbackRaw := by
  classical
  let H : Set FullTranscript := {t | complete (projectControl t)}
  have hd (n : ℕ) : MeasurableSet {t : FullTranscript | deliveredAt (projectControl t) n} := by
    apply (show MeasurableSet {o : FullOutput |
      ∃ ops, o.map (fun r => (r.1,r.2.1.control)) = some (ops,.fourth .delivered)} from trivial).preimage
    exact measurable_pi_apply n
  have hh : MeasurableSet H := by
    simp only [H,complete,Set.setOf_exists]
    exact MeasurableSet.iUnion hd
  have hf : Measurable (fun t : H => (t.val (Nat.find t.property)).map
      (fun r => readLetters r.1)) :=
    Measurable.find (fun n => (measurable_of_countable
      (fun o : FullOutput => o.map (fun r => readLetters r.1))).comp
      ((measurable_pi_apply n).comp measurable_subtype_coe))
      (fun n => (hd n).preimage measurable_subtype_coe) (fun t => t.property)
  exact Measurable.dite hf measurable_const hh

private theorem readback_actual (c : AcquiredNativeState) (s : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s)) (ω : Stream) :
    readbackRaw (fullTranscript c ω) = stoppedReadWord s ω := by
  classical
  cases hw : stoppedReadWord s ω with
  | none =>
    have hω := (noncompletion_fiber s ω).mp hw
    have hc : ¬ complete (transcript c ω) := by
      rintro ⟨n,ops,hv⟩
      obtain ⟨⟨ops',d,paid⟩,hd,hp⟩ := Option.map_eq_some_iff.mp hv
      exact (infinite_tail_native_noncompletion c s hs).2 n
        ⟨ops',d,paid,by simpa [hω] using hd,(Prod.mk.inj hp).2⟩
    simp [readbackRaw,project_full,hc,hw]
  | some w =>
    have h : complete (transcript c ω) :=
      ⟨w.length+1,(terminal_index c s hs ω w hw _).mpr rfl⟩
    have hn : Nat.find h = w.length+1 :=
      (terminal_index c s hs ω w hw _).mp (Nat.find_spec h)
    obtain ⟨b,d,hf,hd,_⟩ := (native_stopped_iff c s hs ω w).mp hw
    simp [readbackRaw,project_full,h,hn,fullTranscript,hd,erase_reads,readLetters,hw]

theorem full_renderer_readback (c : AcquiredNativeState) (s : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s)) (t : ValidTail s) :
    readbackRaw (fullRenderer c s t) = t.val := by
  rw [fullRenderer,readback_actual c s hs]
  rcases t with ⟨t,ht⟩
  cases t with
  | none => exact (noncompletion_fiber _ _).mpr rfl
  | some w => exact (stopped_word_fiber s _ w).mpr ⟨word_stream_prefix w,ht⟩

private def readback (s : ActivePhase) (t : FullTranscript) : ValidTail s := by
  classical
  exact if h : Valid s (readbackRaw t) then ⟨readbackRaw t,h⟩ else ⟨none, trivial⟩

private theorem readback_valid_measurable (s : ActivePhase) : Measurable (readback s) := by
  classical
  have hv : MeasurableSet {u : FullTranscript | Valid s (readbackRaw u)} :=
    (Set.to_countable {w : RawTail | Valid s w}).measurableSet.preimage readback_measurable
  let f : {u : FullTranscript // Valid s (readbackRaw u)} → ValidTail s :=
    fun u => ⟨readbackRaw u.val, u.property⟩
  have hf : Measurable f := (readback_measurable.comp measurable_subtype_coe).subtype_mk
  convert (Measurable.dite hf
    (measurable_const (a := (⟨none, trivial⟩ : ValidTail s))) hv) using 1
  funext t
  dsimp only [readback, f, Set.mem_ofPred_eq]
  split_ifs
  · rfl
  · rename_i hvalid hmem
    exact False.elim (hmem hvalid)
  · rename_i hvalid hmem
    exact False.elim (hvalid hmem)
  · rfl

private theorem readback_left (c : AcquiredNativeState) (s : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s)) :
    Function.LeftInverse (readback s) (fullRenderer c s) := by
  intro t
  apply Subtype.ext
  simp [readback,full_renderer_readback c s hs t,t.property]

theorem full_renderer_tv (c : AcquiredNativeState) (s : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s))
    (P Q : Measure (ValidTail s)) :
    measurableTotalVariation (P.map (fullRenderer c s)) (Q.map (fullRenderer c s)) =
      measurableTotalVariation P Q := by
  have hf : Measurable (fullRenderer c s) := measurable_of_countable _
  have hb := readback_valid_measurable s
  refine le_antisymm (measurable_total_variation_map_le P Q _ hf) ?_
  have h := measurable_total_variation_map_le (P.map (fullRenderer c s))
    (Q.map (fullRenderer c s)) (readback s) hb
  have hi : (readback s) ∘ (fullRenderer c s) = id :=
    funext (readback_left c s hs)
  simpa only [Measure.map_map hb hf,hi,Measure.map_id] using h

#print axioms full_event_reconstruction
#print axioms full_delete_block
#print axioms full_renderer_all_paths
#print axioms full_renderer_readback
#print axioms full_renderer_tv

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual
