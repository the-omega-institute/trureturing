/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeStoppedTailRegeneration
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeStoppedTailRegeneration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: First completion commutes with a noncompleting read including infinite noncompletion. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRow
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeStoppedTailRegeneration
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open FourthSegmentStoppedLaw NativeInstalledFullLaw
open NativeAcquiredPrefixState NativeObserverJointLaw
open NativeFullResidual NativePaidHistoryCommonRow
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction

def consStream (b : Letter) (ω : Stream) : Stream
  | 0 => b
  | n+1 => ω n

private theorem prefix_cons (b : Letter) (ω : Stream) (w : List Letter) (a : Letter) :
    Prefix (consStream b ω) (a :: w) ↔ a = b ∧ Prefix ω w := by
  simp [Prefix, readPrefix, List.ofFn_succ, consStream, eq_comm]

private theorem finite_cons (s t : ActivePhase) (b : Letter)
    (hstep : totalRead (.active s) b = .active t) (ω : Stream) (v : List Letter) :
    stoppedReadWord s (consStream b ω) = some v ↔
      ∃ w, v = b :: w ∧ stoppedReadWord t ω = some w := by
  rw [stopped_word_fiber]
  cases v with
  | nil =>
    constructor
    · rintro ⟨_,c,hc⟩
      have h := (parses_normal_form s [] c).mpr hc
      simp [Parses, pendingColor] at h
    · rintro ⟨w,hw,_⟩
      cases hw
  | cons a v =>
    rw [prefix_cons]
    constructor
    · rintro ⟨⟨ha,hp⟩,c,hc⟩
      subst a
      have h := (parses_normal_form s (b :: v) c).mpr hc
      have ht : Parses (.active t) v c := by simpa [Parses, pendingColor, hstep] using h
      exact ⟨v,rfl,(stopped_word_fiber t ω v).mpr
        ⟨hp,c,(parses_normal_form t v c).mp ht⟩⟩
    · rintro ⟨w,he,hw⟩
      obtain ⟨ha,hv⟩ := List.cons.inj he
      subst a
      subst v
      obtain ⟨hp,c,hc⟩ := (stopped_word_fiber t ω w).mp hw
      refine ⟨⟨rfl,hp⟩,c,(parses_normal_form s (b :: w) c).mp ?_⟩
      simpa [Parses, pendingColor, hstep] using (parses_normal_form t w c).mpr hc

private theorem stopped_cons_continue (s t : ActivePhase) (b : Letter)
    (hstep : totalRead (.active s) b = .active t) (ω : Stream) :
    stoppedReadWord s (consStream b ω) =
      Option.map (List.cons b) (stoppedReadWord t ω) := by
  cases ht : stoppedReadWord t ω with
  | some w =>
    exact (finite_cons s t b hstep ω (b :: w)).mpr ⟨w,rfl,ht⟩
  | none =>
    cases hs : stoppedReadWord s (consStream b ω) with
    | none => rfl
    | some v =>
      obtain ⟨w,_,hw⟩ := (finite_cons s t b hstep ω v).mp hs
      rw [ht] at hw
      cases hw

/-- Both continuation identities retain the never-completing outcome. -/
theorem stopped_read_cons (ω : Stream) :
    stoppedReadWord .p (consStream 0 ω) = some [0] ∧
    stoppedReadWord .beta (consStream 1 ω) = some [1] ∧
    stoppedReadWord .p (consStream 1 ω) =
      Option.map (List.cons 1) (stoppedReadWord .beta ω) ∧
    stoppedReadWord .beta (consStream 0 ω) =
      Option.map (List.cons 0) (stoppedReadWord .p ω) := by
  refine ⟨?_,?_,stopped_cons_continue .p .beta 1 rfl ω,
    stopped_cons_continue .beta .p 0 rfl ω⟩
  · apply (stopped_word_fiber .p (consStream 0 ω) [0]).mpr
    exact ⟨by simp [Prefix,readPrefix,consStream],0,0,rfl⟩
  · apply (stopped_word_fiber .beta (consStream 1 ω) [1]).mpr
    exact ⟨by simp [Prefix,readPrefix,consStream],1,Or.inl ⟨rfl,rfl⟩⟩

universe u
variable {Z : Type u} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- The projection retains all finite words and the noncompletion atom. -/
def rawTailLaw (M : Observer Z) (e : InstalledEmitter M) (s : ActivePhase) (z : Z) :
    Measure RawTail := (tailLaw M e s z).map Subtype.val

instance (M : Observer Z) (e : InstalledEmitter M) (s : ActivePhase) (z : Z) :
    IsProbabilityMeasure (rawTailLaw M e s z) :=
  Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

private theorem raw_tail_map (M : Observer Z) (e : InstalledEmitter M)
    (s : ActivePhase) (z : Z) :
    rawTailLaw M e s z =
      (markedLaw M e (z,none)).map (fun x => stoppedReadWord s (rawFrom x)) := by
  unfold rawTailLaw tailLaw
  rw [Measure.map_map (measurable_of_countable _) (by fun_prop)]
  rfl

private theorem stopped_mark_irrelevance (M : Observer Z) (e : InstalledEmitter M)
    (s : ActivePhase) (z : Z) (a : Option Operation) :
    (markedLaw M e (z,a)).map (fun x => stoppedReadWord s (rawFrom x)) =
      rawTailLaw M e s z := by
  rw [raw_tail_map,marked_regenerate M e (z,a),marked_regenerate M e (z,none)]
  have hm : Measurable (fun x : ℕ → Marked Z => stoppedReadWord s (rawFrom x)) :=
    (measurable_stopped_read_word s).comp rawFrom_measurable
  rw [Measure.map_finset_sum' hm.aemeasurable,Measure.map_finset_sum' hm.aemeasurable]
  simp only [Measure.map_smul]
  apply Finset.sum_congr rfl
  intro v _
  rw [Measure.map_map hm (measurable_prepend _),
    Measure.map_map hm (measurable_prepend _)]
  rfl

private theorem raw_prepend_read (w : Marked Z) (x : ℕ → Marked Z) (b : Letter)
    (hx : (x 0).2 = some (.read b)) :
    rawFrom (prepend w x) = consStream b (rawFrom x) := by
  funext n
  cases n <;> simp [rawFrom,prepend,consStream,hx]

private theorem active_none (M : Observer Z) (e : InstalledEmitter M)
    (s : ActivePhase) (z : Z) (hz : (M.project z).control = .fourth (.active s)) :
    e.emit z none = 0 := by
  by_contra h
  have hl := e.lawful z none ((PMF.mem_support_iff _ _).mpr h)
  simp [hz] at hl

private theorem active_stop (M : Observer Z) (e : InstalledEmitter M)
    (s : ActivePhase) (z : Z) (hz : (M.project z).control = .fourth (.active s))
    (b : Letter) : e.emit z (some (.stop b)) = 0 := by
  by_contra h
  have hl := e.lawful z (some (.stop b)) ((PMF.mem_support_iff _ _).mpr h)
  simp [finiteStep,finiteStop,hz] at hl

private theorem sum_operations {T : Type*} [AddCommMonoid T] (f : Operation → T) :
    ∑ op, f op = (∑ b : Letter, f (.read b)) + ∑ b : Letter, f (.stop b) := by
  classical
  have hu : (Finset.univ : Finset Operation) =
      {.read 0,.read 1,.stop 0,.stop 1} := by decide
  rw [hu]
  simp [Fin.sum_univ_two, add_assoc]

def residualPhase : ActivePhase → ActivePhase
  | .p => .beta
  | .beta => .p

def nextStopped (s : ActivePhase) (b : Letter) (r : RawTail) : RawTail :=
  match s with
  | .p => if b = 0 then some [0] else Option.map (List.cons 1) r
  | .beta => if b = 0 then Option.map (List.cons 0) r else some [1]

private theorem stopped_cons_next (s : ActivePhase) (b : Letter) (ω : Stream) :
    stoppedReadWord s (consStream b ω) =
      nextStopped s b (stoppedReadWord (residualPhase s) ω) := by
  obtain ⟨h0,h1,h2,h3⟩ := stopped_read_cons ω
  cases s <;> fin_cases b <;> simp_all [nextStopped,residualPhase]

private theorem stopped_read_pushforward (M : Observer Z) (e : InstalledEmitter M)
    (s : ActivePhase) (z z' : Z) (b : Letter) :
    (markedLaw M e (z',some (.read b))).map
      (fun x => stoppedReadWord s (rawFrom (prepend (z,none) x))) =
      (rawTailLaw M e (residualPhase s) z').map (nextStopped s b) := by
  rw [← stopped_mark_irrelevance M e (residualPhase s) z' (some (.read b)),
    Measure.map_map (f := fun x : ℕ → Marked Z =>
      stoppedReadWord (residualPhase s) (rawFrom x))
      (g := nextStopped s b) (measurable_of_countable _)
      ((measurable_stopped_read_word (residualPhase s)).comp rawFrom_measurable)]
  apply Measure.map_congr
  filter_upwards [marked_head M e (z',some (.read b))] with x hx
  rw [raw_prepend_read _ x b (by rw [hx]),stopped_cons_next]
  rfl

/-- Regeneration is an equality of complete measures, so it includes the none event. -/
private theorem raw_tail_regenerate (M : Observer Z) (e : InstalledEmitter M)
    (s : ActivePhase) (z : Z) (hz : (M.project z).control = .fourth (.active s)) :
    rawTailLaw M e s z =
      ∑ b : Letter, e.emit z (some (.read b)) •
        ∑ z' : Z, M.update (.read b) z z' •
          (rawTailLaw M e (residualPhase s) z').map (nextStopped s b) := by
  rw [raw_tail_map,marked_regenerate]
  have hm : Measurable (fun x : ℕ → Marked Z => stoppedReadWord s (rawFrom x)) :=
    (measurable_stopped_read_word s).comp rawFrom_measurable
  rw [Measure.map_finset_sum' hm.aemeasurable]
  simp only [Measure.map_smul]
  simp_rw [Measure.map_map hm (measurable_prepend _)]
  simp only [Function.comp_def]
  have hn (z' : Z) : markedRow M e (z,none) (z',none) = 0 := by
    simp [markedRow,PMF.bind_apply,PMF.map_apply,PMF.pure_apply,
      Prod.mk.injEq,active_none M e s z hz]
  simp only [Fintype.sum_prod_type,Fintype.sum_option,hn,zero_smul,zero_add]
  simp_rw [sum_operations,marked_some_mass,active_stop M e s z hz,
    zero_mul,zero_smul,Finset.sum_const_zero,add_zero,stopped_read_pushforward]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.smul_sum]
  simp only [smul_smul]

private theorem real_read_complement (M : Observer Z) (e : InstalledEmitter M)
    (s : ActivePhase) (z : Z) (hz : (M.project z).control = .fourth (.active s)) :
    (e.emit z (some (.read 1))).toReal = 1-(e.emit z (some (.read 0))).toReal := by
  have h := (e.emit z).tsum_coe
  rw [tsum_fintype,Fintype.sum_option,sum_operations] at h
  simp only [active_none M e s z hz,active_stop M e s z hz,
    Finset.sum_const_zero,zero_add,add_zero,Fin.sum_univ_two] at h
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add ((e.emit z).apply_ne_top _) ((e.emit z).apply_ne_top _)] at hr
  norm_num at hr
  linarith

private theorem mixture_real (p : PMF Z) (L : Z → Measure RawTail)
    (hL : ∀ z, IsProbabilityMeasure (L z)) (f : RawTail → RawTail) (E : Set RawTail) :
    (∑ z, p z • (L z).map f).real E =
      ∑ z, (p z).toReal * (L z).real (f ⁻¹' E) := by
  haveI (z : Z) : IsProbabilityMeasure (L z) := hL z
  have hf : Measurable f := measurable_of_countable _
  haveI (z : Z) : IsProbabilityMeasure ((L z).map f) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  simp only [Measure.real,Measure.coe_finsetSum,Finset.sum_apply,
    Measure.smul_apply,smul_eq_mul]
  rw [ENNReal.toReal_sum (fun z _ => ENNReal.mul_ne_top ((p.apply_ne_top z))
    (measure_ne_top ((L z).map f) E))]
  simp only [ENNReal.toReal_mul,Measure.map_apply hf (show MeasurableSet E from trivial)]

private theorem constant_mixture (p : PMF Z) (L : Z → Measure RawTail)
    (hL : ∀ z, IsProbabilityMeasure (L z)) (r : RawTail) :
    (∑ z, p z • (L z).map (fun _ => r)) = Measure.dirac r := by
  haveI (z : Z) : IsProbabilityMeasure (L z) := hL z
  simp only [Measure.map_const,measure_univ,one_smul]
  rw [← Finset.sum_smul]
  have h : ∑ z, p z = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [h,one_smul]

private theorem mixture_event_finite (p : PMF Z) (L : Z → Measure RawTail)
    (hL : ∀ z, IsProbabilityMeasure (L z)) (f : RawTail → RawTail) (E : Set RawTail) :
    (∑ z, p z • (L z).map f) E ≠ ∞ := by
  haveI (z : Z) : IsProbabilityMeasure (L z) := hL z
  haveI (z : Z) : IsProbabilityMeasure ((L z).map f) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  simp only [Measure.coe_finsetSum,Finset.sum_apply,Measure.smul_apply,smul_eq_mul]
  exact ENNReal.sum_ne_top.mpr (fun z _ =>
    ENNReal.mul_ne_top (p.apply_ne_top z) (measure_ne_top _ _))

private theorem generate_p (M : Observer Z) (e : InstalledEmitter M)
    (z : Z) (hz : (M.project z).control = .fourth (.active .p)) (E : Set RawTail) :
    (rawTailLaw M e .p z).real E =
      (e.emit z (some (.read 0))).toReal * (if some [0] ∈ E then 1 else 0) +
      (1-(e.emit z (some (.read 0))).toReal) *
        ∑ z', (M.update (.read 1) z z').toReal *
          (rawTailLaw M e .beta z').real ((Option.map (List.cons 1)) ⁻¹' E) := by
  rw [raw_tail_regenerate M e .p z hz,Fin.sum_univ_two]
  simp only [residualPhase]
  rw [show nextStopped .p 0 = (fun _ : RawTail => some [0]) from rfl,
    show nextStopped .p 1 = Option.map (List.cons 1) from rfl]
  rw [constant_mixture _ _ (fun _ => inferInstance)]
  have h0 : (e.emit z (some (.read 0)) • Measure.dirac (some [0] : RawTail)) E ≠ ∞ :=
    ENNReal.mul_ne_top ((e.emit z).apply_ne_top _) (measure_ne_top _ _)
  have h1 : (e.emit z (some (.read 1)) •
      ∑ z', M.update (.read 1) z z' •
        (rawTailLaw M e .beta z').map (Option.map (List.cons 1))) E ≠ ∞ :=
    ENNReal.mul_ne_top ((e.emit z).apply_ne_top _)
      (mixture_event_finite _ _ (fun _ => inferInstance) _ E)
  rw [measureReal_add_apply h0 h1,measureReal_ennreal_smul_apply,
    measureReal_ennreal_smul_apply,mixture_real _ _ (fun _ => inferInstance),
    real_read_complement M e .p z hz]
  by_cases he : some [0] ∈ E <;>
    simp [Measure.real,Measure.dirac_apply',Set.indicator_apply,he]

private theorem generate_beta (M : Observer Z) (e : InstalledEmitter M)
    (z : Z) (hz : (M.project z).control = .fourth (.active .beta)) (E : Set RawTail) :
    (rawTailLaw M e .beta z).real E =
      (1-(e.emit z (some (.read 0))).toReal) * (if some [1] ∈ E then 1 else 0) +
      (e.emit z (some (.read 0))).toReal *
        ∑ z', (M.update (.read 0) z z').toReal *
          (rawTailLaw M e .p z').real ((Option.map (List.cons 0)) ⁻¹' E) := by
  rw [raw_tail_regenerate M e .beta z hz,Fin.sum_univ_two]
  simp only [residualPhase]
  rw [show nextStopped .beta 1 = (fun _ : RawTail => some [1]) from rfl,
    show nextStopped .beta 0 = Option.map (List.cons 0) from rfl]
  rw [constant_mixture _ _ (fun _ => inferInstance)]
  have h0 : (e.emit z (some (.read 0)) •
      ∑ z', M.update (.read 0) z z' •
        (rawTailLaw M e .p z').map (Option.map (List.cons 0))) E ≠ ∞ :=
    ENNReal.mul_ne_top ((e.emit z).apply_ne_top _)
      (mixture_event_finite _ _ (fun _ => inferInstance) _ E)
  have h1 : (e.emit z (some (.read 1)) • Measure.dirac (some [1] : RawTail)) E ≠ ∞ :=
    ENNReal.mul_ne_top ((e.emit z).apply_ne_top _) (measure_ne_top _ _)
  rw [measureReal_add_apply h0 h1,measureReal_ennreal_smul_apply,
    measureReal_ennreal_smul_apply,mixture_real _ _ (fun _ => inferInstance),
    real_read_complement M e .beta z hz]
  by_cases he : some [1] ∈ E <;>
    simp [Measure.real,Measure.dirac_apply',Set.indicator_apply,he] <;> ring

/-- Current-control hypotheses connect complete all-event laws to the actual acquired kernels. -/
theorem native_stopped_tail_regeneration (M : Observer Z) (e : InstalledEmitter M) :
    (∀ z : Z, (M.project z).control = .fourth (.active .p) → ∀ E : Set RawTail,
      (rawTailLaw M e .p z).real E =
        (e.emit z (some (.read 0))).toReal * (if some [0] ∈ E then 1 else 0) +
        (1-(e.emit z (some (.read 0))).toReal) *
          ∑ z', (M.update (.read 1) z z').toReal *
            (rawTailLaw M e .beta z').real ((Option.map (List.cons 1)) ⁻¹' E)) ∧
    (∀ z : Z, (M.project z).control = .fourth (.active .beta) → ∀ E : Set RawTail,
      (rawTailLaw M e .beta z).real E =
        (1-(e.emit z (some (.read 0))).toReal) * (if some [1] ∈ E then 1 else 0) +
        (e.emit z (some (.read 0))).toReal *
          ∑ z', (M.update (.read 0) z z').toReal *
            (rawTailLaw M e .p z').real ((Option.map (List.cons 0)) ⁻¹' E)) :=
  ⟨generate_p M e,generate_beta M e⟩

/-- Invalid raw words retract to the valid noncompletion value. -/
def rawRetraction (s : ActivePhase) (t : RawTail) : ValidTail s :=
  if h : Valid s t then ⟨t,h⟩ else ⟨none,trivial⟩

theorem raw_projection_tv (s : ActivePhase) (P Q : Measure (ValidTail s)) :
    measurableTotalVariation (P.map Subtype.val) (Q.map Subtype.val) =
      measurableTotalVariation P Q := by
  have hf : Measurable (Subtype.val : ValidTail s → RawTail) := measurable_subtype_coe
  have hb : Measurable (rawRetraction s) := measurable_of_countable _
  have hi : rawRetraction s ∘ (Subtype.val : ValidTail s → RawTail) = id := by
    funext t
    simp [rawRetraction,t.property]
  refine le_antisymm (measurable_total_variation_map_le P Q _ hf) ?_
  have h := measurable_total_variation_map_le (P.map Subtype.val)
    (Q.map Subtype.val) (rawRetraction s) hb
  simpa only [Measure.map_map hb hf,hi,Measure.map_id] using h

theorem pure_raw_law (k : NativeConditionalControl.DepthLaw.Depth) (s : ActivePhase) :
    (pureTail k s).map Subtype.val =
      explicitStoppedWordLaw s (NativeConditionalControl.DepthLaw.rate k) := by
  rw [pureTail,Measure.map_map (measurable_of_countable _) (validStopped_measurable s)]
  exact (actual_fourth_segment_stopped_word_law _ s).2

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeStoppedTailRegeneration
