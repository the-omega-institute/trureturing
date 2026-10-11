/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeObserverJointLaw
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeObserverJointLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered private updates factor from the same-depth native source at every legal finite cut. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeFullResidual
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open NativeConditionalControl.DepthLaw NativeConditionalControl.Tail
open NativeFullResidual
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction

universe u
variable {Z : Type u} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

local instance : MeasurableSpace (List Operation) := ⊤
local instance : MeasurableSingletonClass (List Operation) := ⟨fun _ => trivial⟩

/-- COMPLETE is the one finite carrier Z. The data have no depth, history,
    posterior, cursor or distribution argument. Updates exist independently of emissions. -/
structure Observer (Z : Type u) [Fintype Z] where
  project : Z → FiniteFields
  init : PMF Z
  update : Operation → Z → PMF Z
  init_refines : ∀ z ∈ init.support, project z = initial.source.finiteFields
  update_refines : ∀ (op : Operation) (z : Z) (f : FiniteFields),
    finiteStep (project z) op = some f →
    ∀ z' ∈ (update op z).support, project z' = f

/-- This ordered product is an analysis row, never a component of COMPLETE. -/
def advance (M : Observer Z) (η : PMF Z) : List Operation → PMF Z
  | [] => η
  | op :: h => advance M (η.bind (M.update op)) h

def row (M : Observer Z) (h : List Operation) : PMF Z := advance M M.init h

private theorem advance_append (M : Observer Z) (η : PMF Z) (h v : List Operation) :
    advance M η (h ++ v) = advance M (advance M η h) v := by
  induction h generalizing η with
  | nil => rfl
  | cons op h ih => exact ih _

private theorem advance_refines (M : Observer Z) (η : PMF Z)
    (c d : AcquiredNativeState) (h : List Operation)
    (he : execute c h = some d)
    (hp : ∀ z ∈ η.support, M.project z = c.source.finiteFields) :
    ∀ z ∈ (advance M η h).support, M.project z = d.source.finiteFields := by
  induction h generalizing η c with
  | nil =>
    have hd : c = d := Option.some.inj he
    simpa [advance,hd] using hp
  | cons op h ih =>
    obtain ⟨e,hce,hed⟩ := Option.bind_eq_some_iff.mp he
    apply ih (η.bind (M.update op)) e hed
    intro z hz
    obtain ⟨y,hy,hyz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    apply M.update_refines op y e.source.finiteFields _ z hyz
    rw [hp y hy,← finite_projection_commutes,hce]
    rfl

/-- The actual finite cut saturates at delivered Stop; it never resets after overrun. -/
def cutHistory (ω : Stream) : ℕ → List Operation
  | 0 => []
  | n+1 => ((nativeDrive initial ω (n+1)).map Prod.fst).getD (cutHistory ω n)

private theorem cut_measurable (n : ℕ) : Measurable (fun ω : Stream => cutHistory ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_of_countable (fun p :
      Option (List Operation × AcquiredNativeState × ℕ) × List Operation =>
        (p.1.map Prod.fst).getD p.2)).comp ((drive_measurable initial (n+1)).prodMk ih)

private theorem cut_eq (h : List Operation) (c : AcquiredNativeState)
    (ω : Stream) (hd : nativeDrive initial ω h.length =
      some (h,c,(readLetters h).length)) : cutHistory ω h.length = h := by
  cases h with
  | nil => rfl
  | cons op h =>
    simp only [List.length_cons] at hd ⊢
    simp [cutHistory, hd]

/-- Constructed source/private joint kernel at an actual cut. It uses only the
    already acquired native prefix, including paid rejections and ordered returns. -/
def privateKernel (M : Observer Z) (n : ℕ) : Kernel (Depth × Stream) Z where
  toFun t := (row M (cutHistory t.2 n)).toMeasure
  measurable' := (measurable_of_countable (fun h : List Operation => (row M h).toMeasure)).comp
    ((cut_measurable n).comp measurable_snd)

instance (M : Observer Z) (n : ℕ) : IsMarkovKernel (privateKernel M n) :=
  ⟨fun t => by change IsProbabilityMeasure (row M (cutHistory t.2 n)).toMeasure; infer_instance⟩

def actualLaw (M : Observer Z) (μ : PMF Depth) (n : ℕ) : Measure ((Depth × Stream) × Z) :=
  (jointLaw μ) ⊗ₘ (privateKernel M n)

instance (M : Observer Z) (μ : PMF Depth) (n : ℕ) :
    IsProbabilityMeasure (actualLaw M μ n) := by
  unfold actualLaw
  infer_instance

private theorem kernel_on_history (M : Observer Z) (h : List Operation)
    (c : AcquiredNativeState) (t : Depth × Stream) (ht : t ∈ nativeEvent h c) :
    privateKernel M h.length t = (row M h).toMeasure := by
  change (row M (cutHistory t.2 h.length)).toMeasure = (row M h).toMeasure
  rw [cut_eq h c t.2 ht]

private theorem history_rectangle (M : Observer Z) (μ : PMF Depth)
    (h : List Operation) (c : AcquiredNativeState) (A : Set (Depth × Stream))
    (hA : MeasurableSet A) (hsub : A ⊆ nativeEvent h c) (B : Set Z)
    (hB : MeasurableSet B) :
    actualLaw M μ h.length (A ×ˢ B) = jointLaw μ A * (row M h).toMeasure B := by
  rw [actualLaw,Measure.compProd_apply_prod hA hB]
  calc
    _ = ∫⁻ t in A, (row M h).toMeasure B ∂jointLaw μ :=
      setLIntegral_congr_fun hA fun t ht => congrArg (fun m : Measure Z => m B)
        (kernel_on_history M h c t (hsub ht))
    _ = _ := by simp [mul_comm]

private theorem tagged_source (μ : PMF Depth) (k : Depth) (A : Set Stream)
    (hA : MeasurableSet A) :
    jointLaw μ ({k} ×ˢ A) = μ k * rawReadLaw (rate k) A := by
  rw [jointLaw,Measure.sum_apply_of_countable]
  simp only [Measure.smul_apply,smul_eq_mul]
  rw [tsum_eq_single k]
  · rw [Measure.map_apply (by fun_prop) ((measurableSet_singleton _).prod hA)]
    simp
  · intro j hj
    rw [Measure.map_apply (by fun_prop) ((measurableSet_singleton _).prod hA)]
    simp [hj]

/-- The original joint mass, including any measurable unread-source event. -/
theorem ordered_history_factorization (M : Observer Z) (μ : PMF Depth)
    (h : List Operation) (c : AcquiredNativeState) (hc : run h = some c)
    (k : Depth) (z : Z) (E : Set Stream) (hE : MeasurableSet E) :
    actualLaw M μ h.length
      ((nativeEvent h c ∩ {t : Depth × Stream |
          t.1 = k ∧ rawTail t.2 (readLetters h).length ∈ E}) ×ˢ {z}) =
      μ k * likelihood h k * row M h z * rawReadLaw (rate k) E := by
  let A := nativeEvent h c ∩ {t : Depth × Stream |
    t.1 = k ∧ rawTail t.2 (readLetters h).length ∈ E}
  have hA : MeasurableSet A := (event_measurable h c).inter
    ((measurableSet_singleton k).preimage measurable_fst |>.inter
      (hE.preimage (by unfold rawTail; fun_prop)))
  rw [history_rectangle M μ h c A hA Set.inter_subset_left {z} (measurableSet_singleton z),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z)]
  have he : A = {k} ×ˢ
      (prefixCylinder (readLetters h) ∩
        (fun ω => rawTail ω (readLetters h).length) ⁻¹' E) := by
    dsimp only [A]
    rw [event_eq h c hc]
    ext t
    simp [Set.mem_prod,Set.mem_preimage,Set.mem_inter_iff,and_assoc,and_left_comm]
  rw [he,tagged_source μ k _ ((measurable_cylinder _).inter
    (hE.preimage (by unfold rawTail; fun_prop))),prefix_tail_factorization _ _ E hE]
  simp [likelihood,mul_assoc,mul_comm,mul_left_comm]

private theorem history_mass_joint (M : Observer Z) (μ : PMF Depth)
    (h : List Operation) (c : AcquiredNativeState) (hc : run h = some c) :
    actualLaw M μ h.length (nativeEvent h c ×ˢ Set.univ) = normalizer μ h := by
  rw [history_rectangle M μ h c _ (event_measurable h c) (Set.Subset.refl _)
    _ MeasurableSet.univ,measure_univ,mul_one,history_mass μ h c hc]

/-- Conditioning on the original history leaves the entire ordered private row
    independent of the same-K posterior source. No configuration is selected in advance. -/
theorem conditional_history_product (M : Observer Z) (μ : PMF Depth)
    (h : List Operation) (c : AcquiredNativeState) (hc : run h = some c) :
    ProbabilityTheory.cond (actualLaw M μ h.length) (nativeEvent h c ×ˢ Set.univ) =
      (ProbabilityTheory.cond (jointLaw μ) (nativeEvent h c)).prod (row M h).toMeasure := by
  apply Measure.ext_prod
  intro A B hA hB
  rw [ProbabilityTheory.cond,Measure.smul_apply,Measure.restrict_apply (hA.prod hB),
    history_mass_joint M μ h c hc]
  have hi : (A ×ˢ B) ∩ (nativeEvent h c ×ˢ Set.univ) =
      (A ∩ nativeEvent h c) ×ˢ B := by
    ext p
    simp [and_assoc, and_left_comm, and_comm]
  rw [hi,history_rectangle M μ h c _ (hA.inter (event_measurable h c))
    Set.inter_subset_right B hB,Measure.prod_prod]
  rw [ProbabilityTheory.cond,Measure.smul_apply,Measure.restrict_apply hA,history_mass μ h c hc]
  simp [smul_eq_mul,mul_assoc]

/-- The literal common source and the private configuration are transported together. -/
theorem sameK_private_tail (M : Observer Z) (μ : PMF Depth)
    (h : List Operation) (c : AcquiredNativeState) (hc : run h = some c) :
    (ProbabilityTheory.cond (actualLaw M μ h.length) (nativeEvent h c ×ˢ Set.univ)).map
      (Prod.map (fun t : Depth × Stream =>
        (t.1,rawTail t.2 (readLetters h).length)) id) =
      (jointLaw (posterior μ h c hc)).prod (row M h).toMeasure := by
  rw [conditional_history_product M μ h c hc,← Measure.map_prod_map _ _
    (by unfold rawTail; fun_prop) measurable_id,sameK_conditional_tail μ h c hc,Measure.map_id]

/-- Every positive configuration has exactly the acquired full native fields.
    The next ordered update is defined even if a separate synthetic emission is zero. -/
theorem actual_row_refines (M : Observer Z) (h : List Operation)
    (c : AcquiredNativeState) (hc : run h = some c) :
    (∀ z ∈ (row M h).support, M.project z = c.source.finiteFields) ∧
    (∀ op : Operation, row M (h ++ [op]) = (row M h).bind (M.update op)) ∧
    ∃ nf : PrefixForm, render nf = h ∧ c = reconstruct nf ∧ PrefixFacts nf c := by
  refine ⟨advance_refines M M.init initial c h hc M.init_refines, ?_, ?_⟩
  · intro op
    exact advance_append M M.init h [op]
  · obtain ⟨nf, hn, _⟩ := (native_acquired_prefix_reconstruction h).1.mp ⟨c, hc⟩
    have hr := (native_acquired_prefix_reconstruction h).2 nf hn
    have he : c = reconstruct nf := Option.some.inj (hc.symm.trans hr.1)
    exact ⟨nf, hn, he, he.symm ▸ hr.2.1⟩

private theorem stopped_valid (s : ActivePhase) (ω : Stream) :
    Valid s (stoppedReadWord s ω) := by
  cases hw : stoppedReadWord s ω with
  | none => trivial
  | some w => exact ((stopped_word_fiber s ω w).mp hw).2

/-- The legal tail random variable includes the unique noncompletion outcome. -/
def validStopped (s : ActivePhase) (ω : Stream) : ValidTail s :=
  ⟨stoppedReadWord s ω, stopped_valid s ω⟩

theorem validStopped_measurable (s : ActivePhase) : Measurable (validStopped s) :=
  (measurable_stopped_read_word s).subtype_mk

/-- Constructed raw target from the actual acquired history and same unread source. -/
def rawTarget (μ : PMF Depth) (h : List Operation) (c : AcquiredNativeState)
    (s : ActivePhase) : Measure (ValidTail s) :=
  (ProbabilityTheory.cond (jointLaw μ) (nativeEvent h c)).map
    (fun t => validStopped s (rawTail t.2 (readLetters h).length))

/-- Constructed full target from the actual source/private joint law. -/
def fullTarget (M : Observer Z) (μ : PMF Depth) (h : List Operation)
    (c : AcquiredNativeState) : Measure FullTranscript :=
  (ProbabilityTheory.cond (actualLaw M μ h.length) (nativeEvent h c ×ˢ Set.univ)).map
    (fun t => fullTranscript c (rawTail t.1.2 (readLetters h).length))

private theorem fullTranscript_measurable (c : AcquiredNativeState) :
    Measurable (fullTranscript c) := by
  apply measurable_pi_lambda
  intro n
  exact (measurable_of_countable (fun r : Option (List Operation × AcquiredNativeState × ℕ) =>
    r.map fun p => (p.1, p.2.1.source.finiteFields,
      eventBlocks c.source.finiteFields p.1))).comp (drive_measurable c n)

private theorem fullTarget_eq (M : Observer Z) (μ : PMF Depth)
    (h : List Operation) (c : AcquiredNativeState) (hc : run h = some c)
    (s : ActivePhase) (hs : c.source.finiteFields.control = .fourth (.active s)) :
    fullTarget M μ h c = (rawTarget μ h c s).map (fullRenderer c s) := by
  let shift : Depth × Stream → Depth × Stream :=
    fun t => (t.1, rawTail t.2 (readLetters h).length)
  let render : (Depth × Stream) × Z → FullTranscript :=
    fun t => fullTranscript c t.1.2
  have ht : Measurable shift := by dsimp [shift]; unfold rawTail; fun_prop
  have hr : Measurable render :=
    (fullTranscript_measurable c).comp (measurable_snd.comp measurable_fst)
  have hv : Measurable (fun t : Depth × Stream => validStopped s t.2) :=
    (validStopped_measurable s).comp measurable_snd
  have hf : Measurable (fun t : Depth × Stream => fullTranscript c t.2) :=
    (fullTranscript_measurable c).comp measurable_snd
  have hsource : (rawTarget μ h c s).map (fullRenderer c s) =
      (jointLaw (posterior μ h c hc)).map (fun t => fullTranscript c t.2) := by
    unfold rawTarget
    change (((ProbabilityTheory.cond (jointLaw μ) (nativeEvent h c)).map
      ((fun t : Depth × Stream => validStopped s t.2) ∘ shift)).map _) = _
    rw [← Measure.map_map hv ht, sameK_conditional_tail μ h c hc,
      Measure.map_map (measurable_of_countable _) hv]
    congr 1
    funext t
    exact (full_renderer_all_paths c s hs t.2).symm
  unfold fullTarget
  change ((ProbabilityTheory.cond (actualLaw M μ h.length)
    (nativeEvent h c ×ˢ Set.univ)).map (render ∘ Prod.map shift id)) = _
  rw [← Measure.map_map hr (ht.prodMap measurable_id), sameK_private_tail M μ h c hc]
  change (((jointLaw (posterior μ h c hc)).prod (row M h).toMeasure).map
    ((fun t : Depth × Stream => fullTranscript c t.2) ∘ Prod.fst)) = _
  rw [← Measure.map_map hf measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  exact hsource.symm

private theorem rawTarget_words (μ : PMF Depth) (h : List Operation)
    (c : AcquiredNativeState) (hc : run h = some c) (s : ActivePhase) :
    (rawTarget μ h c s).map Subtype.val =
      FourthSegmentLawRecovery.WordLaw.wordMixture (posterior μ h c hc) s := by
  have hv : Measurable (fun t : Depth × Stream =>
      validStopped s (rawTail t.2 (readLetters h).length)) :=
    (validStopped_measurable s).comp (by unfold rawTail; fun_prop)
  rw [rawTarget, Measure.map_map measurable_subtype_coe hv]
  exact FourthSegmentLawRecovery.WordLaw.posterior_word_law μ h c hc s

private theorem rawTarget_probability (μ : PMF Depth) (h : List Operation)
    (c : AcquiredNativeState) (hc : run h = some c) (s : ActivePhase) :
    IsProbabilityMeasure (rawTarget μ h c s) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond (jointLaw μ) (nativeEvent h c)) := by
    apply ProbabilityTheory.cond_isProbabilityMeasure
    rw [history_mass μ h c hc]
    exact ne_of_gt (normalizer_bounds μ h c hc).1
  exact Measure.isProbabilityMeasure_map
    ((validStopped_measurable s).comp (by unfold rawTail; fun_prop)).aemeasurable

/-- All legal phase histories, with no bound on paid rejections or fourth returns. -/
abbrev PhaseHistory (s : ActivePhase) :=
  {p : List Operation × AcquiredNativeState //
    run p.1 = some p.2 ∧ p.2.source.finiteFields.control = .fourth (.active s)}

/-- Configuration-before-TV on each full original law, then the full history supremum. -/
def fullRisk (M : Observer Z) (μ : PMF Depth) (s : ActivePhase)
    (D : PhaseHistory s → Z → Measure (ValidTail s)) : ℝ≥0∞ :=
  ⨆ H : PhaseHistory s, ∑ z, row M H.val.1 z * measurableTotalVariation
    ((D H z).map (fullRenderer H.val.2 s)) (fullTarget M μ H.val.1 H.val.2)

def rawRisk (M : Observer Z) (μ : PMF Depth) (s : ActivePhase)
    (D : PhaseHistory s → Z → Measure (ValidTail s)) : ℝ≥0∞ :=
  ⨆ H : PhaseHistory s, ∑ z, row M H.val.1 z * measurableTotalVariation
    (D H z) (rawTarget μ H.val.1 H.val.2 s)

/-- The actual target, ordered acquired row, all fields and full-history supremum
    are transported together. Decoders are lawful tail laws supplied separately;
    this theorem constructs the actual law, not a synthetic emission program. -/
theorem native_history_risk_transport (M : Observer Z) (μ : PMF Depth)
    (s : ActivePhase) (D : PhaseHistory s → Z → Measure (ValidTail s)) :
    (∀ H : PhaseHistory s,
      IsProbabilityMeasure (rawTarget μ H.val.1 H.val.2 s) ∧
      IsProbabilityMeasure (fullTarget M μ H.val.1 H.val.2) ∧
      fullTarget M μ H.val.1 H.val.2 =
        (rawTarget μ H.val.1 H.val.2 s).map (fullRenderer H.val.2 s) ∧
      (rawTarget μ H.val.1 H.val.2 s).map Subtype.val =
        FourthSegmentLawRecovery.WordLaw.wordMixture
          (posterior μ H.val.1 H.val.2 H.property.1) s ∧
      (ProbabilityTheory.cond (actualLaw M μ H.val.1.length)
        (nativeEvent H.val.1 H.val.2 ×ˢ Set.univ)).map Prod.snd = (row M H.val.1).toMeasure ∧
      (∀ z ∈ (row M H.val.1).support, M.project z = H.val.2.source.finiteFields) ∧
      (∀ op : Operation, row M (H.val.1 ++ [op]) = (row M H.val.1).bind (M.update op)) ∧
      (∃ nf : PrefixForm, render nf = H.val.1 ∧ H.val.2 = reconstruct nf ∧
        PrefixFacts nf H.val.2) ∧
      (∀ (ω : Stream) (d : AcquiredNativeState) (op : Operation),
        nextNative H.val.2 ω = some (op, d) →
        deleteBlock (fullTranscript H.val.2 ω) =
          fullTranscript d (rawTail ω (readCost op))) ∧
      (∀ (k : Depth) (z : Z) (E : Set Stream), MeasurableSet E →
        actualLaw M μ H.val.1.length
          ((nativeEvent H.val.1 H.val.2 ∩ {t : Depth × Stream |
            t.1 = k ∧ rawTail t.2 (readLetters H.val.1).length ∈ E}) ×ˢ {z}) =
          μ k * likelihood H.val.1 k * row M H.val.1 z * rawReadLaw (rate k) E) ∧
      (∀ ω : Stream, ω ∈ prefixCylinder (readLetters H.val.1) →
        fullTranscript initial ω H.val.1.length =
          some (H.val.1, H.val.2.source.finiteFields,
            eventBlocks initial.source.finiteFields H.val.1) ∧
        (eventBlocks initial.source.finiteFields H.val.1).foldl replayBlock
          initial.source.finiteFields = H.val.2.source.finiteFields ∧
        originalView ((eventBlocks initial.source.finiteFields H.val.1).foldl replayBlock
          initial.source.finiteFields) = originalView H.val.2.source.finiteFields)) ∧
    fullRisk M μ s D = rawRisk M μ s D := by
  constructor
  · intro H
    haveI := rawTarget_probability μ _ _ H.property.1 s
    refine ⟨inferInstance, ?_, fullTarget_eq M μ _ _ H.property.1 s H.property.2,
      rawTarget_words μ _ _ H.property.1 s, ?_,
      (actual_row_refines M _ _ H.property.1).1,
      (actual_row_refines M _ _ H.property.1).2.1,
      (actual_row_refines M _ _ H.property.1).2.2,
      (fun ω d op => full_delete_block H.val.2 d ω op),
      ordered_history_factorization M μ _ _ H.property.1, ?_⟩
    · rw [fullTarget_eq M μ _ _ H.property.1 s H.property.2]
      exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
    · rw [conditional_history_product M μ _ _ H.property.1, Measure.map_snd_prod]
      have hp := normalizer_bounds μ H.val.1 H.val.2 H.property.1
      haveI : IsProbabilityMeasure
          (ProbabilityTheory.cond (jointLaw μ) (nativeEvent H.val.1 H.val.2)) := by
        apply ProbabilityTheory.cond_isProbabilityMeasure
        rw [history_mass μ _ _ H.property.1]
        exact ne_of_gt hp.1
      simp
    · intro ω hω
      apply full_event_reconstruction initial H.val.2 ω H.val.1.length
        (readLetters H.val.1).length H.val.1
      exact (native_acquired_prefix_cylinder _ _ _ _).mpr ⟨H.property.1, hω, rfl⟩
  · unfold fullRisk rawRisk
    congr 1
    funext H
    apply Finset.sum_congr rfl
    intro z _
    rw [fullTarget_eq M μ _ _ H.property.1 s H.property.2,
      full_renderer_tv _ s H.property.2]

#print axioms ordered_history_factorization
#print axioms conditional_history_product
#print axioms sameK_private_tail
#print axioms actual_row_refines
#print axioms native_history_risk_transport

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw
