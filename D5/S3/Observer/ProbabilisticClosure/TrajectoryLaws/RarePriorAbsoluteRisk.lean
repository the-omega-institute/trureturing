/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorAbsoluteRisk
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorAbsoluteRisk
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Runtime lawful fourth tails identify complete native risks. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorThreePoint
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator
import Mathlib.MeasureTheory.Measure.Sub
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorAbsoluteRisk
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators Classical
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open NativeFullResidual RarePriorFiniteMonitor RarePriorFairBitService RarePriorFullFields
open RarePriorGeneratedLaw RarePriorThreePoint
open ConstantSuspensionSeparator (prefixRaw)
open NativeConditionalControl.Prefix NativeConditionalControl.DepthLaw
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open D5.S3.Estimation.DataProcessing.MeasurableTotalVariationTriangle
/-- The phase-indexed law uses only the retained finite runtime. Off-phase rows
    still give a lawful tail; reconstruction is asserted at the actual phase. -/
def lawfulTail (s : ActivePhase) (z : Runtime) : Measure (ValidTail s) :=
  (pathLaw z).map fun p => NativeObserverJointLaw.validStopped s (fun n => (p n).2)
private theorem lawfulTail_probability (s : ActivePhase) (z : Runtime) :
    IsProbabilityMeasure (lawfulTail s z) :=
  Measure.isProbabilityMeasure_map ((NativeObserverJointLaw.validStopped_measurable s).comp (by fun_prop)).aemeasurable
private theorem lawfulTail_reconstruction (s : ActivePhase) (z : Runtime)
    (c : AcquiredNativeState) (hf : z.fields = c.source.finiteFields)
    (hs : c.source.finiteFields.control = .fourth (.active s)) :
    decoder z = (lawfulTail s z).map (fullRenderer c s) := by
  have hm : Measurable (fun p : ℕ → Marked =>
      NativeObserverJointLaw.validStopped s (fun n => (p n).2)) :=
    (NativeObserverJointLaw.validStopped_measurable s).comp (by fun_prop)
  rw [lawfulTail,Measure.map_map (measurable_of_countable _) hm]
  unfold decoder
  congr 1
  funext p
  change fieldsTranscript z.fields (fun n => (p n).2) =
    fullTranscript c (tailStream s (stoppedReadWord s (fun n => (p n).2)))
  rw [hf,← (full_fields_factorization c _).1]; exact full_renderer_all_paths c s hs _
private theorem actual_decoder_reconstruction (μ : PMF Depth) (s : ActivePhase)
    (H : NativeObserverJointLaw.PhaseHistory s) (z : Runtime)
    (hz : z ∈ (NativeObserverJointLaw.row actualObserver H.val.1).support) :
    decoder z = (lawfulTail s z).map (fullRenderer H.val.2 s) := by
  have h := (NativeObserverJointLaw.native_history_risk_transport actualObserver μ s
    (fun _ => lawfulTail s)).1 H
  exact lawfulTail_reconstruction s z H.val.2 (h.2.2.2.2.2.1 z hz) H.property.2
private theorem native_risk_eq (μ : PMF Depth) (s : ActivePhase) :
    NativeObserverJointLaw.fullRisk actualObserver μ s (fun _ => lawfulTail s) = phaseConfRisk μ s ∧
    NativeObserverJointLaw.rawRisk actualObserver μ s (fun _ => lawfulTail s) =
      phaseLawRisk μ s := by
  have h := NativeObserverJointLaw.native_history_risk_transport actualObserver μ s
    (fun _ => lawfulTail s)
  have he : NativeObserverJointLaw.fullRisk actualObserver μ s (fun _ => lawfulTail s) =
      phaseConfRisk μ s := by
    unfold NativeObserverJointLaw.fullRisk phaseConfRisk confError
    apply iSup_congr
    intro H; apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z ∈ (NativeObserverJointLaw.row actualObserver H.val.1).support
    · rw [← actual_decoder_reconstruction μ s H z hz]
    · have hz0 : NativeObserverJointLaw.row actualObserver H.val.1 z = 0 := by
        simpa only [PMF.mem_support_iff,not_not] using hz
      simp [hz0]
  refine ⟨he,?_⟩
  rw [← h.2,he]
  exact (complete_record_risk_bridges (shortParameter 0) ((every_short_history 0).1)).2.1 μ s |>.1
def rawPath (p : ℕ → Marked) : Stream := fun n => (p n).2
private theorem initial_mark_mass (z : Runtime) (x : Letter) : pathLaw z {p | p 0 = (z,x)} =
      (bernoulliMeasure (0 : Letter) 1 (emissionParameter z)) {x} := by
  have h := (generated_full_law z).2.2.2.2.1 0 (fun _ => (z,x))
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at h
  have he : (fun p : ℕ → Marked => fun i : Fin 1 => p i.val) ⁻¹' {fun _ => (z,x)} =
      {p | p 0 = (z,x)} := by
    ext p; simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_setOf_eq,funext_iff]
    refine ⟨fun hp => hp 0,fun hp i => ?_⟩
    have hi : i.val = 0 := by omega
    simpa only [hi] using hp
  rw [he] at h; simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one] at h
  rw [h,markedInitial,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  congr 1
  ext y
  simp
private theorem raw_prefix_cons (z : Runtime) (x : Letter) (w : List Letter) :
    pathLaw z (rawPath ⁻¹' prefixCylinder (x :: w)) =
      (bernoulliMeasure (0 : Letter) 1 (emissionParameter z)) {x} *
        pathLaw (readAdvance z x) (rawPath ⁻¹' prefixCylinder w) := by
  let A : Set (ℕ → Marked) := {p | p 0 = (z,x)}
  let E : Set (ℕ → Marked) := rawPath ⁻¹' prefixCylinder w
  have hE : MeasurableSet E := (measurable_cylinder w).preimage (by unfold rawPath; fun_prop)
  have hm := initial_mark_mass z x
  have hc := congrArg (fun ν : Measure (ℕ → Marked) => ν E) (conditioned_read_path z x)
  rw [Measure.map_apply (by fun_prop) hE,cond_apply' (hE.preimage (by fun_prop))] at hc
  have hpos : pathLaw z A ≠ 0 := by
    rw [show A = {p | p 0 = (z,x)} from rfl,hm]
    fin_cases x <;> cases ht : selectedThreshold z <;>
      norm_num [bernoulliMeasure_apply,emissionParameter,ht,threshold,
        ENNReal.coe_eq_zero,← NNReal.coe_eq_zero,unitInterval.coe_toNNReal]
  have hrec : pathLaw z (A ∩ (fun p n => p (n+1)) ⁻¹' E) =
      pathLaw z A * pathLaw (readAdvance z x) E := by
    rw [← hc,← mul_assoc,ENNReal.mul_inv_cancel hpos (measure_ne_top _ _),one_mul]
  have he : (rawPath ⁻¹' prefixCylinder (x :: w) : Set (ℕ → Marked)) =ᵐ[pathLaw z]
      (A ∩ (fun p n => p (n+1)) ⁻¹' E : Set (ℕ → Marked)) := by
    filter_upwards [(generated_full_law z).2.2.2.2.2.2] with p hp
    change (Prefix (rawPath p) (x :: w)) =
      (p 0 = (z,x) ∧ Prefix (rawPath (fun n => p (n+1))) w)
    apply propext
    simp only [Prefix,rawPath,List.length_cons,readPrefix,List.ofFn_succ,List.cons.injEq]
    have he : p 0 = (z,x) ↔ (p 0).2 = x := by
      rw [Prod.ext_iff,hp.1]
      simp
    simp only [he,Fin.val_zero,Fin.val_succ]
  rw [measure_congr he,hrec,show pathLaw z A = _ from hm]
private def watchControl : Monitor → Option NativeControl
  | .block _ p => some (.seed (if p.val % 2 = 0 then none else some (if p.val ≤ 6 then 0 else 1)))
  | .suffix p => some (match p.val with
      | 0 => .seed (some 1)
      | 1 => .early 0 .p
      | 2 => .early 0 .beta
      | 3 => .early 1 .p
      | _ => .early 2 .p)
  | .accepted | .sink => none
private def WatchingInvariant (z : Runtime) : Prop :=
  z.mode = .watching → watchControl z.monitor = some z.fields.control
private theorem watching_step (z d : Runtime) (op : Operation)
    (hi : WatchingInvariant z) (hd : runtimeStep z op = some d) : WatchingInvariant d := by
  rcases z with ⟨⟨ctrl,r⟩,mon,m⟩
  obtain ⟨f,hf,he⟩ := Option.map_eq_some_iff.mp hd
  subst d
  dsimp only [WatchingInvariant]
  cases m with
  | ordinary => simp [nextMode]
  | gBeta => cases op <;> simp [nextMode]
  | g => cases op with
    | stop b => simp [nextMode]
    | read x => fin_cases x <;> simp [nextMode]
  | watching =>
    have hh := hi rfl
    cases op with
    | stop b => simp [nextMode]
    | read x =>
      cases mon with
      | accepted => simp [watchControl] at hh
      | sink => simp [watchControl] at hh
      | suffix p =>
        fin_cases p <;> fin_cases x <;>
          simp [watchControl] at hh <;> subst ctrl <;>
          simp [finiteStep,finiteRead,payloadRead,payloadControl,completionControl] at hf <;>
          subst f <;> simp [scan,nextMode,watchControl]
      | block c p =>
        fin_cases p <;> fin_cases x <;>
          simp [watchControl] at hh <;> subst ctrl <;>
          simp [finiteStep,finiteRead,payloadRead,payloadControl,completionControl] at hf <;>
          subst f <;> simp [scan,nextMode,watchControl] <;> split_ifs <;> simp_all
private theorem watching_execute (z d : Runtime) (ops : List Operation)
    (hi : WatchingInvariant z) (hd : runtimeExecute z ops = some d) : WatchingInvariant d := by
  induction ops generalizing z with
  | nil => simp only [runtimeExecute,Option.some.injEq] at hd; subst d; exact hi
  | cons op ops ih =>
    obtain ⟨q,hq,hd⟩ := Option.bind_eq_some_iff.mp hd
    exact ih q (watching_step z q op hi hq) hd
private theorem actual_not_watching (h : List Operation) (z : Runtime)
    (hz : runtimeRun h = some z) (s : ActivePhase)
    (hs : z.fields.control = .fourth (.active s)) : z.mode ≠ .watching := by
  have hi : WatchingInvariant z := watching_execute runtimeInitial z h
    (by simp [WatchingInvariant,runtimeInitial,watchControl,initial,monitorInitial]) hz
  intro hm; have he := hi hm
  rw [hs] at he
  cases hmon : z.monitor with
  | accepted => simp [hmon,watchControl] at he
  | sink => simp [hmon,watchControl] at he
  | block c p => simp [hmon,watchControl] at he
  | suffix p => fin_cases p <;> simp [hmon,watchControl] at he
private theorem ordinary_advance (z : Runtime) (hm : z.mode = .ordinary) (x : Letter) :
    (readAdvance z x).mode = .ordinary := by
  unfold readAdvance runtimeStep
  cases hf : finiteStep z.fields (.read x) <;> simp [hf,nextMode,hm]
private theorem ordinary_parameter (z : Runtime) (hm : z.mode = .ordinary) :
    (emissionParameter z : ℝ) = 2/5 := by
  cases z with | mk f mon m =>
    dsimp at hm
    subst m
    cases f with | mk ctrl r =>
      cases ctrl with
      | seed first => norm_num [emissionParameter,selectedThreshold,queryMode,threshold]
      | early t s => norm_num [emissionParameter,selectedThreshold,queryMode,threshold]
      | fourth q => cases q with
        | active s => cases s <;>
          norm_num [emissionParameter,selectedThreshold,queryMode,threshold]
        | pending b => norm_num [emissionParameter,selectedThreshold,queryMode,threshold]
        | delivered => norm_num [emissionParameter,selectedThreshold,queryMode,threshold]
def ordinaryRate : unitInterval := ⟨2/5,by norm_num,by norm_num⟩
private theorem ordinary_prefix (z : Runtime) (hm : z.mode = .ordinary) (w : List Letter) :
    pathLaw z (rawPath ⁻¹' prefixCylinder w) = wordMass ordinaryRate w := by
  induction w generalizing z with
  | nil => simp [rawPath,prefixCylinder,Prefix,readPrefix,wordMass]
  | cons x w ih =>
    rw [raw_prefix_cons,ih _ (ordinary_advance z hm x)]
    have he : emissionParameter z = ordinaryRate := Subtype.ext (ordinary_parameter z hm)
    simp [wordMass,he]
private theorem ordinary_stream (z : Runtime) (hm : z.mode = .ordinary) :
    (pathLaw z).map rawPath = rawReadLaw ordinaryRate := by
  let μ := (pathLaw z).map rawPath
  let ν := rawReadLaw ordinaryRate
  have hmeas : Measurable rawPath := by unfold rawPath; fun_prop
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have he (n : ℕ) : μ.map (fun p (i : Fin (n+1)) => p i.val) =
      ν.map (fun p (i : Fin (n+1)) => p i.val) := by
    apply Measure.ext_of_singleton
    intro w; have hevent : (fun p : Stream => fun i : Fin (n+1) => p i.val) ⁻¹' {w} =
        prefixCylinder (List.ofFn w) := by
      ext p; simp only [Set.mem_preimage,Set.mem_singleton_iff,prefixCylinder,
        Set.mem_ofPred_eq,Prefix,List.length_ofFn,readPrefix,List.ofFn_inj,Fin.val_cast]
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _),
      Measure.map_apply (by fun_prop) (measurableSet_singleton _),hevent]
    change μ (prefixCylinder (List.ofFn w)) = _
    rw [show μ (prefixCylinder (List.ofFn w)) = _ from
      Measure.map_apply hmeas (measurable_cylinder _),ordinary_prefix z hm,cylinder_mass]
  let P : (I : Finset ℕ) → Measure (I → Letter) := fun I => ν.map I.restrict
  have hp : IsProjectiveMeasureFamily (α := fun _ : ℕ => Letter) P := by
    intro I J hJI
    dsimp [P]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
  have hμ : IsProjectiveLimit (α := fun _ : ℕ => Letter) μ P := by
    apply (isProjectiveLimit_nat_iff hp μ).mpr
    intro n
    let E : (Fin (n+1) → Letter) → (Finset.Iic n → Letter) :=
      fun w i => w ⟨i.val,Nat.lt_succ_iff.mpr (Finset.mem_Iic.mp i.property)⟩
    have hf (ρ : Measure Stream) : ρ.map (frestrictLe n) =
        (ρ.map (fun p (i : Fin (n+1)) => p i.val)).map E := by
      rw [Measure.map_map (measurable_of_countable _) (by fun_prop)]; rfl
    rw [hf,he,← hf]; rfl
  exact hμ.unique (show IsProjectiveLimit ν P from fun _ => rfl)
private theorem ordinary_tail (z : Runtime) (hm : z.mode = .ordinary) (s : ActivePhase) :
    (lawfulTail s z).map Subtype.val = explicitStoppedWordLaw s ordinaryRate := by
  have hr : Measurable rawPath := by unfold rawPath; fun_prop
  have hm' : Measurable (fun p : ℕ → Marked =>
      NativeObserverJointLaw.validStopped s (fun n => (p n).2)) :=
    (NativeObserverJointLaw.validStopped_measurable s).comp hr
  rw [lawfulTail,Measure.map_map measurable_subtype_coe hm']
  change (pathLaw z).map ((stoppedReadWord s) ∘ rawPath) = _
  rw [← Measure.map_map (measurable_stopped_read_word s) hr,ordinary_stream z hm]
  exact (actual_fourth_segment_stopped_word_law ordinaryRate s).2
private theorem common_measure_tv {X : Type*} [MeasurableSpace X]
    (P Q C : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsFiniteMeasure C] (hP : C ≤ P) (hQ : C ≤ Q) :
    measurableTotalVariation P Q ≤ 1-C Set.univ := by
  have hmassP : (P-C) Set.univ = 1-C Set.univ := by
    rw [Measure.sub_apply MeasurableSet.univ hP,measure_univ]
  have hmassQ : (Q-C) Set.univ = 1-C Set.univ := by
    rw [Measure.sub_apply MeasurableSet.univ hQ,measure_univ]
  rw [← Measure.sub_add_cancel_of_le hP,← Measure.sub_add_cancel_of_le hQ]; apply iSup_le
  intro E; simp only [Measure.add_apply]
  apply max_le
  · apply tsub_le_iff_right.mpr
    calc
      (P-C) E.val+C E.val ≤ (1-C Set.univ)+C E.val :=
        add_le_add ((measure_mono (Set.subset_univ _)).trans_eq hmassP) le_rfl
      _ ≤ (1-C Set.univ)+((Q-C) E.val+C E.val) := by gcongr; exact le_add_left le_rfl
  · apply tsub_le_iff_right.mpr
    calc
      (Q-C) E.val+C E.val ≤ (1-C Set.univ)+C E.val :=
        add_le_add ((measure_mono (Set.subset_univ _)).trans_eq hmassQ) le_rfl
      _ ≤ (1-C Set.univ)+((P-C) E.val+C E.val) := by gcongr; exact le_add_left le_rfl
private theorem subtype_tv (s : ActivePhase) (P Q : Measure (ValidTail s)) :
    measurableTotalVariation (P.map Subtype.val) (Q.map Subtype.val) =
      measurableTotalVariation P Q := by
  refine le_antisymm
    (measurable_total_variation_map_le P Q Subtype.val measurable_subtype_coe) ?_
  apply iSup_le
  intro E
  have hm : MeasurableSet (Subtype.val '' E.val : Set RawTail) := Set.to_countable _ |>.measurableSet
  have he : Subtype.val ⁻¹' (Subtype.val '' E.val : Set RawTail) = E.val :=
    Set.preimage_image_eq E.val Subtype.val_injective
  apply le_iSup_of_le ⟨Subtype.val '' E.val,hm⟩
  rw [Measure.map_apply measurable_subtype_coe hm, Measure.map_apply measurable_subtype_coe hm,he]
def rawLaw (s : ActivePhase) (z : Runtime) : Measure RawTail :=
  (lawfulTail s z).map Subtype.val
private theorem rawLaw_probability (s : ActivePhase) (z : Runtime) :
    IsProbabilityMeasure (rawLaw s z) := by
  haveI := lawfulTail_probability s z
  exact Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
private theorem rawLaw_finite (s : ActivePhase) (z : Runtime) (w : List Letter) :
    rawLaw s z {some w} =
      if ∃ b, WordFamily s b w then pathLaw z (rawPath ⁻¹' prefixCylinder w) else 0 := by
  classical
  have hr : Measurable rawPath := by unfold rawPath; fun_prop
  have hm : Measurable (fun p : ℕ → Marked =>
      NativeObserverJointLaw.validStopped s (fun n => (p n).2)) :=
    (NativeObserverJointLaw.validStopped_measurable s).comp hr
  rw [rawLaw,lawfulTail,Measure.map_map measurable_subtype_coe hm]
  change ((pathLaw z).map ((stoppedReadWord s) ∘ rawPath)) {some w} = _
  rw [Measure.map_apply ((measurable_stopped_read_word s).comp hr) (measurableSet_singleton _)]
  change pathLaw z ((fun p : ℕ → Marked => stoppedReadWord s (rawPath p)) ⁻¹' {some w}) = _
  have he : (fun p : ℕ → Marked => stoppedReadWord s (rawPath p)) ⁻¹' {some w} =
      if ∃ b, WordFamily s b w then rawPath ⁻¹' prefixCylinder w else ∅ := by
    ext p; simp only [Set.mem_preimage,Set.mem_singleton_iff,stopped_word_fiber]
    split_ifs with h <;> simp [prefixCylinder,h]
  rw [he]
  split_ifs <;> simp
private theorem raw_law_ext (P Q : Measure RawTail)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (he : ∀ w : List Letter, P {some w} = Q {some w}) : P = Q := by
  have hr : P.restrict ({none}ᶜ : Set RawTail) = Q.restrict ({none}ᶜ : Set RawTail) := by
    apply Measure.ext_of_singleton
    intro t
    cases t <;> simp [Measure.restrict_apply,he]
  have hpq : P ({none}ᶜ : Set RawTail) = Q ({none}ᶜ : Set RawTail) := by
    have hh := congrArg (fun R : Measure RawTail => R Set.univ) hr
    simpa using hh
  have hn : P {none} = Q {none} := by
    rw [← compl_compl ({none} : Set RawTail),
      measure_compl (measurableSet_singleton _).compl (measure_ne_top _ _),
      measure_compl (measurableSet_singleton _).compl (measure_ne_top _ _),hpq,
      measure_univ,measure_univ]
  exact Measure.ext_of_singleton (fun t => by cases t with
    | none => exact hn
    | some w => exact he w)
def specialBetaLaw : Measure RawTail :=
  ENNReal.ofReal (99/100) • Measure.dirac (some [1])+
    ENNReal.ofReal (1/100) • (explicitStoppedWordLaw .p ordinaryRate).map (prefixRaw 0)
def specialPLaw : Measure RawTail :=
  ENNReal.ofReal (9/10) • Measure.dirac (some [0])+
    ENNReal.ofReal (99/1000) • Measure.dirac (some [1,1])+
    ENNReal.ofReal (1/1000) •
      (explicitStoppedWordLaw .p ordinaryRate).map (prefixRaw 1 ∘ prefixRaw 0)
private theorem special_probability :
    IsProbabilityMeasure specialBetaLaw ∧ IsProbabilityMeasure specialPLaw := by
  haveI := ConstantSuspensionSeparator.endpoint_probability .p ordinaryRate
  haveI : IsProbabilityMeasure ((explicitStoppedWordLaw .p ordinaryRate).map (prefixRaw 0)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  haveI : IsProbabilityMeasure
      ((explicitStoppedWordLaw .p ordinaryRate).map (prefixRaw 1 ∘ prefixRaw 0)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  constructor <;> constructor <;>
    norm_num [specialBetaLaw,specialPLaw,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
      ← ENNReal.ofReal_add]
private theorem measure_le_of_singletons {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P Q : Measure X)
    (h : ∀ x, P {x} ≤ Q {x}) : P ≤ Q := by
  apply Measure.le_iff.mpr
  intro E hE
  conv_lhs => rw [← Measure.sum_smul_dirac P]
  conv_rhs => rw [← Measure.sum_smul_dirac Q]
  simp only [Measure.sum_apply _ hE,Measure.smul_apply,smul_eq_mul]
  apply ENNReal.tsum_le_tsum
  intro x; exact mul_le_mul' (h x) le_rfl
def sharedAtoms : ActivePhase → Measure RawTail
  | .p => ENNReal.ofReal (1/3) • Measure.dirac (some [0])+
      ENNReal.ofReal (9/25) • Measure.dirac (some [1,1])
  | .beta => ENNReal.ofReal (3/5) • Measure.dirac (some [1])
private theorem shared_finite (s : ActivePhase) : IsFiniteMeasure (sharedAtoms s) := by
  constructor
  cases s <;> simp [sharedAtoms,Measure.add_apply,Measure.smul_apply,smul_eq_mul]
def ordinaryErrorBound : ActivePhase → ℝ
  | .p => 23/75
  | .beta => 2/5
private theorem shared_mass (s : ActivePhase) :
    1-sharedAtoms s Set.univ = ENNReal.ofReal (ordinaryErrorBound s) := by
  cases s <;>
    simp only [sharedAtoms,ordinaryErrorBound,Measure.add_apply,Measure.smul_apply,
      smul_eq_mul,Measure.dirac_apply_of_mem (Set.mem_univ _),mul_one]
  all_goals
    norm_num [← ENNReal.ofReal_add]
    rw [← ENNReal.ofReal_one,← ENNReal.ofReal_sub 1 (by norm_num)]; norm_num
private theorem shared_endpoint (s : ActivePhase) (k : Depth) (hk : k = depthOne ∨ k = depthTwo) :
    sharedAtoms s ≤ explicitStoppedWordLaw s (rate k) := by
  apply measure_le_of_singletons
  intro t
  cases s with
  | p =>
    by_cases hα : t = some [0]
    · subst t
      have hf : ∃ b, WordFamily .p b [0] := ⟨0,0,rfl⟩
      rcases hk with rfl | rfl <;>
        norm_num [sharedAtoms,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
          explicit_finite_mass,hf,wordMass,bernoulliMeasure_apply,rate,depthOne,depthTwo,
          Nat.fib,alphaMass,betaMass] <;>
        apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (by finiteness)).mp <;>
        norm_num [ENNReal.toReal_mul,ENNReal.coe_toReal,unitInterval.coe_toNNReal]
    · by_cases hβ : t = some [1,1]
      · subst t
        have hf : ∃ b, WordFamily .p b [1,1] := ⟨1,0,rfl⟩
        rcases hk with rfl | rfl <;>
          norm_num [sharedAtoms,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
            explicit_finite_mass,hf,wordMass,bernoulliMeasure_apply,rate,depthOne,depthTwo,
            Nat.fib,alphaMass,betaMass] <;>
          apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (by finiteness)).mp <;>
          norm_num [ENNReal.toReal_mul,ENNReal.coe_toReal,unitInterval.coe_toNNReal]
      · simp [sharedAtoms,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
          Measure.dirac_apply',hα,hβ,eq_comm]
  | beta =>
    by_cases hβ : t = some [1]
    · subst t
      have hf : ∃ b, WordFamily .beta b [1] := ⟨1,Or.inl ⟨rfl,rfl⟩⟩
      rcases hk with rfl | rfl <;>
        norm_num [sharedAtoms,Measure.smul_apply,smul_eq_mul,explicit_finite_mass,hf,
          wordMass,bernoulliMeasure_apply,rate,depthOne,depthTwo,Nat.fib, alphaMass,betaMass] <;>
        apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (by finiteness)).mp <;>
        norm_num [ENNReal.toReal_mul,ENNReal.coe_toReal,unitInterval.coe_toNNReal]
    · simp [sharedAtoms,Measure.smul_apply,smul_eq_mul,Measure.dirac_apply',hβ,eq_comm]
private theorem shared_ordinary (s : ActivePhase) :
    sharedAtoms s ≤ explicitStoppedWordLaw s ordinaryRate := by
  have hr : ordinaryRate = rate depthTwo := by
    apply Subtype.ext
    norm_num [ordinaryRate,rate,depthTwo,Nat.fib]
  rw [hr]; exact shared_endpoint s depthTwo (Or.inr rfl)
private theorem zero_posterior_support (h : List Operation) (c : AcquiredNativeState)
    (hc : run h = some c) (k : Depth) (hk1 : k ≠ depthOne) (hk2 : k ≠ depthTwo) :
    posterior muZero h c hc k = 0 := by
  simp [posterior,PMF.normalize_apply,muZero,prior,weight,zeroParameter,hk1,hk2]
private theorem shared_posterior (s : ActivePhase) (h : List Operation)
    (c : AcquiredNativeState) (hc : run h = some c) :
    sharedAtoms s ≤ FourthSegmentLawRecovery.WordLaw.wordMixture (posterior muZero h c hc) s := by
  apply Measure.le_iff.mpr
  intro E hE
  let ν := posterior muZero h c hc
  rw [FourthSegmentLawRecovery.WordLaw.wordMixture,Measure.sum_apply _ hE]
  simp only [Measure.smul_apply,smul_eq_mul]
  calc
    sharedAtoms s E = (∑' k, ν k)*sharedAtoms s E := by rw [ν.tsum_coe,one_mul]
    _ = ∑' k, ν k*sharedAtoms s E := ENNReal.tsum_mul_right.symm
    _ ≤ ∑' k, ν k*explicitStoppedWordLaw s (rate k) E := by
      apply ENNReal.tsum_le_tsum
      intro k
      by_cases hk1 : k = depthOne
      · exact mul_le_mul' le_rfl ((shared_endpoint s k (Or.inl hk1)) E)
      · by_cases hk2 : k = depthTwo
        · exact mul_le_mul' le_rfl ((shared_endpoint s k (Or.inr hk2)) E)
        · simp [ν,zero_posterior_support h c hc k hk1 hk2]
private theorem full_error_raw (μ : PMF Depth) (s : ActivePhase)
    (H : NativeObserverJointLaw.PhaseHistory s) (z : Runtime)
    (hz : NativeObserverJointLaw.row actualObserver H.val.1 = PMF.pure z)
    (hg : historyGenerated H.val.1 = decoder z) :
    lawError μ H.val.1 H.val.2 = measurableTotalVariation (rawLaw s z)
      (FourthSegmentLawRecovery.WordLaw.wordMixture
        (posterior μ H.val.1 H.val.2 H.property.1) s) := by
  have ht := (NativeObserverJointLaw.native_history_risk_transport actualObserver μ s
    (fun _ => lawfulTail s)).1 H
  have hp : z ∈ (NativeObserverJointLaw.row actualObserver H.val.1).support := by
    rw [hz]; simp
  haveI := ht.1
  haveI := lawfulTail_probability s z
  rw [lawError,hg,actual_decoder_reconstruction μ s H z hp,ht.2.2.1,
    full_renderer_tv H.val.2 s H.property.2,← subtype_tv s,ht.2.2.2.1]
  rfl
private theorem mixture_probability (ν : PMF Depth) (s : ActivePhase) :
    IsProbabilityMeasure (FourthSegmentLawRecovery.WordLaw.wordMixture ν s) := by
  haveI (k : Depth) := ConstantSuspensionSeparator.endpoint_probability s (rate k)
  constructor; simp [FourthSegmentLawRecovery.WordLaw.wordMixture,Measure.sum_apply,
    Measure.smul_apply,smul_eq_mul,ν.tsum_coe]
private theorem ordinary_full_error (s : ActivePhase) (h : List Operation)
    (c : AcquiredNativeState) (hc : run h = some c)
    (hs : c.source.finiteFields.control = .fourth (.active s)) (z : Runtime)
    (hz : NativeObserverJointLaw.row actualObserver h = PMF.pure z)
    (hg : historyGenerated h = decoder z) (hm : z.mode = .ordinary) :
    lawError muZero h c ≤ ENNReal.ofReal (ordinaryErrorBound s) := by
  let H : NativeObserverJointLaw.PhaseHistory s := ⟨(h,c),hc,hs⟩
  rw [full_error_raw muZero s H z hz hg,show rawLaw s z = _ from ordinary_tail z hm s]
  haveI := mixture_probability (posterior muZero h c hc) s
  haveI := ConstantSuspensionSeparator.endpoint_probability s ordinaryRate
  haveI := shared_finite s
  exact (common_measure_tv _ _ (sharedAtoms s) (shared_ordinary s)
    (shared_posterior s h c hc)).trans_eq (shared_mass s)
private theorem raw_beta_step (z : Runtime) :
    rawLaw .beta z = betaMass (emissionParameter z) • Measure.dirac (some [1])+
      alphaMass (emissionParameter z) • (rawLaw .p (readAdvance z 0)).map (prefixRaw 0) := by
  haveI := rawLaw_probability .beta z
  haveI := rawLaw_probability .p (readAdvance z 0)
  haveI : IsProbabilityMeasure ((rawLaw .p (readAdvance z 0)).map (prefixRaw 0)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  haveI : IsProbabilityMeasure
      (betaMass (emissionParameter z) • Measure.dirac (some [1])+
        alphaMass (emissionParameter z) • (rawLaw .p (readAdvance z 0)).map (prefixRaw 0)) := by
    constructor
    simp [Measure.add_apply,Measure.smul_apply,smul_eq_mul,alphaMass,betaMass, ← ENNReal.coe_add]
  apply raw_law_ext
  intro w
  cases w with
  | nil =>
    rw [rawLaw_finite]; simp [← parses_normal_form,Parses,pendingColor,Measure.add_apply,
      Measure.smul_apply,smul_eq_mul,Measure.map_apply (measurable_of_countable _)
        (measurableSet_singleton _),prefixRaw,Set.preimage]
  | cons x w =>
    fin_cases x
    · change rawLaw .beta z {some ((0 : Letter) :: w)} =
        (betaMass (emissionParameter z) • Measure.dirac (some [1])+
          alphaMass (emissionParameter z) •
            (rawLaw .p (readAdvance z 0)).map (prefixRaw 0) : Measure RawTail) {some ((0 : Letter) :: w)}
      rw [rawLaw_finite,raw_prefix_cons]
      have hpre : prefixRaw 0 ⁻¹' {some ((0 : Letter) :: w)} = {some w} := by
        ext t
        cases t <;> simp [prefixRaw]
      rw [Measure.add_apply,Measure.smul_apply,Measure.smul_apply,
        Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),hpre,
        rawLaw_finite]
      simp [← parses_normal_form,Parses,pendingColor,totalRead,legalRead,
        bernoulliMeasure_apply,alphaMass,smul_eq_mul]
    · change rawLaw .beta z {some ((1 : Letter) :: w)} =
        (betaMass (emissionParameter z) • Measure.dirac (some [1])+
          alphaMass (emissionParameter z) •
            (rawLaw .p (readAdvance z 0)).map (prefixRaw 0) : Measure RawTail) {some ((1 : Letter) :: w)}
      rw [rawLaw_finite,raw_prefix_cons]
      have hpre : prefixRaw 0 ⁻¹' {some ((1 : Letter) :: w)} = ∅ := by
        ext t
        cases t <;> simp [prefixRaw]
      rw [Measure.add_apply,Measure.smul_apply,Measure.smul_apply,
        Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),hpre]
      cases w <;> simp [← parses_normal_form,Parses,pendingColor,totalRead,legalRead,
        bernoulliMeasure_apply,betaMass,smul_eq_mul,rawPath,prefixCylinder,Prefix,readPrefix]
private theorem raw_p_step (z : Runtime) :
    rawLaw .p z = alphaMass (emissionParameter z) • Measure.dirac (some [0])+
      betaMass (emissionParameter z) • (rawLaw .beta (readAdvance z 1)).map (prefixRaw 1) := by
  haveI := rawLaw_probability .p z
  haveI := rawLaw_probability .beta (readAdvance z 1)
  haveI : IsProbabilityMeasure ((rawLaw .beta (readAdvance z 1)).map (prefixRaw 1)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  haveI : IsProbabilityMeasure
      (alphaMass (emissionParameter z) • Measure.dirac (some [0])+
        betaMass (emissionParameter z) • (rawLaw .beta (readAdvance z 1)).map (prefixRaw 1)) := by
    constructor
    simp [Measure.add_apply,Measure.smul_apply,smul_eq_mul,alphaMass,betaMass, ← ENNReal.coe_add]
  apply raw_law_ext
  intro w
  cases w with
  | nil =>
    rw [rawLaw_finite]; simp [← parses_normal_form,Parses,pendingColor,Measure.add_apply,
      Measure.smul_apply,smul_eq_mul,Measure.map_apply (measurable_of_countable _)
        (measurableSet_singleton _),prefixRaw,Set.preimage]
  | cons x w =>
    fin_cases x
    · change rawLaw .p z {some ((0 : Letter) :: w)} =
        (alphaMass (emissionParameter z) • Measure.dirac (some [0])+
          betaMass (emissionParameter z) •
            (rawLaw .beta (readAdvance z 1)).map (prefixRaw 1) : Measure RawTail) {some ((0 : Letter) :: w)}
      rw [rawLaw_finite,raw_prefix_cons]
      have hpre : prefixRaw 1 ⁻¹' {some ((0 : Letter) :: w)} = ∅ := by
        ext t
        cases t <;> simp [prefixRaw]
      rw [Measure.add_apply,Measure.smul_apply,Measure.smul_apply,
        Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),hpre]
      cases w <;> simp [← parses_normal_form,Parses,pendingColor,totalRead,legalRead,
        bernoulliMeasure_apply,alphaMass,smul_eq_mul,rawPath,prefixCylinder,Prefix,readPrefix]
    · change rawLaw .p z {some ((1 : Letter) :: w)} =
        (alphaMass (emissionParameter z) • Measure.dirac (some [0])+
          betaMass (emissionParameter z) •
            (rawLaw .beta (readAdvance z 1)).map (prefixRaw 1) : Measure RawTail) {some ((1 : Letter) :: w)}
      rw [rawLaw_finite,raw_prefix_cons]
      have hpre : prefixRaw 1 ⁻¹' {some ((1 : Letter) :: w)} = {some w} := by
        ext t
        cases t <;> simp [prefixRaw]
      rw [Measure.add_apply,Measure.smul_apply,Measure.smul_apply,
        Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),hpre,
        rawLaw_finite]
      simp [← parses_normal_form,Parses,pendingColor,totalRead,legalRead,
        bernoulliMeasure_apply,betaMass,smul_eq_mul]
private theorem special_beta_tail (z : Runtime)
    (hs : z.fields.control = .fourth (.active .beta)) (hm : z.mode = .gBeta) :
    rawLaw .beta z = specialBetaLaw := by
  rcases z with ⟨⟨ctrl,r⟩,mon,m⟩
  dsimp at hs hm
  subst ctrl m; rw [raw_beta_step]
  have ha := (special_transactions r mon).2.2.1
  have he : (readAdvance ⟨⟨.fourth (.active .beta),r⟩,mon,.gBeta⟩ 0).mode = .ordinary := by
    simp [readAdvance,ha]
  rw [show rawLaw .p _ = _ from ordinary_tail _ he .p]
  unfold specialBetaLaw
  congr 1 <;> congr 1 <;>
    norm_num [alphaMass,betaMass,emissionParameter,selectedThreshold,queryMode,threshold,
      ← ENNReal.ofReal_coe_nnreal,unitInterval.coe_toNNReal]
private theorem special_p_tail (z : Runtime)
    (hs : z.fields.control = .fourth (.active .p)) (hm : z.mode = .g) :
    rawLaw .p z = specialPLaw := by
  rcases z with ⟨⟨ctrl,r⟩,mon,m⟩
  dsimp at hs hm
  subst ctrl m; rw [raw_p_step]
  have ha := (special_transactions r mon).2.1
  have hf : (readAdvance ⟨⟨.fourth (.active .p),r⟩,mon,.g⟩ 1).fields.control =
      .fourth (.active .beta) := by simp [readAdvance,ha]
  have he : (readAdvance ⟨⟨.fourth (.active .p),r⟩,mon,.g⟩ 1).mode = .gBeta := by
    simp [readAdvance,ha]
  rw [special_beta_tail _ hf he]
  unfold specialBetaLaw specialPLaw
  rw [Measure.map_add _ _ (measurable_of_countable _),Measure.map_smul,
    Measure.map_smul,Measure.map_dirac' (measurable_of_countable _) _,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    smul_add,smul_smul,smul_smul]
  have hα : alphaMass (emissionParameter ⟨⟨.fourth (.active .p),r⟩,mon,.g⟩) =
      ENNReal.ofReal (9/10) := by
    norm_num [alphaMass,emissionParameter,selectedThreshold,queryMode,threshold,
      ← ENNReal.ofReal_coe_nnreal,unitInterval.coe_toNNReal]
  have hβ : betaMass (emissionParameter ⟨⟨.fourth (.active .p),r⟩,mon,.g⟩) =
      ENNReal.ofReal (1/10) := by
    norm_num [betaMass,emissionParameter,selectedThreshold,queryMode,threshold,
      ← ENNReal.ofReal_coe_nnreal,unitInterval.coe_toNNReal]
  rw [hα,hβ]; norm_num [prefixRaw,← ENNReal.ofReal_mul,add_assoc]
private theorem zero_mixture (s : ActivePhase) (h : List Operation)
    (c : AcquiredNativeState) (hc : run h = some c) :
    FourthSegmentLawRecovery.WordLaw.wordMixture (posterior muZero h c hc) s =
      posterior muZero h c hc depthOne • explicitStoppedWordLaw s (rate depthOne)+
      posterior muZero h c hc depthTwo • explicitStoppedWordLaw s (rate depthTwo) := by
  apply Measure.ext
  intro E hE; rw [FourthSegmentLawRecovery.WordLaw.wordMixture,Measure.sum_apply _ hE,
    tsum_eq_sum (s := ({depthOne,depthTwo} : Finset Depth))]
  · simp [Measure.add_apply,Measure.smul_apply,depthOne,depthTwo]
  · intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hk
    simp [zero_posterior_support h c hc k hk.1 hk.2]
def endpointMean (h : List Operation) (c : AcquiredNativeState) (hc : run h = some c) : ℝ :=
  (posterior muZero h c hc depthOne).toReal/3+
    (posterior muZero h c hc depthTwo).toReal*(2/5)
private theorem zero_alpha_mass (h : List Operation) (c : AcquiredNativeState)
    (hc : run h = some c) :
    (FourthSegmentLawRecovery.WordLaw.wordMixture (posterior muZero h c hc) .p)
      {some [0]} = ENNReal.ofReal (endpointMean h c hc) := by
  rw [zero_mixture,Measure.add_apply,Measure.smul_apply,Measure.smul_apply]
  have hf : ∃ b, WordFamily .p b [0] := ⟨0,0,rfl⟩
  have h1 : explicitStoppedWordLaw .p (rate depthOne) {some [0]} = ENNReal.ofReal (1/3) := by
    norm_num [explicit_finite_mass,hf,wordMass,bernoulliMeasure_apply,rate,depthOne,Nat.fib,
      alphaMass,← ENNReal.ofReal_coe_nnreal,unitInterval.coe_toNNReal]
  have h2 : explicitStoppedWordLaw .p (rate depthTwo) {some [0]} = ENNReal.ofReal (2/5) := by
    norm_num [explicit_finite_mass,hf,wordMass,bernoulliMeasure_apply,rate,depthTwo,Nat.fib,
      alphaMass,← ENNReal.ofReal_coe_nnreal,unitInterval.coe_toNNReal]
  rw [h1,h2]; simp only [smul_eq_mul]
  have hν1 := (ENNReal.ofReal_toReal (PMF.apply_ne_top (posterior muZero h c hc) depthOne)).symm
  have hν2 := (ENNReal.ofReal_toReal (PMF.apply_ne_top (posterior muZero h c hc) depthTwo)).symm
  rw [hν1,hν2,← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; simp [endpointMean,div_eq_mul_inv]
private theorem special_beta_shared : sharedAtoms .beta ≤ specialBetaLaw := by
  apply measure_le_of_singletons
  intro t
  by_cases ht : t = some [1]
  · subst t
    have he : sharedAtoms .beta {some [1]} ≤
        (ENNReal.ofReal (99/100) • Measure.dirac (some [1]) : Measure RawTail) {some [1]} := by
      norm_num [sharedAtoms,Measure.smul_apply,smul_eq_mul]
    exact he.trans (Measure.le_iff.mp (Measure.le_add_right le_rfl) _ (measurableSet_singleton _))
  · simp [sharedAtoms,Measure.smul_apply,Measure.dirac_apply',ht,eq_comm]
private theorem special_beta_error (H : NativeObserverJointLaw.PhaseHistory .beta)
    (z : Runtime) (hz : NativeObserverJointLaw.row actualObserver H.val.1 = PMF.pure z)
    (hg : historyGenerated H.val.1 = decoder z) (hf : z.fields = H.val.2.source.finiteFields)
    (hm : z.mode = .gBeta) : lawError muZero H.val.1 H.val.2 ≤ ENNReal.ofReal (2/5) := by
  rw [full_error_raw muZero .beta H z hz hg,special_beta_tail z (hf ▸ H.property.2) hm]
  haveI := special_probability.1
  haveI := mixture_probability
    (posterior muZero H.val.1 H.val.2 H.property.1) .beta
  haveI := shared_finite .beta
  exact (common_measure_tv _ _ (sharedAtoms .beta) special_beta_shared
    (shared_posterior .beta _ _ _)).trans_eq (shared_mass .beta)
def G0Law : Measure RawTail :=
  ENNReal.ofReal (9/10) • Measure.dirac (some [0])+
    ENNReal.ofReal (1/10) • Measure.dirac (some [1,1])
private theorem G0_probability : IsProbabilityMeasure G0Law := by
  constructor
  norm_num [G0Law,Measure.add_apply,Measure.smul_apply,smul_eq_mul,← ENNReal.ofReal_add]
private theorem zero_alpha_upper (h : List Operation) (c : AcquiredNativeState)
    (hc : run h = some c) :
    (FourthSegmentLawRecovery.WordLaw.wordMixture (posterior muZero h c hc) .p)
      {some [0]} ≤ ENNReal.ofReal (2/5) := by
  let ν := posterior muZero h c hc
  rw [FourthSegmentLawRecovery.WordLaw.wordMixture,Measure.sum_apply_of_countable]
  simp only [Measure.smul_apply,smul_eq_mul]
  calc
    (∑' k, ν k*explicitStoppedWordLaw .p (rate k) {some [0]}) ≤
        ∑' k, ν k*ENNReal.ofReal (2/5) := by
      apply ENNReal.tsum_le_tsum
      intro k
      by_cases hk1 : k = depthOne
      · subst k
        have hf : ∃ b, WordFamily .p b [0] := ⟨0,0,rfl⟩
        apply mul_le_mul' le_rfl
        norm_num [explicit_finite_mass,hf,wordMass,bernoulliMeasure_apply,rate,depthOne,Nat.fib,
          alphaMass,← ENNReal.ofReal_coe_nnreal,unitInterval.coe_toNNReal]
      · by_cases hk2 : k = depthTwo
        · subst k
          have hf : ∃ b, WordFamily .p b [0] := ⟨0,0,rfl⟩
          apply mul_le_mul' le_rfl
          norm_num [explicit_finite_mass,hf,wordMass,bernoulliMeasure_apply,rate,depthTwo,Nat.fib,
            alphaMass,← ENNReal.ofReal_coe_nnreal,unitInterval.coe_toNNReal]
        · simp [ν,zero_posterior_support h c hc k hk1 hk2]
    _ = _ := by rw [ENNReal.tsum_mul_right,ν.tsum_coe,one_mul]
private theorem G0_exact_tv (H : NativeObserverJointLaw.PhaseHistory .p) :
    measurableTotalVariation G0Law (FourthSegmentLawRecovery.WordLaw.wordMixture
        (posterior muZero H.val.1 H.val.2 H.property.1) .p) =
      ENNReal.ofReal (9/10-endpointMean H.val.1 H.val.2 H.property.1) := by
  let Q := FourthSegmentLawRecovery.WordLaw.wordMixture
    (posterior muZero H.val.1 H.val.2 H.property.1) .p
  let C : Measure RawTail := Q {some [0]} • Measure.dirac (some [0])+
    ENNReal.ofReal (1/10) • Measure.dirac (some [1,1])
  haveI := mixture_probability (posterior muZero H.val.1 H.val.2 H.property.1) .p
  haveI := G0_probability
  haveI : IsFiniteMeasure C := by
    constructor; simp [C,Measure.add_apply,Measure.smul_apply,smul_eq_mul]
  have hA : Q {some [0]} ≤ ENNReal.ofReal (9/10) :=
    (zero_alpha_upper _ _ _).trans (by norm_num)
  have hB : ENNReal.ofReal (1/10) ≤ Q {some [1,1]} := by
    have h := shared_posterior .p H.val.1 H.val.2 H.property.1
    have hh := h {some [1,1]}
    norm_num [sharedAtoms,Measure.add_apply,Measure.smul_apply,smul_eq_mul] at hh
    exact (show ENNReal.ofReal (1/10) ≤ ENNReal.ofReal (9/25) by norm_num).trans hh
  have hCP : C ≤ G0Law := by
    apply measure_le_of_singletons
    intro t
    by_cases hα : t = some [0]
    · subst t; simpa [C,G0Law,Measure.add_apply,Measure.smul_apply,smul_eq_mul] using hA
    · by_cases hβ : t = some [1,1]
      · subst t; simp [C,G0Law,Measure.add_apply,Measure.smul_apply,smul_eq_mul]
      · simp [C,Measure.add_apply,Measure.smul_apply,Measure.dirac_apply',hα,hβ,eq_comm]
  have hCQ : C ≤ Q := by
    apply measure_le_of_singletons
    intro t
    by_cases hα : t = some [0]
    · subst t; simp [C,Measure.add_apply,Measure.smul_apply,smul_eq_mul]
    · by_cases hβ : t = some [1,1]
      · subst t; simpa [C,Measure.add_apply,Measure.smul_apply,smul_eq_mul] using hB
      · simp [C,Measure.add_apply,Measure.smul_apply,Measure.dirac_apply',hα,hβ,eq_comm]
  have hmass : 1-C Set.univ = ENNReal.ofReal (9/10)-Q {some [0]} := by
    simp only [C,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
      Measure.dirac_apply_of_mem (Set.mem_univ _),mul_one]
    rw [add_comm,tsub_add_eq_tsub_tsub]
    congr 1; rw [← ENNReal.ofReal_one,← ENNReal.ofReal_sub 1 (by norm_num)]
    norm_num
  have hgap : ENNReal.ofReal (9/10)-Q {some [0]} =
      ENNReal.ofReal (9/10-endpointMean H.val.1 H.val.2 H.property.1) := by
    rw [show Q {some [0]} = _ from zero_alpha_mass _ _ _,← ENNReal.ofReal_sub (9/10) (by
      unfold endpointMean; positivity)]
  apply le_antisymm
  · exact (common_measure_tv G0Law Q C hCP hCQ).trans_eq (hmass.trans hgap)
  · rw [← hgap]
    apply le_trans _ (le_iSup (fun E : {E : Set RawTail // MeasurableSet E} =>
      max (G0Law E.val-Q E.val) (Q E.val-G0Law E.val)) ⟨{some [0]},measurableSet_singleton _⟩)
    simp [G0Law,Measure.add_apply,Measure.smul_apply,smul_eq_mul]
private theorem G_exact_deviation : measurableTotalVariation specialPLaw G0Law = ENNReal.ofReal (1/1000) := by
  let C : Measure RawTail := ENNReal.ofReal (9/10) • Measure.dirac (some [0])+
    ENNReal.ofReal (99/1000) • Measure.dirac (some [1,1])
  haveI := special_probability.2
  haveI := G0_probability
  haveI : IsFiniteMeasure C := by
    constructor; simp [C,Measure.add_apply,Measure.smul_apply,smul_eq_mul]
  have hCP : C ≤ specialPLaw := Measure.le_add_right le_rfl
  have hCQ : C ≤ G0Law := by
    apply Measure.le_iff.mpr
    intro E hE; simp only [C,G0Law,Measure.add_apply,Measure.smul_apply,smul_eq_mul]
    exact add_le_add le_rfl (mul_le_mul' (by norm_num) le_rfl)
  have hmass : 1-C Set.univ = ENNReal.ofReal (1/1000) := by
    norm_num [C,Measure.add_apply,Measure.smul_apply,smul_eq_mul,← ENNReal.ofReal_add]
    rw [← ENNReal.ofReal_one,← ENNReal.ofReal_sub 1 (by norm_num)]; norm_num
  have hempty : (prefixRaw 1 ∘ prefixRaw 0) ⁻¹' {some ([1,1] : List Letter)} = ∅ := by
    ext t
    cases t <;> simp [prefixRaw]
  apply le_antisymm
  · exact (common_measure_tv specialPLaw G0Law C hCP hCQ).trans_eq hmass
  · apply le_trans _ (le_iSup (fun E : {E : Set RawTail // MeasurableSet E} =>
      max (specialPLaw E.val-G0Law E.val) (G0Law E.val-specialPLaw E.val))
      ⟨{some [1,1]},measurableSet_singleton _⟩)
    change ENNReal.ofReal (1/1000) ≤
      max (specialPLaw {some [1,1]}-G0Law {some [1,1]})
        (G0Law {some [1,1]}-specialPLaw {some [1,1]})
    simp only [specialPLaw,G0Law,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
      Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),hempty]
    norm_num
    right
    rw [← ENNReal.ofReal_sub (1/10) (by norm_num : (0 : ℝ) ≤ 99/1000)]; norm_num
private theorem special_p_error (H : NativeObserverJointLaw.PhaseHistory .p)
    (z : Runtime) (hz : runtimeRun H.val.1 = some z)
    (hrow : NativeObserverJointLaw.row actualObserver H.val.1 = PMF.pure z)
    (hg : historyGenerated H.val.1 = decoder z) (hf : z.fields = H.val.2.source.finiteFields)
    (hm : z.mode = .g) : lawError muZero H.val.1 H.val.2 ≤ ENNReal.ofReal (253/500) := by
  obtain ⟨n,hn,hh⟩ := (exhaustive_history_modes H.val.1 z hz).1 hm
  have hrun := ((long_history_concentration (shortParameter 0) (every_short_history 0).1).1 n).1
  have hc : H.val.2 = longState n := by
    have hr : run H.val.1 = some (longState n) := by
      rw [show H.val.1 = longHistory n from hh]; exact hrun
    exact Option.some.inj (H.property.1.symm.trans hr)
  have hcal : 79/200 < endpointMean H.val.1 H.val.2 H.property.1 := by
    simpa only [show H.val.1 = longHistory n from hh,hc,endpointMean] using
      (long_endpoint_calibration n hn).2.2.1
  rw [full_error_raw muZero .p H z hrow hg,special_p_tail z (hf ▸ H.property.2) hm]
  have htv := measurable_total_variation_triangle specialPLaw G0Law
    (FourthSegmentLawRecovery.WordLaw.wordMixture (posterior muZero H.val.1 H.val.2 H.property.1) .p)
  rw [G_exact_deviation,G0_exact_tv H] at htv
  refine htv.trans ?_
  have hnonneg : 0 ≤ 9/10-endpointMean H.val.1 H.val.2 H.property.1 := by
    have hα := zero_alpha_upper H.val.1 H.val.2 H.property.1
    rw [zero_alpha_mass] at hα; have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hα
    have hp : 0 ≤ endpointMean H.val.1 H.val.2 H.property.1 := by unfold endpointMean; positivity
    norm_num [hp] at hh
    linarith
  rw [← ENNReal.ofReal_add (by norm_num) hnonneg]; apply ENNReal.ofReal_le_ofReal
  linarith
private theorem actual_special_phase (h : List Operation) (c : AcquiredNativeState)
    (hc : run h = some c) (z : Runtime) (hz : runtimeRun h = some z)
    (hrow : NativeObserverJointLaw.row actualObserver h = PMF.pure z) :
    (z.mode = .g → z.fields.control = .fourth (.active .p)) ∧
    (z.mode = .gBeta → z.fields.control = .fourth (.active .beta)) := by
  have he := exhaustive_history_modes h z hz
  constructor
  · intro hm
    obtain ⟨n,hn,hh⟩ := he.1 hm
    have hr := (original_latch_activation n hn).1
    rw [← hh,hz] at hr; have hzz := Option.some.inj hr
    rw [hzz]; rfl
  · intro hm
    obtain ⟨n,hn,hh⟩ := he.2.1 hm
    have hr := ((long_history_concentration (shortParameter 0) (every_short_history 0).1).1 n).1
    obtain ⟨q,hq,hf,hrq,hnq⟩ := deterministic_actual_rows (longHistory n) (longState n) hr
    have hqeq : q = ⟨latchedFields,.accepted,.g⟩ := by
      have hrl := (original_latch_activation n hn).1
      rw [show reads (blocks n ++ latchWord) = longHistory n from rfl,hq] at hrl
      exact Option.some.inj hrl
    have hrnext := hnq (.read 1)
    rw [hqeq] at hrnext; have hhist : h = longHistory n ++ [.read 1] := by
      simpa [longHistory,reads,List.map_append] using hh
    rw [← hhist,hrow] at hrnext
    have hzq : z = (runtimeStep ⟨latchedFields,.accepted,.g⟩ (.read 1)).getD
        ⟨latchedFields,.accepted,.g⟩ := by
      apply (PMF.mem_support_pure_iff _ _).mp
      change z ∈ (actualUpdate (.read 1) ⟨latchedFields,.accepted,.g⟩).support
      rw [← hrnext]
      simp
    rw [hzq]; simp [latchedFields,runtimeStep,finiteStep,finiteRead,payloadRead,payloadControl,
      completionControl]
def absoluteBound : ActivePhase → ℝ
  | .p => 253/500
  | .beta => 2/5
private theorem all_history_error (s : ActivePhase) (H : NativeObserverJointLaw.PhaseHistory s) :
    lawError muZero H.val.1 H.val.2 ≤ ENNReal.ofReal (absoluteBound s) := by
  obtain ⟨z,hz,hf,hrow,hg,hnext⟩ :=
    (history_marginal_compatibility muZero H.val.1 H.val.2 H.property.1).2
  have hn := actual_not_watching H.val.1 z hz s (hf ▸ H.property.2)
  have hsp := actual_special_phase H.val.1 H.val.2 H.property.1 z hz hrow
  cases hm : z.mode with
  | watching => exact (hn hm).elim
  | ordinary =>
    exact (ordinary_full_error s _ _ H.property.1 H.property.2 z hrow hg hm).trans
      (by cases s <;> norm_num [ordinaryErrorBound,absoluteBound])
  | g =>
    have hs : s = .p := by
      have he := (hsp.1 hm).symm.trans (hf ▸ H.property.2)
      simpa using he.symm
    subst s; exact special_p_error H z hz hrow hg hf hm
  | gBeta =>
    have hs : s = .beta := by
      have he := (hsp.2 hm).symm.trans (hf ▸ H.property.2)
      simpa using he.symm
    subst s; exact special_beta_error H z hrow hg hf hm
private theorem short_le_phase (μ : PMF Depth) (s : ActivePhase) (H : ℕ) :
    shortLawRisk μ s H ≤ phaseLawRisk μ s := by
  apply iSup_le
  intro p
  exact le_iSup (fun q : NativeObserverJointLaw.PhaseHistory s => lawError μ q.val.1 q.val.2) p.val
private theorem cap_mono (μ : PMF Depth) (s : ActivePhase) (H K : ℕ) (hHK : H ≤ K) :
    shortLawRisk μ s H ≤ shortLawRisk μ s K := by
  apply iSup_le
  intro p; exact le_iSup (fun q : {q : NativeObserverJointLaw.PhaseHistory s //
    (readLetters q.val.1).length ≤ K} => lawError μ q.val.val.1 q.val.val.2)
    ⟨p.val,p.property.trans hHK⟩
private theorem terminal_actual_error (μ : PMF Depth) (h : List Operation)
    (c : AcquiredNativeState) (hc : run h = some c)
    (ht : (∃ b, c.source.finiteFields.control = .fourth (.pending b)) ∨
      c.source.finiteFields.control = .fourth .delivered) :
    lawError μ h c = 0 ∧ confError μ h c = 0 := by
  obtain ⟨z,hz,hf,hrow,hg,hnext⟩ := (history_marginal_compatibility μ h c hc).2
  have hzt : (∃ b, z.fields.control = .fourth (.pending b)) ∨
      z.fields.control = .fourth .delivered := by simpa only [hf] using ht
  have hn : jointLaw μ (nativeEvent h c) ≠ 0 := by
    rw [history_mass μ h c hc]; exact ne_of_gt (normalizer_bounds μ h c hc).1
  haveI := ProbabilityTheory.cond_isProbabilityMeasure hn
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond
      (NativeObserverJointLaw.actualLaw actualObserver μ h.length) (nativeEvent h c ×ˢ Set.univ)) := by
    rw [NativeObserverJointLaw.conditional_history_product actualObserver μ h c hc]
    infer_instance
  have htarget : NativeObserverJointLaw.fullTarget actualObserver μ h c = decoder z := by
    rw [terminal_dirac z hzt]
    unfold NativeObserverJointLaw.fullTarget
    calc
      _ = (ProbabilityTheory.cond (NativeObserverJointLaw.actualLaw actualObserver μ h.length)
          (nativeEvent h c ×ˢ Set.univ)).map
          (fun _ => renderPath z (fun _ => (z,0))) := by
        apply Measure.map_congr
        apply Filter.Eventually.of_forall
        intro t
        dsimp only
        rw [(full_fields_factorization c _).1,← hf]
        exact terminal_constant z hzt (fun n => (z,rawTail t.1.2 (readLetters h).length n)) _
      _ = _ := by simp
  have herr : lawError μ h c = 0 := by
    rw [lawError,hg,htarget]; simp [measurableTotalVariation]
  refine ⟨herr,?_⟩
  rw [(complete_record_risk_bridges (shortParameter 0) (every_short_history 0).1).1 μ h c hc |>.1,herr]
/-- Every actual fourth query is classified by its retained runtime. Complete
    stopped-word laws and the original record renderer use the same actual row. -/
theorem runtime_law_risk_bridge :
    (∀ (s : ActivePhase) (z : Runtime), IsProbabilityMeasure (lawfulTail s z)) ∧
    (∀ (μ : PMF Depth) (s : ActivePhase) (H : NativeObserverJointLaw.PhaseHistory s)
      (z : Runtime), z ∈ (NativeObserverJointLaw.row actualObserver H.val.1).support →
        decoder z = (lawfulTail s z).map (fullRenderer H.val.2 s)) ∧
    (∀ (μ : PMF Depth) (s : ActivePhase),
      NativeObserverJointLaw.fullRisk actualObserver μ s (fun _ => lawfulTail s) = phaseConfRisk μ s ∧
      NativeObserverJointLaw.rawRisk actualObserver μ s (fun _ => lawfulTail s) = phaseLawRisk μ s) ∧
    (∀ (s : ActivePhase) (H : NativeObserverJointLaw.PhaseHistory s),
      ∃ z : Runtime, runtimeRun H.val.1 = some z ∧ z.fields = H.val.2.source.finiteFields ∧
        NativeObserverJointLaw.row actualObserver H.val.1 = PMF.pure z ∧
        historyGenerated H.val.1 = decoder z ∧ z.mode ≠ .watching ∧
        ((z.mode = .ordinary ∧ rawLaw s z = explicitStoppedWordLaw s ordinaryRate) ∨
          (s = .p ∧ z.mode = .g ∧ rawLaw s z = specialPLaw) ∨
          (s = .beta ∧ z.mode = .gBeta ∧ rawLaw s z = specialBetaLaw))) ∧
    (∀ (z : Runtime) (x : Letter), z.mode = .ordinary → (readAdvance z x).mode = .ordinary) := by
  refine ⟨lawfulTail_probability,actual_decoder_reconstruction,native_risk_eq,?_,fun z x hm => ordinary_advance z hm x⟩
  intro s H
  obtain ⟨z,hz,hf,hrow,hg,hnext⟩ :=
    (history_marginal_compatibility muZero H.val.1 H.val.2 H.property.1).2
  have hn := actual_not_watching H.val.1 z hz s (hf ▸ H.property.2)
  have hsp := actual_special_phase H.val.1 H.val.2 H.property.1 z hz hrow
  refine ⟨z,hz,hf,hrow,hg,hn,?_⟩
  cases hm : z.mode with
  | watching => exact (hn hm).elim
  | ordinary => exact Or.inl ⟨rfl,ordinary_tail z hm s⟩
  | g =>
    have hs : s = .p := by
      have hctrl := ((hsp.1 hm).symm.trans (hf ▸ H.property.2)).symm
      cases s <;> simp_all
    subst s; exact Or.inr (Or.inl ⟨rfl,rfl,special_p_tail z (hf ▸ H.property.2) hm⟩)
  | gBeta =>
    have hs : s = .beta := by
      have hctrl := ((hsp.2 hm).symm.trans (hf ▸ H.property.2)).symm
      cases s <;> simp_all
    subst s; exact Or.inr (Or.inr ⟨rfl,rfl,special_beta_tail z (hf ▸ H.property.2) hm⟩)
/-- Absolute complete-record estimates hold on every original phase history.
    The capped rare-prior estimates retain non-strict supremum bounds. -/
theorem all_history_absolute_risks :
    (∀ (s : ActivePhase) (H : NativeObserverJointLaw.PhaseHistory s),
      lawError muZero H.val.1 H.val.2 ≤ ENNReal.ofReal (absoluteBound s) ∧
      confError muZero H.val.1 H.val.2 ≤ ENNReal.ofReal (absoluteBound s)) ∧
    (∀ s : ActivePhase, (phaseLawRisk muZero s).toReal ≤ absoluteBound s ∧
      (phaseConfRisk muZero s).toReal ≤ absoluteBound s) ∧ (∀ (s : ActivePhase) (H : ℕ),
      (shortLawRisk (prior (shortParameter H)) s H).toReal ≤ absoluteBound s+1/1000 ∧
      (shortConfRisk (prior (shortParameter H)) s H).toReal ≤ absoluteBound s+1/1000) ∧
    (∀ (μ : PMF Depth) (s : ActivePhase) (H K : ℕ), H ≤ K →
      shortLawRisk μ s H ≤ shortLawRisk μ s K ∧ shortConfRisk μ s H ≤ shortConfRisk μ s K) ∧
    (∀ (μ : PMF Depth) (h : List Operation) (c : AcquiredNativeState), run h = some c →
      ((∃ b, c.source.finiteFields.control = .fourth (.pending b)) ∨
        c.source.finiteFields.control = .fourth .delivered) →
      lawError μ h c = 0 ∧ confError μ h c = 0) := by
  have he := complete_record_risk_bridges (shortParameter 0) (every_short_history 0).1
  have hphase (s : ActivePhase) : phaseLawRisk muZero s ≤ ENNReal.ofReal (absoluteBound s) :=
    iSup_le (all_history_error s)
  have hreal (s : ActivePhase) : (phaseLawRisk muZero s).toReal ≤ absoluteBound s := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hphase s)
    simpa [ENNReal.toReal_ofReal,show 0 ≤ absoluteBound s from by cases s <;> norm_num [absoluteBound]] using h
  refine ⟨?_,?_,?_,?_,terminal_actual_error⟩
  · intro s H
    rw [(he.1 muZero H.val.1 H.val.2 H.property.1).1]
    exact ⟨all_history_error s H,all_history_error s H⟩
  · intro s
    rw [(he.2.1 muZero s).1]; exact ⟨hreal s,hreal s⟩
  · intro s H
    have hr := (complete_record_risk_bridges (shortParameter H) (every_short_history H).1).2.2.1 s H
    have hf := (he.2.1 muZero s).2.1
    have hb := (ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top hf)
      (short_le_phase muZero s H)).trans (hreal s)
    rw [((he.2.1 (prior (shortParameter H)) s).2.2 H).1]
    exact ⟨hr.trans (by linarith),hr.trans (by linarith)⟩
  · intro μ s H K hHK
    rw [((he.2.1 μ s).2.2 H).1,((he.2.1 μ s).2.2 K).1]
    exact ⟨cap_mono μ s H K hHK,cap_mono μ s H K hHK⟩
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorAbsoluteRisk
