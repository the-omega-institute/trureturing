/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorThreePoint
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorThreePoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational rare three-point priors control every short native posterior. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorGeneratedLaw
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorReferenceScalar
import D5.S3.Estimation.DataProcessing.MeasurableTotalVariationTriangle

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorThreePoint
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open NativeConditionalControl.DepthLaw
open RarePriorFiniteMonitor
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open Filter
open scoped Topology

def depthOne : Depth := ⟨1,by decide⟩
def depthTwo : Depth := ⟨2,by decide⟩
def depthThree : Depth := ⟨3,by decide⟩

structure Parameter where
  value : ℚ
  nonneg : 0 ≤ value
  small : value ≤ 1/2

def weight (t : Parameter) (k : Depth) : ℝ≥0∞ :=
  if k = depthOne then ENNReal.ofReal ((1-(t.value : ℝ))/2)
  else if k = depthTwo then ENNReal.ofReal ((1-(t.value : ℝ))/2)
  else if k = depthThree then ENNReal.ofReal (t.value : ℝ) else 0

private theorem weight_sum (t : Parameter) :
    ∑ k ∈ ({depthOne,depthTwo,depthThree} : Finset Depth), weight t k = 1 := by
  have ht0 : 0 ≤ (t.value : ℝ) := by exact_mod_cast t.nonneg
  have ht1 : (t.value : ℝ) ≤ ((1/2 : ℚ) : ℝ) := by exact_mod_cast t.small
  norm_num at ht1
  have hbase : 0 ≤ (1-(t.value : ℝ))/2 := by linarith
  norm_num [weight,depthOne,depthTwo,depthThree]
  rw [← ENNReal.ofReal_add hbase ht0,← ENNReal.ofReal_add hbase (by positivity)]
  convert ENNReal.ofReal_one using 1
  congr 1
  ring

def prior (t : Parameter) : PMF Depth :=
  PMF.ofFinset (weight t) {depthOne,depthTwo,depthThree} (weight_sum t) (by
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hk
    simp [weight,hk.1,hk.2.1,hk.2.2])

def zeroParameter : Parameter := ⟨0,by norm_num,by norm_num⟩
def muZero : PMF Depth := prior zeroParameter

def lambdaQ (H : ℕ) : ℚ := 1/(2000*(9/8)^H+1)

private theorem lambda_bounds (H : ℕ) : 0 < lambdaQ H ∧ lambdaQ H ≤ 1/2 := by
  have hp : (1 : ℚ) ≤ (9/8)^H := one_le_pow₀ (by norm_num)
  unfold lambdaQ
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hp]

def shortParameter (H : ℕ) : Parameter :=
  ⟨lambdaQ H,(lambda_bounds H).1.le,(lambda_bounds H).2⟩

/-- Real source cylinder mass, before conditioning and without a runtime argument. -/
def realMass (k : Depth) : List Letter → ℝ
  | [] => 1
  | x :: w => ((bernoulliMeasure (0 : Letter) 1 (rate k)) {x}).toReal * realMass k w

private theorem mass_actual (k : Depth) (w : List Letter) :
    (wordMass (rate k) w).toReal = realMass k w := by
  induction w with
  | nil => simp [wordMass,realMass]
  | cons x w ih =>
    change (((bernoulliMeasure (0 : Letter) 1 (rate k)) {x}) * wordMass (rate k) w).toReal = _
    rw [ENNReal.toReal_mul,ih]
    rfl

private theorem mass_nonneg (k : Depth) (w : List Letter) : 0 ≤ realMass k w := by
  rw [← mass_actual]
  exact ENNReal.toReal_nonneg

private theorem atom_real (k : Depth) (x : Letter) :
    ((bernoulliMeasure (0 : Letter) 1 (rate k)) {x}).toReal =
      if x = 0 then (rate k : ℝ) else 1-(rate k : ℝ) := by
  fin_cases x <;> simp [bernoulliMeasure_apply,unitInterval.coe_toNNReal]

private theorem mass_pos (k : Depth) (w : List Letter) : 0 < realMass k w := by
  induction w with
  | nil => norm_num [realMass]
  | cons x w ih =>
    have hr := ratio_interior k
    rw [realMass,atom_real]
    split_ifs
    · exact mul_pos hr.1 ih
    · exact mul_pos (sub_pos.mpr hr.2) ih

private theorem rare_ratio (w : List Letter) :
    realMass depthThree w ≤ (9/8 : ℝ)^w.length*realMass depthOne w := by
  induction w with
  | nil => norm_num [realMass]
  | cons x w ih =>
    have hn := mass_nonneg depthThree w
    have h1 := mass_nonneg depthOne w
    fin_cases x <;>
      simp only [realMass,atom_real,List.length_cons,pow_succ] at ⊢
    all_goals
      norm_num [rate,depthOne,depthThree,Nat.fib_add_two] at ⊢
    all_goals norm_num [depthOne,depthThree] at ih hn h1
    all_goals nlinarith only [ih,hn,
      mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 9/8) w.length) h1]

private theorem normalizer_three (t : Parameter) (ops : List Operation) :
    normalizer (prior t) ops =
      weight t depthOne*likelihood ops depthOne+
      weight t depthTwo*likelihood ops depthTwo+
      weight t depthThree*likelihood ops depthThree := by
  unfold normalizer
  rw [tsum_eq_sum (s := ({depthOne,depthTwo,depthThree} : Finset Depth))]
  · norm_num [prior,PMF.ofFinset_apply,depthOne,depthTwo,depthThree,add_assoc]
  · intro k hk
    have hzero : prior t k = 0 := by
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hk
      simp [prior,weight,hk.1,hk.2.1,hk.2.2]
    rw [hzero,zero_mul]

private theorem posterior_at (t : Parameter) (ops : List Operation)
    (c : AcquiredNativeState) (hc : run ops = some c) (k : Depth) :
    ((posterior (prior t) ops c hc) k).toReal =
      (weight t k).toReal*realMass k (readLetters ops)/
        (((1-(t.value : ℝ))/2)*realMass depthOne (readLetters ops)+
         ((1-(t.value : ℝ))/2)*realMass depthTwo (readLetters ops)+
         (t.value : ℝ)*realMass depthThree (readLetters ops)) := by
  have ht0 : 0 ≤ (t.value : ℝ) := by exact_mod_cast t.nonneg
  have ht1 : (t.value : ℝ) ≤ ((1/2 : ℚ) : ℝ) := by exact_mod_cast t.small
  norm_num at ht1
  have hb : 0 ≤ (1-(t.value : ℝ))/2 := by linarith
  have hp (k : Depth) : likelihood ops k ≠ ⊤ := by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (by
      unfold likelihood
      rw [← cylinder_mass]
      exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ)
  simp only [posterior,PMF.normalize_apply,ENNReal.toReal_mul,ENNReal.toReal_inv]
  change ((prior t) k).toReal * (likelihood ops k).toReal *
    (normalizer (prior t) ops).toReal⁻¹ = _
  rw [normalizer_three]
  have hw (k : Depth) : weight t k ≠ ⊤ := (prior t).apply_ne_top k
  have hmul (k : Depth) : weight t k * likelihood ops k ≠ ⊤ :=
    ENNReal.mul_ne_top (hw k) (hp k)
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hmul _,hmul _⟩) (hmul _),
    ENNReal.toReal_add (hmul _) (hmul _)]
  simp only [prior,PMF.ofFinset_apply] at ⊢
  simp only [weight,
    show depthThree ≠ depthOne from by decide,
    show depthThree ≠ depthTwo from by decide,
    show depthTwo ≠ depthOne from by decide,
    if_false,if_pos rfl,ite_true,eq_self_iff_true]
  simp only [ite_true,ENNReal.toReal_ofReal ht0,ENNReal.toReal_ofReal hb,
    ENNReal.toReal_mul,likelihood,mass_actual]
  rfl

private theorem posterior_real (t : Parameter) (ops : List Operation)
    (c : AcquiredNativeState) (hc : run ops = some c) :
    ((posterior (prior t) ops c hc) depthThree).toReal =
      (t.value : ℝ)*realMass depthThree (readLetters ops)/
        (((1-(t.value : ℝ))/2)*realMass depthOne (readLetters ops)+
         ((1-(t.value : ℝ))/2)*realMass depthTwo (readLetters ops)+
         (t.value : ℝ)*realMass depthThree (readLetters ops)) := by
  have ht0 : 0 ≤ (t.value : ℝ) := by exact_mod_cast t.nonneg
  simpa [weight,depthOne,depthTwo,depthThree,ENNReal.toReal_ofReal ht0]
    using posterior_at t ops c hc depthThree

/-- All short legal histories, including prelude and terminal histories, share
    the same rare posterior bound under one rational normalized prior. -/
theorem every_short_history (H : ℕ) :
    0 < (shortParameter H).value ∧
    (∀ k : Depth, prior (shortParameter H) k = weight (shortParameter H) k) ∧
    (∀ (ops : List Operation) (c : AcquiredNativeState) (hc : run ops = some c),
      (readLetters ops).length ≤ H →
      ((posterior (prior (shortParameter H)) ops c hc) depthThree).toReal < 1/1000) := by
  refine ⟨(lambda_bounds H).1,fun _ => rfl,?_⟩
  intro ops c hc hH
  rw [posterior_real]
  let w := readLetters ops
  let t : ℝ := (shortParameter H).value
  have ht0 : 0 < t := by dsimp [t,shortParameter]; exact_mod_cast (lambda_bounds H).1
  have ht1 : t ≤ ((1/2 : ℚ) : ℝ) := by dsimp [t,shortParameter]; exact_mod_cast (lambda_bounds H).2
  norm_num at ht1
  have h1 := mass_pos depthOne w
  have h2 := mass_pos depthTwo w
  have h3 := mass_nonneg depthThree w
  have hr := rare_ratio w
  have hpow : (9/8 : ℝ)^w.length ≤ (9/8 : ℝ)^H :=
    pow_le_pow_right₀ (by norm_num) hH
  have hb : 0 < (1-t)/2 := by linarith
  have hden : 0 < ((1-t)/2)*realMass depthOne w+
      ((1-t)/2)*realMass depthTwo w+t*realMass depthThree w := by positivity
  have hformula : t*(2000*(9/8 : ℝ)^H+1) = 1 := by
    dsimp [t,shortParameter,lambdaQ]
    push_cast
    field_simp
  have hratio : realMass depthThree w ≤ (9/8 : ℝ)^H*realMass depthOne w :=
    hr.trans (mul_le_mul_of_nonneg_right hpow h1.le)
  change t*realMass depthThree w / _ < 1/1000
  apply (div_lt_iff₀ hden).mpr
  have hmul := mul_le_mul_of_nonneg_left hratio ht0.le
  have hid : t*(9/8 : ℝ)^H = (1-t)/2000 := by nlinarith only [hformula]
  rw [← mul_assoc,hid] at hmul
  nlinarith only [hmul,mul_pos ht0 h1,mul_pos hb h2,mul_nonneg ht0.le h3]

private theorem endpoint_identity (a b d t : ℝ)
    (hd : ((1-t)/2)*a+((1-t)/2)*b+t*d ≠ 0) (hab : a+b ≠ 0) :
    ((1-t)/2)*a/(((1-t)/2)*a+((1-t)/2)*b+t*d) =
      (1-t*d/(((1-t)/2)*a+((1-t)/2)*b+t*d))*((1/2)*a/((1/2)*a+(1/2)*b)) := by
  have hhalf : (1/2)*a+(1/2)*b ≠ 0 := by
    intro he
    apply hab
    linarith
  have hscaled : -(t*a)-t*b+t*d*2+a+b ≠ 0 := by
    intro he
    apply hd
    linarith
  field_simp [hd,hhalf,hab,hscaled]
  linear_combination a * (mul_inv_cancel₀ hscaled)

private theorem posterior_mix_real (t : Parameter) (ops : List Operation)
    (c : AcquiredNativeState) (hc : run ops = some c) (k : Depth) :
    ((posterior (prior t) ops c hc) k).toReal =
      (1-((posterior (prior t) ops c hc) depthThree).toReal)*
        ((posterior muZero ops c hc) k).toReal+
      ((posterior (prior t) ops c hc) depthThree).toReal*
        (if k = depthThree then 1 else 0) := by
  have ht0 : 0 ≤ (t.value : ℝ) := by exact_mod_cast t.nonneg
  have ht1 : (t.value : ℝ) ≤ ((1/2 : ℚ) : ℝ) := by exact_mod_cast t.small
  norm_num at ht1
  have hb : 0 < (1-(t.value : ℝ))/2 := by linarith
  have h1 := mass_pos depthOne (readLetters ops)
  have h2 := mass_pos depthTwo (readLetters ops)
  have h3 := mass_pos depthThree (readLetters ops)
  have hd : 0 < ((1-(t.value : ℝ))/2)*realMass depthOne (readLetters ops)+
      ((1-(t.value : ℝ))/2)*realMass depthTwo (readLetters ops)+
      (t.value : ℝ)*realMass depthThree (readLetters ops) := by positivity
  have hd0 : 0 < realMass depthOne (readLetters ops)/2+
      realMass depthTwo (readLetters ops)/2 := by positivity
  have h12 : 0 < realMass depthOne (readLetters ops)+realMass depthTwo (readLetters ops) :=
    add_pos h1 h2
  have hDD : 0 < (1-(t.value : ℝ))*(realMass depthOne (readLetters ops)+
      realMass depthTwo (readLetters ops))+2*(t.value : ℝ)*realMass depthThree (readLetters ops) := by
    nlinarith only [hd]
  norm_num only [depthOne,depthTwo,depthThree] at h12 hDD
  rw [posterior_at,posterior_real]
  change _ = (1-_)*((posterior (prior zeroParameter) ops c hc) k).toReal+_
  rw [posterior_at]
  by_cases hk1 : k = depthOne
  · subst k
    simp only [weight,if_pos rfl,zeroParameter,Rat.cast_zero,sub_zero,zero_mul,
      add_zero,ENNReal.toReal_ofReal hb.le,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ (1-0)/2),
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1/2),
      show depthOne ≠ depthThree from by decide,if_neg,one_div,ite_true,ite_false]
    simp only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2⁻¹),mul_zero,add_zero]
    simpa only [one_div] using endpoint_identity _ _ _ _ (ne_of_gt hd) (by
      have h := add_pos h1 h2
      exact ne_of_gt h)
  · by_cases hk2 : k = depthTwo
    · subst k
      simp only [weight,show depthTwo ≠ depthOne from by decide,if_neg,if_pos rfl,
        zeroParameter,Rat.cast_zero,sub_zero,zero_mul,add_zero,
        ENNReal.toReal_ofReal hb.le,
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ (1-0)/2),
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1/2),
        show depthTwo ≠ depthThree from by decide,one_div,ite_true,ite_false]
      simp only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2⁻¹),mul_zero,add_zero]
      convert endpoint_identity (realMass depthTwo (readLetters ops))
        (realMass depthOne (readLetters ops)) (realMass depthThree (readLetters ops))
        (t.value : ℝ) (by nlinarith only [hd]) (by positivity) using 1 <;> ring
    · by_cases hk3 : k = depthThree
      · subst k
        norm_num [weight,zeroParameter,depthOne,depthTwo,depthThree,ENNReal.toReal_ofReal ht0]
      · simp [weight,hk1,hk2,hk3,zeroParameter]

private theorem posterior_mix (t : Parameter) (ops : List Operation)
    (c : AcquiredNativeState) (hc : run ops = some c) (k : Depth) :
    (posterior (prior t) ops c hc) k =
      ENNReal.ofReal (1-((posterior (prior t) ops c hc) depthThree).toReal)*
        (posterior muZero ops c hc) k+
      ENNReal.ofReal ((posterior (prior t) ops c hc) depthThree).toReal*
        (PMF.pure depthThree) k := by
  have hpos := ENNReal.toReal_nonneg (a := (posterior (prior t) ops c hc) depthThree)
  have hle : ((posterior (prior t) ops c hc) depthThree).toReal ≤ 1 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top
      ((posterior (prior t) ops c hc).coe_le_one depthThree)
    simpa using h
  rw [← ENNReal.ofReal_toReal ((posterior (prior t) ops c hc).apply_ne_top k),
    posterior_mix_real t ops c hc k,
    ENNReal.ofReal_add (mul_nonneg (sub_nonneg.mpr hle) ENNReal.toReal_nonneg)
      (mul_nonneg hpos (by split_ifs <;> norm_num)),
    ENNReal.ofReal_mul (sub_nonneg.mpr hle),ENNReal.ofReal_mul hpos,
    ENNReal.ofReal_toReal ((posterior muZero ops c hc).apply_ne_top k)]
  congr 2
  by_cases hk : k = depthThree <;> simp [hk,eq_comm]

/-- Complete source records, including every infinite seed path. -/
def completeSourceLaw (ν : PMF Depth) (f : FiniteFields) :
    Measure NativeFullResidual.FullTranscript :=
  (jointLaw ν).map (fun t => RarePriorFullFields.fieldsTranscript f t.2)

instance (ν : PMF Depth) (f : FiniteFields) : IsProbabilityMeasure (completeSourceLaw ν f) :=
  Measure.isProbabilityMeasure_map
    ((RarePriorGeneratedLaw.fields_measurable f).comp measurable_snd).aemeasurable

private theorem complete_mix (t : Parameter) (ops : List Operation)
    (c : AcquiredNativeState) (hc : run ops = some c) (f : FiniteFields) :
    completeSourceLaw (posterior (prior t) ops c hc) f =
      ENNReal.ofReal (1-((posterior (prior t) ops c hc) depthThree).toReal) •
        completeSourceLaw (posterior muZero ops c hc) f+
      ENNReal.ofReal ((posterior (prior t) ops c hc) depthThree).toReal •
        completeSourceLaw (PMF.pure depthThree) f := by
  apply Measure.ext
  intro E hE
  have hm : Measurable (fun t : Depth × Stream => RarePriorFullFields.fieldsTranscript f t.2) :=
    (RarePriorGeneratedLaw.fields_measurable f).comp measurable_snd
  simp only [completeSourceLaw,Measure.map_apply hm hE,jointLaw,
    Measure.sum_apply _ (hE.preimage hm),Measure.smul_apply,Measure.add_apply,smul_eq_mul]
  conv_lhs =>
    arg 1
    ext k
    rw [posterior_mix t ops c hc k]
  simp only [add_mul]
  simp only [mul_assoc]
  rw [ENNReal.tsum_add,ENNReal.tsum_mul_left,ENNReal.tsum_mul_left]

private theorem mixture_tv {X : Type*} [MeasurableSpace X]
    (Q R : Measure X) [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    measurableTotalVariation
      (ENNReal.ofReal (1-s) • Q+ENNReal.ofReal s • R) Q ≤ ENNReal.ofReal s := by
  have ha : ENNReal.ofReal (1-s) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hab : ENNReal.ofReal (1-s)+ENNReal.ofReal s = 1 := by
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hs1) hs]
    norm_num
  apply iSup_le
  intro E
  have hq : Q E.val ≤ 1 := (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  have hr : R E.val ≤ 1 := (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul]
  apply max_le
  · apply tsub_le_iff_right.mpr
    calc
      ENNReal.ofReal (1-s)*Q E.val+ENNReal.ofReal s*R E.val ≤
          Q E.val+ENNReal.ofReal s :=
        add_le_add (by simpa [mul_comm] using mul_le_mul_right ha (Q E.val))
          (by simpa [mul_comm] using mul_le_mul_left hr (ENNReal.ofReal s))
      _ = _ := add_comm _ _
  · apply tsub_le_iff_right.mpr
    calc
      Q E.val = (ENNReal.ofReal (1-s)+ENNReal.ofReal s)*Q E.val := by rw [hab,one_mul]
      _ = ENNReal.ofReal (1-s)*Q E.val+ENNReal.ofReal s*Q E.val := add_mul _ _ _
      _ ≤ ENNReal.ofReal (1-s)*Q E.val+ENNReal.ofReal s := by
        gcongr
        simpa [mul_comm] using mul_le_mul_left hq (ENNReal.ofReal s)
      _ ≤ ENNReal.ofReal s+(ENNReal.ofReal (1-s)*Q E.val+ENNReal.ofReal s*R E.val) := by
        rw [← add_assoc,add_comm (ENNReal.ofReal s)]
        exact le_add_right le_rfl

private theorem actual_complete_target (μ : PMF Depth) (ops : List Operation)
    (c : AcquiredNativeState) (hc : run ops = some c) :
    NativeObserverJointLaw.fullTarget RarePriorFullFields.actualObserver μ ops c =
      completeSourceLaw (posterior μ ops c hc) c.source.finiteFields := by
  let shift : Depth × Stream → Depth × Stream :=
    fun t => (t.1,rawTail t.2 (readLetters ops).length)
  let render : (Depth × Stream) × Runtime → NativeFullResidual.FullTranscript :=
    fun t => RarePriorFullFields.fieldsTranscript c.source.finiteFields t.1.2
  have ht : Measurable shift := by dsimp [shift]; unfold rawTail; fun_prop
  have hr : Measurable render :=
    (RarePriorGeneratedLaw.fields_measurable _).comp (measurable_snd.comp measurable_fst)
  have hf : NativeFullResidual.fullTranscript c =
      RarePriorFullFields.fieldsTranscript c.source.finiteFields := by
    funext ω
    exact (RarePriorFullFields.full_fields_factorization c ω).1
  unfold NativeObserverJointLaw.fullTarget
  rw [hf]
  change ((ProbabilityTheory.cond
    (NativeObserverJointLaw.actualLaw RarePriorFullFields.actualObserver μ ops.length)
    (nativeEvent ops c ×ˢ Set.univ)).map (render ∘ Prod.map shift id)) = _
  rw [← Measure.map_map hr (ht.prodMap measurable_id),
    (RarePriorGeneratedLaw.history_marginal_compatibility μ ops c hc).1]
  change (((jointLaw (posterior μ ops c hc)).prod
    (NativeObserverJointLaw.row RarePriorFullFields.actualObserver ops).toMeasure).map
    ((fun t : Depth × Stream => RarePriorFullFields.fieldsTranscript c.source.finiteFields t.2)
      ∘ Prod.fst)) = _
  have hm : Measurable (fun t : Depth × Stream =>
      RarePriorFullFields.fieldsTranscript c.source.finiteFields t.2) :=
    (RarePriorGeneratedLaw.fields_measurable _).comp measurable_snd
  rw [← Measure.map_map hm
    measurable_fst,Measure.map_fst_prod,measure_univ,one_smul]
  rfl

/-- The same-history endpoint posterior is exactly the zero-rare prior posterior.
    Its complement is the only perturbation of the entire unbounded record law. -/
theorem every_short_complete_target (H : ℕ) (ops : List Operation)
    (c : AcquiredNativeState) (hc : run ops = some c)
    (hH : (readLetters ops).length ≤ H) :
    (∀ k : Depth, (posterior (prior (shortParameter H)) ops c hc) k =
      ENNReal.ofReal (1-((posterior (prior (shortParameter H)) ops c hc) depthThree).toReal)*
        (posterior muZero ops c hc) k+
      ENNReal.ofReal ((posterior (prior (shortParameter H)) ops c hc) depthThree).toReal*
        (PMF.pure depthThree) k) ∧
    measurableTotalVariation
      (NativeObserverJointLaw.fullTarget RarePriorFullFields.actualObserver
        (prior (shortParameter H)) ops c)
      (NativeObserverJointLaw.fullTarget RarePriorFullFields.actualObserver muZero ops c) <
        ENNReal.ofReal (1/1000) ∧
    ∃ z : Runtime, runtimeRun ops = some z ∧ z.fields = c.source.finiteFields ∧
      NativeObserverJointLaw.row RarePriorFullFields.actualObserver ops = PMF.pure z ∧
      RarePriorGeneratedLaw.historyGenerated ops = RarePriorGeneratedLaw.decoder z ∧
      ∀ (op : Operation) (d : AcquiredNativeState), nativeStep c op = some d →
        NativeObserverJointLaw.row RarePriorFullFields.actualObserver (ops ++ [op]) =
          RarePriorFullFields.actualUpdate op z ∧
        (ProbabilityTheory.cond (RarePriorGeneratedLaw.historyGenerated ops)
          {t | RarePriorGeneratedLaw.firstOperation t = some op}).map
          NativeFullResidual.deleteBlock = RarePriorGeneratedLaw.historyGenerated (ops ++ [op]) := by
  refine ⟨posterior_mix _ ops c hc,?_,?_⟩
  ·
    rw [actual_complete_target _ ops c hc,actual_complete_target _ ops c hc,complete_mix]
    have hs : ((posterior (prior (shortParameter H)) ops c hc) depthThree).toReal < 1/1000 :=
      (every_short_history H).2.2 ops c hc hH
    have hle := mixture_tv
      (completeSourceLaw (posterior muZero ops c hc) c.source.finiteFields)
      (completeSourceLaw (PMF.pure depthThree) c.source.finiteFields)
      ((posterior (prior (shortParameter H)) ops c hc) depthThree).toReal
      ENNReal.toReal_nonneg (by linarith)
    exact hle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hs)
  · exact (RarePriorGeneratedLaw.history_marginal_compatibility
      (prior (shortParameter H)) ops c hc).2

def retryList : ℕ → List Letter
  | 0 => []
  | n+1 => retryList n ++ [0,0,0,1,1,1,1,1]

def longForm (n : ℕ) : PrefixForm :=
  ⟨retryList n,.acquired 1 (.segment 0 1 (.segment 0 0 (.segment 0 0 (.active 0 .p))))⟩
def longHistory (n : ℕ) : List Operation := reads (blocks n ++ latchWord)
def longState (n : ℕ) : AcquiredNativeState := reconstruct (longForm n)

private theorem long_render (n : ℕ) : render (longForm n) = longHistory n := by
  have hr : retryWord (retryList n) = blocks n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simpa [retryList,retryWord,List.map_append,List.flatten_append,blocks,blockWord]
        using congrArg (fun w => w ++ blockWord) ih
  simp [longForm,longHistory,render,hr,seedWord,renderPayload,phaseWord,
    pWord,loopWord,latchWord,reads,List.map_append,List.append_assoc]

private theorem long_run (n : ℕ) : run (longHistory n) = some (longState n) :=
  (native_acquired_prefix_reconstruction (longHistory n)).2 (longForm n) (long_render n) |>.1

private theorem mass_append (k : Depth) (u v : List Letter) :
    realMass k (u ++ v) = realMass k u*realMass k v := by
  induction u with
  | nil => simp [realMass]
  | cons x u ih => simp [realMass,ih,mul_assoc]

private theorem long_mass (k : Depth) (n : ℕ) :
    realMass k (blocks n ++ latchWord) =
      realMass k blockWord^n*realMass k latchWord := by
  rw [mass_append]
  congr 1
  induction n with
  | zero => rfl
  | succ n ih => simp [blocks,mass_append,ih,pow_succ]

private theorem likelihood_separation :
    realMass depthOne blockWord < realMass depthThree blockWord ∧
    realMass depthTwo blockWord < realMass depthThree blockWord := by
  norm_num [realMass,atom_real,blockWord,depthOne,depthTwo,depthThree,rate,Nat.fib_add_two]

private theorem long_posterior_formula (t : Parameter) (n : ℕ)
    (ht : 0 < t.value) :
    ((posterior (prior t) (longHistory n) (longState n) (long_run n)) depthThree).toReal =
      (t.value : ℝ)/
        (((1-(t.value : ℝ))/2)*
          ((realMass depthOne blockWord/realMass depthThree blockWord)^n*
            (realMass depthOne latchWord/realMass depthThree latchWord))+
         ((1-(t.value : ℝ))/2)*
          ((realMass depthTwo blockWord/realMass depthThree blockWord)^n*
            (realMass depthTwo latchWord/realMass depthThree latchWord))+(t.value : ℝ)) := by
  rw [posterior_real]
  have he : readLetters (longHistory n) = blocks n ++ latchWord := by
    simpa only [longHistory,List.append_nil,readLetters] using
      NativeConditionalControl.Prefix.erase_reads (blocks n ++ latchWord) []
  rw [he,long_mass,long_mass,long_mass]
  have hblock := mass_pos depthThree blockWord
  have hsuffix := mass_pos depthThree latchWord
  have hp : realMass depthThree blockWord^n*realMass depthThree latchWord ≠ 0 :=
    ne_of_gt (mul_pos (pow_pos hblock _) hsuffix)
  have h1pos := mass_pos depthOne (blocks n ++ latchWord)
  have h2pos := mass_pos depthTwo (blocks n ++ latchWord)
  rw [long_mass] at h1pos h2pos
  have ht0 : 0 < (t.value : ℝ) := by exact_mod_cast ht
  have ht1 : (t.value : ℝ) ≤ ((1/2 : ℚ) : ℝ) := by exact_mod_cast t.small
  norm_num at ht1
  have hb : 0 < (1-(t.value : ℝ))/2 := by linarith
  have he1 : (realMass depthOne blockWord/realMass depthThree blockWord)^n*
      (realMass depthOne latchWord/realMass depthThree latchWord) =
        (realMass depthOne blockWord^n*realMass depthOne latchWord)/
          (realMass depthThree blockWord^n*realMass depthThree latchWord) := by
    rw [div_pow,div_mul_div_comm]
  have he2 : (realMass depthTwo blockWord/realMass depthThree blockWord)^n*
      (realMass depthTwo latchWord/realMass depthThree latchWord) =
        (realMass depthTwo blockWord^n*realMass depthTwo latchWord)/
          (realMass depthThree blockWord^n*realMass depthThree latchWord) := by
    rw [div_pow,div_mul_div_comm]
  rw [he1,he2]
  simp only [← mul_assoc]
  have hden1 : 0 < ((1-(t.value : ℝ))/2)*realMass depthOne blockWord^n*realMass depthOne latchWord+
      ((1-(t.value : ℝ))/2)*realMass depthTwo blockWord^n*realMass depthTwo latchWord+
      (t.value : ℝ)*realMass depthThree blockWord^n*realMass depthThree latchWord := by
    simpa only [mul_assoc] using add_pos (add_pos (mul_pos hb h1pos) (mul_pos hb h2pos))
      (mul_pos ht0 (mul_pos (pow_pos hblock n) hsuffix))
  have hden2 : 0 < ((1-(t.value : ℝ))/2)*
      ((realMass depthOne blockWord^n*realMass depthOne latchWord)/
        (realMass depthThree blockWord^n*realMass depthThree latchWord))+
      ((1-(t.value : ℝ))/2)*
      ((realMass depthTwo blockWord^n*realMass depthTwo latchWord)/
        (realMass depthThree blockWord^n*realMass depthThree latchWord))+(t.value : ℝ) :=
    add_pos (add_pos
      (mul_pos hb (div_pos h1pos (mul_pos (pow_pos hblock n) hsuffix)))
      (mul_pos hb (div_pos h2pos (mul_pos (pow_pos hblock n) hsuffix)))) ht0
  apply (div_eq_div_iff (ne_of_gt hden1) (ne_of_gt hden2)).mpr
  field_simp [ne_of_gt hblock,ne_of_gt hsuffix,pow_ne_zero n (ne_of_gt hblock)]
  <;> ring


private theorem endpoint_odds (n : ℕ) :
    realMass depthTwo (blocks n ++ latchWord)/realMass depthOne (blocks n ++ latchWord) =
      (27/25 : ℝ)^3*(1594323/1562500 : ℝ)^(2*n) := by
  rw [long_mass,long_mass,mul_div_mul_comm,← div_pow]
  have hb : realMass depthTwo blockWord/realMass depthOne blockWord =
      (1594323/1562500 : ℝ)^2 := by
    norm_num [realMass,atom_real,blockWord,depthOne,depthTwo,rate,Nat.fib_add_two]
  have hl : realMass depthTwo latchWord/realMass depthOne latchWord = (27/25 : ℝ)^3 := by
    norm_num [realMass,atom_real,latchWord,depthOne,depthTwo,rate,Nat.fib_add_two]
  rw [hb,hl,← pow_mul,mul_comm]

/-- The recognized histories are native positive histories. Their same-source
    posterior concentrates at depth three for every fixed positive rare weight. -/
theorem long_history_concentration (t : Parameter) (ht : 0 < t.value) :
    (∀ n : ℕ, run (longHistory n) = some (longState n) ∧
      0 < normalizer (prior t) (longHistory n)) ∧
    (∀ n : ℕ, 375 ≤ n → runtimeRun (longHistory n) =
      some ⟨latchedFields,.accepted,.g⟩) ∧
    realMass depthOne blockWord < realMass depthThree blockWord ∧
    realMass depthTwo blockWord < realMass depthThree blockWord ∧
    Tendsto (fun n =>
      ((posterior (prior t) (longHistory n) (longState n) (long_run n)) depthThree).toReal)
      atTop (𝓝 1) := by
  refine ⟨fun n => ⟨long_run n,(normalizer_bounds (prior t) _ _ (long_run n)).1⟩,
    fun n hn => (original_latch_activation n hn).1,
    likelihood_separation.1,likelihood_separation.2,?_⟩
  have h31 := mass_pos depthThree blockWord
  have h1 : realMass depthOne blockWord/realMass depthThree blockWord < 1 :=
    (div_lt_one h31).mpr likelihood_separation.1
  have h2 : realMass depthTwo blockWord/realMass depthThree blockWord < 1 :=
    (div_lt_one h31).mpr likelihood_separation.2
  have h1lim := tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg (mass_nonneg depthOne _) h31.le) h1
  have h2lim := tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg (mass_nonneg depthTwo _) h31.le) h2
  have hden : Tendsto (fun n =>
      ((1-(t.value : ℝ))/2)*
        ((realMass depthOne blockWord/realMass depthThree blockWord)^n*
          (realMass depthOne latchWord/realMass depthThree latchWord))+
      ((1-(t.value : ℝ))/2)*
        ((realMass depthTwo blockWord/realMass depthThree blockWord)^n*
          (realMass depthTwo latchWord/realMass depthThree latchWord))+(t.value : ℝ))
      atTop (𝓝 (t.value : ℝ)) := by
    convert ((h1lim.mul_const _).const_mul _).add
      ((h2lim.mul_const _).const_mul _) |>.add_const (t.value : ℝ) using 1 <;> simp
  have ht0 : (t.value : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  have hlim :=
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (t.value : ℝ)) atTop
      (𝓝 (t.value : ℝ))).div hden ht0)
  rw [div_self ht0] at hlim
  exact hlim.congr (fun n => (long_posterior_formula t n ht).symm)

/-- The original endpoint posterior on every selected long history exceeds the
    required mean threshold, with the exact native likelihood odds. -/
theorem long_endpoint_calibration (n : ℕ) (hn : 375 ≤ n) :
    realMass depthTwo (blocks n ++ latchWord)/realMass depthOne (blocks n ++ latchWord) =
      (27/25 : ℝ)^3*(1594323/1562500 : ℝ)^(2*n) ∧
    16 < realMass depthTwo (blocks n ++ latchWord)/realMass depthOne (blocks n ++ latchWord) ∧
    79/200 < ((posterior muZero (longHistory n) (longState n) (long_run n)) depthOne).toReal/3+
      ((posterior muZero (longHistory n) (longState n) (long_run n)) depthTwo).toReal*(2/5) ∧
    RarePriorReferenceScalar.tStar+47/100 < 21/40-(1116529/22781250 : ℝ) ∧
    (∀ (t : Parameter), 0 < t.value →
      Tendsto (fun m => ((posterior (prior t) (longHistory m) (longState m)
        (long_run m)) depthThree).toReal) atTop (𝓝 1)) := by
  have hnum : (26/25 : ℝ) < (1594323/1562500 : ℝ)^2 := by norm_num
  have hBern := one_add_mul_sub_le_pow
    (by norm_num : (-1 : ℝ) ≤ (1594323/1562500 : ℝ)^2) n
  have hnr : (375 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (16 : ℝ) < ((1594323/1562500 : ℝ)^2)^n := by
    have hnpos : (0 : ℝ) < n := by linarith
    have hm := mul_lt_mul_of_pos_left hnum hnpos
    nlinarith only [hBern,hm,hnr]
  have hO : (16 : ℝ) < (27/25 : ℝ)^3*(1594323/1562500 : ℝ)^(2*n) := by
    rw [pow_mul]
    nlinarith only [hpow]
  have ho : (16 : ℝ) < realMass depthTwo (blocks n ++ latchWord)/
      realMass depthOne (blocks n ++ latchWord) := by rw [endpoint_odds]; exact hO
  refine ⟨endpoint_odds n,ho,?_,?_,?_⟩
  ·
    have h1 := mass_pos depthOne (blocks n ++ latchWord)
    have h2 := mass_pos depthTwo (blocks n ++ latchWord)
    have hratio : 16*realMass depthOne (blocks n ++ latchWord) <
        realMass depthTwo (blocks n ++ latchWord) := (lt_div_iff₀ h1).mp ho
    change _ < ((posterior (prior zeroParameter) (longHistory n) (longState n) (long_run n)) depthOne).toReal/3+_
    simp only [muZero]
    rw [posterior_at,posterior_at]
    have her : readLetters (reads (blocks n ++ latchWord)) = blocks n ++ latchWord := by
      simpa only [List.append_nil,readLetters] using
        NativeConditionalControl.Prefix.erase_reads (blocks n ++ latchWord) []
    simp only [zeroParameter,weight,show depthTwo ≠ depthOne from by decide,if_neg,
      if_pos rfl,ite_true,Rat.cast_zero,sub_zero,zero_mul,add_zero,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ (1-0)/2),longHistory,
      her]
    simp only [ite_false,ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1/2)]
    have hd : 0 < (1/2 : ℝ)*realMass depthOne (blocks n ++ latchWord)+
        (1/2 : ℝ)*realMass depthTwo (blocks n ++ latchWord) := by positivity
    have he : (1/2 : ℝ)*realMass depthOne (blocks n ++ latchWord)/
          ((1/2)*realMass depthOne (blocks n ++ latchWord)+(1/2)*realMass depthTwo (blocks n ++ latchWord))/3+
        (1/2)*realMass depthTwo (blocks n ++ latchWord)/
          ((1/2)*realMass depthOne (blocks n ++ latchWord)+(1/2)*realMass depthTwo (blocks n ++ latchWord))*(2/5) =
        ((1/6)*realMass depthOne (blocks n ++ latchWord)+(1/5)*realMass depthTwo (blocks n ++ latchWord))/
          ((1/2)*realMass depthOne (blocks n ++ latchWord)+(1/2)*realMass depthTwo (blocks n ++ latchWord)) := by ring
    rw [he]
    apply (lt_div_iff₀ hd).mpr
    nlinarith only [hratio,h1]
  · have ht := RarePriorReferenceScalar.exact_reference_scalar.2.2.2.2.2.2
    norm_num at ⊢
    linarith
  · intro t ht
    exact (long_history_concentration t ht).2.2.2.2

set_option maxRecDepth 2048

/-- Full-record risks use the original phase-history domains and actual acquired rows. -/
def lawError (μ : PMF Depth) (h : List Operation) (c : AcquiredNativeState) : ℝ≥0∞ :=
  measurableTotalVariation (RarePriorGeneratedLaw.historyGenerated h)
    (NativeObserverJointLaw.fullTarget RarePriorFullFields.actualObserver μ h c)

def confError (μ : PMF Depth) (h : List Operation) (c : AcquiredNativeState) : ℝ≥0∞ :=
  ∑ z : Runtime, NativeObserverJointLaw.row RarePriorFullFields.actualObserver h z *
    measurableTotalVariation (RarePriorGeneratedLaw.decoder z)
      (NativeObserverJointLaw.fullTarget RarePriorFullFields.actualObserver μ h c)

def phaseLawRisk (μ : PMF Depth) (s : ActivePhase) : ℝ≥0∞ :=
  ⨆ p : NativeObserverJointLaw.PhaseHistory s, lawError μ p.val.1 p.val.2

def phaseConfRisk (μ : PMF Depth) (s : ActivePhase) : ℝ≥0∞ :=
  ⨆ p : NativeObserverJointLaw.PhaseHistory s, confError μ p.val.1 p.val.2

def shortLawRisk (μ : PMF Depth) (s : ActivePhase) (H : ℕ) : ℝ≥0∞ :=
  ⨆ p : {p : NativeObserverJointLaw.PhaseHistory s //
    (readLetters p.val.1).length ≤ H}, lawError μ p.val.val.1 p.val.val.2

def shortConfRisk (μ : PMF Depth) (s : ActivePhase) (H : ℕ) : ℝ≥0∞ :=
  ⨆ p : {p : NativeObserverJointLaw.PhaseHistory s //
    (readLetters p.val.1).length ≤ H}, confError μ p.val.val.1 p.val.val.2

private theorem tv_probability_bound {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    measurableTotalVariation P Q ≤ 1 := by
  apply iSup_le
  intro E
  exact max_le ((tsub_le_self).trans (prob_le_one))
    ((tsub_le_self).trans (prob_le_one))

private theorem error_pure (μ : PMF Depth) (h : List Operation)
    (c : AcquiredNativeState) (hc : run h = some c) :
    confError μ h c = lawError μ h c ∧ lawError μ h c ≤ 1 := by
  classical
  obtain ⟨z,_,_,hz,hgen,_⟩ :=
    (RarePriorGeneratedLaw.history_marginal_compatibility μ h c hc).2
  constructor
  · simp [confError,lawError,hz,hgen,PMF.pure_apply,ite_mul]
  · rw [lawError,hgen,actual_complete_target μ h c hc]
    haveI := (RarePriorGeneratedLaw.generated_full_law z).1
    exact tv_probability_bound _ _

private theorem phase_bounds (μ : PMF Depth) (s : ActivePhase) :
    phaseConfRisk μ s = phaseLawRisk μ s ∧ phaseLawRisk μ s ≤ 1 := by
  unfold phaseConfRisk phaseLawRisk
  constructor
  · apply iSup_congr
    intro p
    exact (error_pure μ _ _ p.property.1).1
  · apply iSup_le
    intro p
    exact (error_pure μ _ _ p.property.1).2

private theorem short_bounds (μ : PMF Depth) (s : ActivePhase) (H : ℕ) :
    shortConfRisk μ s H = shortLawRisk μ s H ∧ shortLawRisk μ s H ≤ 1 := by
  unfold shortConfRisk shortLawRisk
  constructor
  · apply iSup_congr
    intro p
    exact (error_pure μ _ _ p.val.property.1).1
  · apply iSup_le
    intro p
    exact (error_pure μ _ _ p.val.property.1).2

private theorem short_risk_perturbation (s : ActivePhase) (H : ℕ) :
    (shortLawRisk (prior (shortParameter H)) s H).toReal ≤
      (shortLawRisk muZero s H).toReal+1/1000 := by
  have hp := (short_bounds (prior (shortParameter H)) s H).2
  have hq := (short_bounds muZero s H).2
  have hfinite := ne_top_of_le_ne_top ENNReal.one_ne_top hq
  have he : shortLawRisk (prior (shortParameter H)) s H ≤
      shortLawRisk muZero s H+ENNReal.ofReal (1/1000) := by
    apply iSup_le
    intro p
    have hb := (every_short_complete_target H p.val.val.1 p.val.val.2
      p.val.property.1 p.property).2.1.le
    rw [D5.S3.Estimation.DataProcessing.MeasurableTotalVariationTriangle.measurable_total_variation_comm] at hb
    have ht := D5.S3.Estimation.DataProcessing.MeasurableTotalVariationTriangle.measurable_total_variation_triangle
      (RarePriorGeneratedLaw.historyGenerated p.val.val.1)
      (NativeObserverJointLaw.fullTarget RarePriorFullFields.actualObserver muZero p.val.val.1 p.val.val.2)
      (NativeObserverJointLaw.fullTarget RarePriorFullFields.actualObserver
        (prior (shortParameter H)) p.val.val.1 p.val.val.2)
    have hi : lawError muZero p.val.val.1 p.val.val.2 ≤ shortLawRisk muZero s H :=
      le_iSup (fun p : {p : NativeObserverJointLaw.PhaseHistory s //
        (readLetters p.val.1).length ≤ H} => lawError muZero p.val.val.1 p.val.val.2) p
    exact ht.trans (add_le_add hi hb)
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨hfinite,ENNReal.ofReal_ne_top⟩) he
  rw [ENNReal.toReal_add hfinite ENNReal.ofReal_ne_top] at h
  norm_num at h ⊢
  exact h

def firstAlpha : Set NativeFullResidual.FullTranscript :=
  {t | RarePriorGeneratedLaw.firstOperation t = some (.read 0)}

private theorem firstAlpha_measurable : MeasurableSet firstAlpha :=
  (measurableSet_singleton _).preimage RarePriorGeneratedLaw.first_measurable

private theorem firstAlpha_source (ν : PMF Depth) :
    completeSourceLaw ν latchedFields firstAlpha =
      ∑' k : Depth, ν k * ENNReal.ofReal (rate k : ℝ) := by
  have hm : Measurable (fun t : Depth × Stream =>
      RarePriorFullFields.fieldsTranscript latchedFields t.2) :=
    (RarePriorGeneratedLaw.fields_measurable _).comp measurable_snd
  rw [completeSourceLaw,Measure.map_apply hm firstAlpha_measurable]
  have he : (fun t : Depth × Stream => RarePriorFullFields.fieldsTranscript latchedFields t.2) ⁻¹'
      firstAlpha = Prod.snd ⁻¹' prefixCylinder [0] := by
    ext t
    simp [firstAlpha,RarePriorGeneratedLaw.firstOperation,RarePriorFullFields.fieldsTranscript,
      RarePriorFullFields.finiteDrive,RarePriorFullFields.finiteNext,
      RarePriorFullFields.finiteOperation,latchedFields,finiteStep,finiteRead,
      prefixCylinder,Prefix,readPrefix,List.ofFn_succ]
  rw [he]
  simp only [jointLaw,Measure.sum_apply_of_countable,Measure.smul_apply,smul_eq_mul]
  apply tsum_congr
  intro k
  rw [Measure.map_apply (show Measurable (fun ω : Stream => (k,ω)) by fun_prop)
    ((measurable_cylinder [0]).preimage measurable_snd)]
  change ν k * rawReadLaw (rate k) (prefixCylinder [0]) = _
  rw [cylinder_mass]
  simp only [wordMass,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
    bernoulliMeasure_apply,Set.mem_singleton_iff,if_pos rfl,
    show (1 : Letter) ≠ 0 from by decide,if_false,add_zero]
  congr 1
  simp [bernoulliMeasure_apply (rate k) (measurableSet_singleton (0 : Letter)),
    ← ENNReal.ofReal_coe_nnreal,unitInterval.coe_toNNReal]

private theorem firstAlpha_three :
    completeSourceLaw (PMF.pure depthThree) latchedFields firstAlpha = ENNReal.ofReal (3/8) := by
  rw [firstAlpha_source]
  norm_num [PMF.pure_apply,depthThree,rate,Nat.fib_add_two]

private theorem long_fields (n : ℕ) (hn : 375 ≤ n) :
    (longState n).source.finiteFields = latchedFields := by
  have he := arbitrary_legal_projection (longHistory n) ⟨longState n,long_run n⟩
  have hz : runtimeRun (longHistory n) = some ⟨latchedFields,.accepted,.g⟩ :=
    (original_latch_activation n hn).1
  rw [hz,long_run n] at he
  exact (Option.some.inj he).symm

private theorem long_firstAlpha (n : ℕ) (hn : 375 ≤ n) :
    RarePriorGeneratedLaw.historyGenerated (longHistory n) firstAlpha = ENNReal.ofReal (9/10) := by
  obtain ⟨z,hz,_,_,hgen,_⟩ :=
    (RarePriorGeneratedLaw.history_marginal_compatibility muZero _ _ (long_run n)).2
  have hg : runtimeRun (longHistory n) = some ⟨latchedFields,.accepted,.g⟩ :=
    (original_latch_activation n hn).1
  rw [hg] at hz
  cases Option.some.inj hz
  rw [hgen]
  have he := (RarePriorGeneratedLaw.configuration_compatibility
    (⟨latchedFields,.accepted,.g⟩ : Runtime)).1
      (by simp [latchedFields]) (by simp [latchedFields]) 0 |>.1
  convert he using 1 <;> norm_num [firstAlpha,RarePriorGeneratedLaw.emissionParameter,
    RarePriorFairBitService.selectedThreshold,queryMode,latchedFields,
    RarePriorFairBitService.threshold,bernoulliMeasure_apply,
    ← ENNReal.ofReal_coe_nnreal,unitInterval.coe_toNNReal]

private theorem event_gap {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) (E : Set X) (hE : MeasurableSet E) :
    P E - Q E ≤ measurableTotalVariation P Q := by
  exact (le_max_left _ _).trans
    (le_iSup (fun A : {A : Set X // MeasurableSet A} =>
      max (P A.val-Q A.val) (Q A.val-P A.val)) ⟨E,hE⟩)

private theorem long_cylinder_lower (t : Parameter) (n : ℕ) (hn : 375 ≤ n) :
    -1/10+(5/8)*((posterior (prior t) (longHistory n) (longState n) (long_run n)) depthThree).toReal ≤
      (lawError (prior t) (longHistory n) (longState n)).toReal := by
  let s := ((posterior (prior t) (longHistory n) (longState n) (long_run n)) depthThree).toReal
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have hs1 : s ≤ 1 := by
    simpa [s] using ENNReal.toReal_mono ENNReal.one_ne_top
      ((posterior (prior t) (longHistory n) (longState n) (long_run n)).coe_le_one depthThree)
  have hQ : completeSourceLaw (posterior muZero (longHistory n) (longState n) (long_run n))
      latchedFields firstAlpha ≤ 1 := prob_le_one
  have hQT : completeSourceLaw (posterior muZero (longHistory n) (longState n) (long_run n))
      latchedFields firstAlpha ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hQ
  have htarget := actual_complete_target (prior t) (longHistory n) (longState n) (long_run n)
  rw [long_fields n hn,complete_mix] at htarget
  have hmass : (NativeObserverJointLaw.fullTarget RarePriorFullFields.actualObserver
      (prior t) (longHistory n) (longState n)) firstAlpha =
      ENNReal.ofReal (1-s)*
        completeSourceLaw (posterior muZero (longHistory n) (longState n) (long_run n))
          latchedFields firstAlpha+ENNReal.ofReal s*ENNReal.ofReal (3/8) := by
    rw [htarget,Measure.add_apply,Measure.smul_apply,Measure.smul_apply,firstAlpha_three]
    rfl
  have htarget1 : (NativeObserverJointLaw.fullTarget RarePriorFullFields.actualObserver
      (prior t) (longHistory n) (longState n)) firstAlpha ≤ 1 := by
    rw [actual_complete_target _ _ _ (long_run n)]
    exact prob_le_one
  have htargetT := ne_top_of_le_ne_top ENNReal.one_ne_top htarget1
  have htvT := ne_top_of_le_ne_top ENNReal.one_ne_top
    (error_pure (prior t) (longHistory n) (longState n) (long_run n)).2
  have hbound : ((NativeObserverJointLaw.fullTarget RarePriorFullFields.actualObserver
      (prior t) (longHistory n) (longState n)) firstAlpha).toReal ≤ 1-(5/8)*s := by
    rw [hmass,ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hQT)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sub_nonneg.mpr hs1),
      ENNReal.toReal_ofReal hs0,ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3/8)]
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hQ
    norm_num at h
    nlinarith only [h,mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr h)]
  have htv : RarePriorGeneratedLaw.historyGenerated (longHistory n) firstAlpha -
      (NativeObserverJointLaw.fullTarget RarePriorFullFields.actualObserver
        (prior t) (longHistory n) (longState n)) firstAlpha ≤
      lawError (prior t) (longHistory n) (longState n) :=
    event_gap _ _ firstAlpha firstAlpha_measurable
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨htvT,htargetT⟩)
    (tsub_le_iff_right.mp htv)
  rw [long_firstAlpha n hn,ENNReal.toReal_add htvT htargetT] at h
  norm_num at h
  change -1/10+(5/8)*s ≤ _
  linarith

/-- Deterministic actual rows identify law and configuration risks on the complete
    record domain. Normalization bounds precede every real conversion. The full
    first-alpha cylinder proves the long-history margin; short risks retain the
    exact rare-prior perturbation relative to the zero-rare same-history target. -/
theorem complete_record_risk_bridges (t : Parameter) (ht : 0 < t.value) :
    (∀ (μ : PMF Depth) (h : List Operation) (c : AcquiredNativeState), run h = some c →
      confError μ h c = lawError μ h c ∧ lawError μ h c ≤ 1) ∧
    (∀ (μ : PMF Depth) (s : ActivePhase),
      phaseConfRisk μ s = phaseLawRisk μ s ∧ phaseLawRisk μ s ≤ 1 ∧
      ∀ H : ℕ, shortConfRisk μ s H = shortLawRisk μ s H ∧ shortLawRisk μ s H ≤ 1) ∧
    (∀ (s : ActivePhase) (H : ℕ),
      (shortLawRisk (prior (shortParameter H)) s H).toReal ≤
        (shortLawRisk muZero s H).toReal+1/1000) ∧
    (∀ n : ℕ, 375 ≤ n →
      RarePriorGeneratedLaw.historyGenerated (longHistory n) firstAlpha = ENNReal.ofReal (9/10) ∧
      -1/10+(5/8)*((posterior (prior t) (longHistory n) (longState n) (long_run n)) depthThree).toReal ≤
        (lawError (prior t) (longHistory n) (longState n)).toReal) ∧
    21/40 ≤ (phaseLawRisk (prior t) .p).toReal ∧
    RarePriorReferenceScalar.tStar+47/100 <
      (phaseLawRisk (prior t) .p).toReal-(1116529/22781250 : ℝ) := by
  have hrT := ne_top_of_le_ne_top ENNReal.one_ne_top (phase_bounds (prior t) .p).2
  have hl : Tendsto (fun n => -1/10+(5/8)*
      ((posterior (prior t) (longHistory n) (longState n) (long_run n)) depthThree).toReal)
      atTop (𝓝 (21/40 : ℝ)) := by
    convert ((long_history_concentration t ht).2.2.2.2.const_mul (5/8)).const_add (-1/10) using 1
    norm_num
  have hb : (21/40 : ℝ) ≤ (phaseLawRisk (prior t) .p).toReal := by
    apply le_of_tendsto hl
    filter_upwards [eventually_ge_atTop 375] with n hn
    have hphase : (longState n).source.finiteFields.control = .fourth (.active .p) := by
      rw [long_fields n hn]
      rfl
    exact (long_cylinder_lower t n hn).trans (ENNReal.toReal_mono hrT
      (le_iSup (fun p : NativeObserverJointLaw.PhaseHistory .p =>
        lawError (prior t) p.val.1 p.val.2) ⟨(longHistory n,longState n),long_run n,hphase⟩))
  refine ⟨fun μ h c hc => error_pure μ h c hc,
    fun μ s => ⟨(phase_bounds μ s).1,(phase_bounds μ s).2,short_bounds μ s⟩,
    short_risk_perturbation,fun n hn => ⟨long_firstAlpha n hn,long_cylinder_lower t n hn⟩,hb,?_⟩
  have hm := (long_endpoint_calibration 375 (by omega)).2.2.2.1
  linarith

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorThreePoint
