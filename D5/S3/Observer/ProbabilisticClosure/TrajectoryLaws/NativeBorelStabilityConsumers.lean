/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStabilityConsumers
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStabilityConsumers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-supported-depth risk, unboxed zero-face boxes and necessary lower-tail repair bounds. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelNormalizedStability
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeBorelCommonFlow NativeBorelEndpointIdentification NativeFullResidual
open NativeConditionalControl.Tail FourthSegmentStoppedLaw
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open D5.S3.Estimation.DataProcessing.MeasurableTotalVariationTriangle
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open NativeBorelSignedAction NativeBorelNormalizedStability
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelStabilityConsumers
open NativeBorelTVTopology NativePaidHistoryCommonRowRisks
open NativeConditionalControl.DepthLaw
open scoped Topology

def targetLoss (s : ActivePhase) (r : unitInterval) (D : RegularDescriptor s) : ℝ :=
  (measurableTotalVariation (law D) (native s r : Measure (ValidTail s))).toReal

set_option maxHeartbeats 1200000 in
lemma bounded_target_loss (s : ActivePhase) (r : unitInterval) : Bounded (targetLoss s r) := by
  have hm : Measurable (fun P : ProbabilityMeasure (ValidTail s) =>
      (measurableTotalVariation (P : Measure (ValidTail s)) (native s r : Measure (ValidTail s))).toReal) := by
    letI := tvEMetric s
    letI : BorelSpace (ProbabilityMeasure (ValidTail s)) := ⟨(tv_borel_eq s).symm⟩
    change Measurable (fun P : ProbabilityMeasure (ValidTail s) => (edist P (native s r)).toReal)
    have hc : Continuous (fun P : ProbabilityMeasure (ValidTail s) => edist P (native s r)) :=
      continuous_id.edist continuous_const
    exact hc.measurable.ennreal_toReal
  refine ⟨hm.comp measurable_subtype_coe,1,by norm_num,?_⟩
  intro D
  unfold targetLoss
  rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono ENNReal.one_ne_top (probability_tv_le_one _ _)).trans_eq (by simp)

def radius : ActivePhase → ℝ
  | .p => 1116529/22781250
  | .beta => 239/6750

def supportedRisk (ν : (s : ActivePhase) → Measure (RegularDescriptor s))
    (μ : PMF Depth) : ℝ :=
  max (sSup ((fun k => ∫ D, targetLoss .p (rate k) D ∂ν .p) '' {k | μ k ≠ 0}) - radius .p)
      (sSup ((fun k => ∫ D, targetLoss .beta (rate k) D ∂ν .beta) '' {k | μ k ≠ 0}) - radius .beta)

def flowMargins (F : CommonFlow) : (s : ActivePhase) → Measure (RegularDescriptor s)
  | .p => F.nuP
  | .beta => F.nuB

lemma source_endpoint_rates : rate (1 : Depth) = lowerRate ∧ rate (2 : Depth) = upperRate := by
  constructor <;> apply Subtype.ext <;> norm_num [rate,lowerRate,upperRate,Nat.fib]

lemma target_integral_bounds (s : ActivePhase) (ν : Measure (RegularDescriptor s))
    [IsProbabilityMeasure ν] (r : unitInterval) :
    0 ≤ (∫ D, targetLoss s r D ∂ν) ∧ (∫ D, targetLoss s r D ∂ν) ≤ 1 := by
  constructor
  · exact integral_nonneg (fun _ => ENNReal.toReal_nonneg)
  · have hi := integral_mono ((bounded_target_loss s r).integrable ν)
      (integrable_const (1 : ℝ)) (fun D => by
        exact (ENNReal.toReal_mono ENNReal.one_ne_top (probability_tv_le_one _ _)).trans_eq (by simp))
    simpa using hi

lemma supported_term_le (ν : (s : ActivePhase) → Measure (RegularDescriptor s))
    (hν : ∀ s, IsProbabilityMeasure (ν s)) (μ : PMF Depth) (s : ActivePhase)
    (k : Depth) (hk : μ k ≠ 0) :
    (∫ D, targetLoss s (rate k) D ∂ν s) - radius s ≤ supportedRisk ν μ := by
  letI := hν s
  have hb : BddAbove ((fun k => ∫ D, targetLoss s (rate k) D ∂ν s) '' {k | μ k ≠ 0}) := by
    refine ⟨1,?_⟩
    rintro _ ⟨k,hk,rfl⟩
    exact (target_integral_bounds s (ν s) (rate k)).2
  have hk' : (∫ D, targetLoss s (rate k) D ∂ν s) ≤
      sSup ((fun k => ∫ D, targetLoss s (rate k) D ∂ν s) '' {k | μ k ≠ 0}) :=
    le_csSup hb ⟨k,hk,rfl⟩
  cases s
  · exact (sub_le_sub_right hk' _).trans (le_max_left _ _)
  · exact (sub_le_sub_right hk' _).trans (le_max_right _ _)

lemma supported_endpoint_le (ν : (s : ActivePhase) → Measure (RegularDescriptor s))
    (hν : ∀ s, IsProbabilityMeasure (ν s)) (μ : PMF Depth)
    (h1 : μ 1 ≠ 0) (h2 : μ 2 ≠ 0) (s : ActivePhase) (b : Bool) :
    (∫ D, fullLoss s b D ∂ν s) - radius s ≤ supportedRisk ν μ := by
  cases b
  · simpa [fullLoss,targetLoss,endpoint,source_endpoint_rates.1] using supported_term_le ν hν μ s 1 h1
  · simpa [fullLoss,targetLoss,endpoint,source_endpoint_rates.2] using supported_term_le ν hν μ s 2 h2

lemma native_p_event (b : Bool) :
    (native .p (endpoint b) : Measure (ValidTail .p)).real Ep = cR b*(1+zR b+zR b^2) := by
  rw [p_event_real,native_p_real,native_p_real,native_p_real]
  cases b <;> norm_num [cR,zR]

lemma endpoint_distance (s : ActivePhase) :
    (measurableTotalVariation (native s lowerRate : Measure (ValidTail s))
      (native s upperRate : Measure (ValidTail s))).toReal = 2*radius s := by
  cases s
  · rw [complete_sign_event _ _ Ep (Set.to_countable _).measurableSet p_signs.1 p_signs.2]
    change (ENNReal.ofReal ((native .p (endpoint false) : Measure (ValidTail .p)).real Ep -
      (native .p (endpoint true) : Measure (ValidTail .p)).real Ep)).toReal = _
    rw [native_p_event,native_p_event]
    norm_num [cR,zR,radius]
  · rw [complete_sign_event _ _ Eb (Set.to_countable _).measurableSet b_signs.1 b_signs.2]
    change (ENNReal.ofReal ((native .beta (endpoint false) : Measure (ValidTail .beta)).real Eb -
      (native .beta (endpoint true) : Measure (ValidTail .beta)).real Eb)).toReal = _
    rw [native_b_event,native_b_event]
    norm_num [cR,rR,radius]

lemma endpoint_triangle (s : ActivePhase) (D : RegularDescriptor s) :
    2*radius s ≤ fullLoss s false D + fullLoss s true D := by
  have ht := real_tv_triangle (native s lowerRate : Measure _) (law D) (native s upperRate : Measure _)
  rw [endpoint_distance,measurable_total_variation_comm (native s lowerRate : Measure _) (law D)] at ht
  exact ht

lemma original_risk_triangle (F : CommonFlow) (μ : PMF Depth)
    (h1 : μ 1 ≠ 0) (h2 : μ 2 ≠ 0) (b : Bool) :
    radius .p ≤ supportedRisk (flowMargins F) μ + completeLoss F b := by
  have hf : ∀ s, IsProbabilityMeasure (flowMargins F s) := by
    intro s; cases s
    · exact F.probP
    · exact F.probB
  have hsup := supported_endpoint_le (flowMargins F) hf μ h1 h2 .p (!b)
  have htri := integral_mono (integrable_const (2*radius .p))
    ((p_loss_integrable F false).add (p_loss_integrable F true)) (endpoint_triangle .p)
  simp only [Pi.add_apply] at htri
  rw [integral_add (p_loss_integrable F false) (p_loss_integrable F true)] at htri
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at htri
  have hmax : (∫ Q, fullLoss .p b Q ∂F.nuP) ≤ completeLoss F b := le_max_left _ _
  cases b <;> simp only [Bool.not_false,Bool.not_true,flowMargins] at hsup <;> linarith

lemma original_risk_normalized (F : CommonFlow) (μ : PMF Depth)
    (h1 : μ 1 ≠ 0) (h2 : μ 2 ≠ 0) (b : Bool) (n : ℕ) (hn : 4 ≤ n) :
    radius .p ≤ supportedRisk (flowMargins F) μ + HR b*(slack F b n/(cR b*zR b^n)) := by
  exact (original_risk_triangle F μ h1 h2 b).trans (add_le_add le_rfl (normalized_stability F b n hn))


lemma directed_event_bound {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (E : Set X) (hE : MeasurableSet E) :
    μ.real E-ν.real E ≤ (measurableTotalVariation μ ν).toReal :=
  (le_abs_self _).trans (event_gap μ ν E hE)

lemma endpoint_coordinate_excess {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (P R D : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure R] [IsProbabilityMeasure D]
    (S : Set X) (hS : MeasurableSet S)
    (hpos : ∀ t ∈ S, R.real {t} ≤ P.real {t})
    (hneg : ∀ t ∉ S, P.real {t} ≤ R.real {t}) (t : X) :
    min (P.real {t}) (R.real {t}) - D.real {t} ≤
      (measurableTotalVariation P D).toReal+(measurableTotalVariation D R).toReal-(P.real S-R.real S) ∧
    D.real {t} - max (P.real {t}) (R.real {t}) ≤
      (measurableTotalVariation P D).toReal+(measurableTotalVariation D R).toReal-(P.real S-R.real S) := by
  have hA := directed_event_bound P D S hS
  have hB := directed_event_bound D R S hS
  by_cases ht : t ∈ S
  · have diff (μ : Measure X) [IsProbabilityMeasure μ] : μ.real (S \ {t}) = μ.real S-μ.real {t} := by
      have hi := measureReal_inter_add_sdiff (μ := μ) (s := S) (measurableSet_singleton t)
      have he : S ∩ {t} = {t} := by ext x; simp; aesop
      rw [he] at hi
      linarith
    have hAd := directed_event_bound P D (S \ {t}) (hS.diff (measurableSet_singleton t))
    have hBd := directed_event_bound D R (S \ {t}) (hS.diff (measurableSet_singleton t))
    rw [diff,diff] at hAd hBd
    rw [min_eq_right (hpos t ht),max_eq_left (hpos t ht)]
    constructor <;> linarith
  · have union (μ : Measure X) [IsProbabilityMeasure μ] : μ.real (S ∪ {t}) = μ.real S+μ.real {t} :=
      measureReal_union (Set.disjoint_singleton_right.mpr ht) (measurableSet_singleton t)
    have hAu := directed_event_bound P D (S ∪ {t}) (hS.union (measurableSet_singleton t))
    have hBu := directed_event_bound D R (S ∪ {t}) (hS.union (measurableSet_singleton t))
    rw [union,union] at hAu hBu
    rw [min_eq_left (hneg t ht),max_eq_right (hneg t ht)]
    constructor <;> linarith

lemma scalar_triangle_slack (a b d G : ℝ) (hG : 0 ≤ G)
    (hlo : min a b-d ≤ G) (hhi : d-max a b ≤ G) :
    0 ≤ |d-a|+|d-b|-|a-b| ∧ |d-a|+|d-b|-|a-b| ≤ 2*G := by
  have htri : |a-b| ≤ |d-a|+|d-b| := by
    simpa [abs_sub_comm a d] using abs_sub_le a d b
  constructor
  · linarith
  · rcases le_total a b with hab | hba
    · rw [min_eq_left hab] at hlo; rw [max_eq_right hab] at hhi
      by_cases hd : d ≤ a
      · rw [abs_of_nonpos (by linarith : d-a ≤ 0),abs_of_nonpos (by linarith : d-b ≤ 0),
          abs_of_nonpos (by linarith : a-b ≤ 0)]; linarith
      · by_cases hd' : d ≤ b
        · rw [abs_of_nonneg (by linarith : 0 ≤ d-a),abs_of_nonpos (by linarith : d-b ≤ 0),
            abs_of_nonpos (by linarith : a-b ≤ 0)]; linarith
        · rw [abs_of_nonneg (by linarith : 0 ≤ d-a),abs_of_nonneg (by linarith : 0 ≤ d-b),
            abs_of_nonpos (by linarith : a-b ≤ 0)]; linarith
    · rw [min_eq_right hba] at hlo; rw [max_eq_left hba] at hhi
      by_cases hd : d ≤ b
      · rw [abs_of_nonpos (by linarith : d-a ≤ 0),abs_of_nonpos (by linarith : d-b ≤ 0),
          abs_of_nonneg (by linarith : 0 ≤ a-b)]; linarith
      · by_cases hd' : d ≤ a
        · rw [abs_of_nonpos (by linarith : d-a ≤ 0),abs_of_nonneg (by linarith : 0 ≤ d-b),
            abs_of_nonneg (by linarith : 0 ≤ a-b)]; linarith
        · rw [abs_of_nonneg (by linarith : 0 ≤ d-a),abs_of_nonneg (by linarith : 0 ≤ d-b),
            abs_of_nonneg (by linarith : 0 ≤ a-b)]; linarith

def coordinateTriangleSlack (s : ActivePhase) (t : ValidTail s) (D : RegularDescriptor s) : ℝ :=
  |(law D).real {t} - (native s lowerRate : Measure (ValidTail s)).real {t}| +
  |(law D).real {t} - (native s upperRate : Measure (ValidTail s)).real {t}| -
  |(native s lowerRate : Measure (ValidTail s)).real {t} - (native s upperRate : Measure (ValidTail s)).real {t}|
def configurationTriangleSlack (s : ActivePhase) (D : RegularDescriptor s) : ℝ :=
  fullLoss s false D+fullLoss s true D-2*radius s

lemma coordinate_triangle_control (s : ActivePhase) (t : ValidTail s) (D : RegularDescriptor s) :
    0 ≤ coordinateTriangleSlack s t D ∧ coordinateTriangleSlack s t D ≤ 2*configurationTriangleSlack s D := by
  have hG : 0 ≤ configurationTriangleSlack s D := sub_nonneg.mpr (endpoint_triangle s D)
  have hex : min ((native s lowerRate : Measure (ValidTail s)).real {t}) ((native s upperRate : Measure (ValidTail s)).real {t}) -
      (law D).real {t} ≤ configurationTriangleSlack s D ∧
      (law D).real {t} - max ((native s lowerRate : Measure (ValidTail s)).real {t})
        ((native s upperRate : Measure (ValidTail s)).real {t}) ≤ configurationTriangleSlack s D := by
    cases s
    · have h := endpoint_coordinate_excess (native .p lowerRate : Measure _) (native .p upperRate : Measure _) (law D)
        Ep (Set.to_countable _).measurableSet
        (fun t ht => ENNReal.toReal_mono (measure_ne_top _ _) (p_signs.1 t ht))
        (fun t ht => ENNReal.toReal_mono (measure_ne_top _ _) (p_signs.2 t ht)) t
      rw [measurable_total_variation_comm (native .p lowerRate : Measure _) (law D)] at h
      change _ ≤ fullLoss .p false D+fullLoss .p true D-_ ∧ _ ≤ fullLoss .p false D+fullLoss .p true D-_ at h
      have he : (native .p lowerRate : Measure (ValidTail .p)).real Ep -
          (native .p upperRate : Measure (ValidTail .p)).real Ep = 2*radius .p := by
        change (native .p (endpoint false) : Measure (ValidTail .p)).real Ep -
          (native .p (endpoint true) : Measure (ValidTail .p)).real Ep = _
        rw [native_p_event,native_p_event]; norm_num [cR,zR,radius]
      rw [he] at h
      exact h
    · have h := endpoint_coordinate_excess (native .beta lowerRate : Measure _) (native .beta upperRate : Measure _) (law D)
        Eb (Set.to_countable _).measurableSet
        (fun t ht => ENNReal.toReal_mono (measure_ne_top _ _) (b_signs.1 t ht))
        (fun t ht => ENNReal.toReal_mono (measure_ne_top _ _) (b_signs.2 t ht)) t
      rw [measurable_total_variation_comm (native .beta lowerRate : Measure _) (law D)] at h
      change _ ≤ fullLoss .beta false D+fullLoss .beta true D-_ ∧ _ ≤ fullLoss .beta false D+fullLoss .beta true D-_ at h
      have he : (native .beta lowerRate : Measure (ValidTail .beta)).real Eb -
          (native .beta upperRate : Measure (ValidTail .beta)).real Eb = 2*radius .beta := by
        change (native .beta (endpoint false) : Measure (ValidTail .beta)).real Eb -
          (native .beta (endpoint true) : Measure (ValidTail .beta)).real Eb = _
        rw [native_b_event,native_b_event]; norm_num [cR,rR,radius]
      rw [he] at h
      exact h
  exact scalar_triangle_slack _ _ _ _ hG hex.1 hex.2

lemma bounded_atom_real (s : ActivePhase) (t : ValidTail s) :
    Bounded (fun D : RegularDescriptor s => (law D).real {t}) := by
  refine ⟨((Measure.measurable_coe (measurableSet_singleton t)).comp (measurable_law s)).ennreal_toReal,
    1,by norm_num,?_⟩
  intro D; change ‖(law D {t}).toReal‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one).trans_eq (by simp)

lemma bounded_coordinate_slack (s : ActivePhase) (t : ValidTail s) : Bounded (coordinateTriangleSlack s t) :=
  ((((bounded_atom_real s t).sub (bounded_const ((native s lowerRate : Measure (ValidTail s)).real {t}))).abs).add
    (((bounded_atom_real s t).sub (bounded_const ((native s upperRate : Measure (ValidTail s)).real {t}))).abs)).sub
    (bounded_const |(native s lowerRate : Measure (ValidTail s)).real {t}-(native s upperRate : Measure (ValidTail s)).real {t}|)

lemma zero_face_coordinates (ν : (s : ActivePhase) → Measure (RegularDescriptor s))
    (hν : ∀ s, IsProbabilityMeasure (ν s)) (μ : PMF Depth) (h1 : μ 1 ≠ 0) (h2 : μ 2 ≠ 0)
    (hJ : supportedRisk ν μ = 0) (s : ActivePhase) :
    ∀ᵐ D ∂ν s, ∀ t : ValidTail s, coordinateTriangleSlack s t D = 0 := by
  letI := hν s
  have hA := supported_endpoint_le ν hν μ h1 h2 s false
  have hB := supported_endpoint_le ν hν μ h1 h2 s true
  rw [hJ] at hA hB
  have hFA := (bounded_target_loss s (endpoint false)).integrable (ν s)
  have hFB := (bounded_target_loss s (endpoint true)).integrable (ν s)
  change Integrable (fullLoss s false) (ν s) at hFA
  change Integrable (fullLoss s true) (ν s) at hFB
  have hG : Integrable (configurationTriangleSlack s) (ν s) := (hFA.add hFB).sub (integrable_const _)
  have hGI : ∫ D, configurationTriangleSlack s D ∂ν s = 0 := by
    have hi : (∫ D, configurationTriangleSlack s D ∂ν s) =
        (∫ D, fullLoss s false D ∂ν s)+(∫ D, fullLoss s true D ∂ν s)-2*radius s := by
      unfold configurationTriangleSlack
      have hadd := integral_add hFA hFB
      have hsub := integral_sub (hFA.add hFB) (integrable_const (2*radius s))
      simp only [Pi.add_apply] at hadd hsub
      rw [hsub,hadd]
      simp
    have hnonneg : 0 ≤ ∫ D, configurationTriangleSlack s D ∂ν s :=
      integral_nonneg (fun D => sub_nonneg.mpr (endpoint_triangle s D))
    linarith
  apply ae_all_iff.mpr
  intro t
  have hi := integral_mono ((bounded_coordinate_slack s t).integrable (ν s)) (hG.const_mul 2)
    (fun D => (coordinate_triangle_control s t D).2)
  rw [integral_const_mul,hGI,mul_zero] at hi
  have hpos : 0 ≤ coordinateTriangleSlack s t := fun D => (coordinate_triangle_control s t D).1
  have hzero : ∫ D, coordinateTriangleSlack s t D ∂ν s = 0 :=
    le_antisymm hi (integral_nonneg hpos)
  exact (integral_eq_zero_iff_of_nonneg hpos ((bounded_coordinate_slack s t).integrable (ν s))).mp hzero



lemma scalar_zero_interval (a b d : ℝ) (h : |d-a|+|d-b|-|a-b|=0) :
    min a b ≤ d ∧ d ≤ max a b := by
  have ordered (a b : ℝ) (hab : a ≤ b) (he : |d-a|+|d-b|-|a-b|=0) : a ≤ d ∧ d ≤ b := by
    constructor
    · by_contra hn
      have hd : d < a := lt_of_not_ge hn
      rw [abs_of_nonpos (by linarith : d-a ≤ 0),
        abs_of_nonpos (by linarith : d-b ≤ 0),abs_of_nonpos (by linarith : a-b ≤ 0)] at he
      linarith
    · by_contra hn
      have hd : b < d := lt_of_not_ge hn
      rw [abs_of_nonneg (by linarith : 0 ≤ d-a),
        abs_of_nonneg (by linarith : 0 ≤ d-b),abs_of_nonpos (by linarith : a-b ≤ 0)] at he
      linarith
  rcases le_total a b with hab | hba
  · simpa [min_eq_left hab,max_eq_right hab] using ordered a b hab h
  · have he : |d-b|+|d-a|-|b-a|=0 := by simpa [abs_sub_comm a b,add_comm] using h
    simpa [min_eq_right hba,max_eq_left hba] using ordered b a hba he

lemma zero_face_boxes (ν : (s : ActivePhase) → Measure (RegularDescriptor s))
    (hν : ∀ s, IsProbabilityMeasure (ν s)) (μ : PMF Depth) (h1 : μ 1 ≠ 0) (h2 : μ 2 ≠ 0)
    (hJ : supportedRisk ν μ = 0) (s : ActivePhase) :
    ∀ᵐ D ∂ν s, EndpointBox D := by
  filter_upwards [zero_face_coordinates ν hν μ h1 h2 hJ s] with D hD
  intro t
  have hi := scalar_zero_interval ((native s lowerRate : Measure (ValidTail s)).real {t})
    ((native s upperRate : Measure (ValidTail s)).real {t}) ((law D).real {t}) (by simpa only [coordinateTriangleSlack] using hD t)
  rw [← native_coordinate,← native_coordinate]
  rcases le_total ((native s lowerRate : Measure (ValidTail s)) {t}) ((native s upperRate : Measure (ValidTail s)) {t}) with hab | hba
  · have hr := ENNReal.toReal_mono (measure_ne_top (native s upperRate : Measure (ValidTail s)) _) hab
    change (native s lowerRate : Measure (ValidTail s)).real {t} ≤ (native s upperRate : Measure (ValidTail s)).real {t} at hr
    rw [min_eq_left hr,max_eq_right hr] at hi
    rw [min_eq_left hab,max_eq_right hab]
    exact ⟨(ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hi.1,
      (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hi.2⟩
  · have hr := ENNReal.toReal_mono (measure_ne_top (native s lowerRate : Measure (ValidTail s)) _) hba
    change (native s upperRate : Measure (ValidTail s)).real {t} ≤ (native s lowerRate : Measure (ValidTail s)).real {t} at hr
    rw [min_eq_right hr,max_eq_left hr] at hi
    rw [min_eq_right hba,max_eq_left hba]
    exact ⟨(ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hi.1,
      (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hi.2⟩

structure UnboxedCommonFlow where
  nuP : Measure PDescriptor
  nuB : Measure BDescriptor
  probP : IsProbabilityMeasure nuP
  probB : IsProbabilityMeasure nuB
  GammaB : Measure (PDescriptor × BDescriptor)
  GammaA : Measure (BDescriptor × PDescriptor)
  probGammaB : IsProbabilityMeasure GammaB
  probGammaA : IsProbabilityMeasure GammaA
  B : Kernel PDescriptor BDescriptor
  A : Kernel BDescriptor PDescriptor
  markovB : IsMarkovKernel B
  markovA : IsMarkovKernel A
  disintegrateB : GammaB.IsCondKernel B
  disintegrateA : GammaA.IsCondKernel A
  marginB₁ : GammaB.fst = nuP
  marginB₂ : GammaB.snd = nuB
  marginA₁ : GammaA.fst = nuB
  marginA₂ : GammaA.snd = nuP
  normalizedB : ∀ᵐ Q ∂nuP, residualB Q = (lawKernel .beta) ∘ₘ B Q
  normalizedA : ∀ᵐ W ∂nuB, residualA W = (lawKernel .p) ∘ₘ A W

def UnboxedCommonFlow.margins (U : UnboxedCommonFlow) :
    (s : ActivePhase) → Measure (RegularDescriptor s)
  | .p => U.nuP
  | .beta => U.nuB

lemma UnboxedCommonFlow.probMargins (U : UnboxedCommonFlow) :
    ∀ s, IsProbabilityMeasure (U.margins s) := by
  intro s; cases s
  · exact U.probP
  · exact U.probB

def UnboxedCommonFlow.zeroFace (U : UnboxedCommonFlow) (μ : PMF Depth)
    (h1 : μ 1 ≠ 0) (h2 : μ 2 ≠ 0) (hJ : supportedRisk U.margins μ = 0) : CommonFlow where
  nuP := U.nuP
  nuB := U.nuB
  probP := U.probP
  probB := U.probB
  GammaB := U.GammaB
  GammaA := U.GammaA
  probGammaB := U.probGammaB
  probGammaA := U.probGammaA
  B := U.B
  A := U.A
  markovB := U.markovB
  markovA := U.markovA
  disintegrateB := U.disintegrateB
  disintegrateA := U.disintegrateA
  marginB₁ := U.marginB₁
  marginB₂ := U.marginB₂
  marginA₁ := U.marginA₁
  marginA₂ := U.marginA₂
  normalizedB := U.normalizedB
  normalizedA := U.normalizedA
  boxP := zero_face_boxes U.margins U.probMargins μ h1 h2 hJ .p
  boxB := zero_face_boxes U.margins U.probMargins μ h1 h2 hJ .beta

lemma bounded_event_real (s : ActivePhase) (E : Set (ValidTail s)) (hE : MeasurableSet E) :
    Bounded (fun D : RegularDescriptor s => (law D).real E) := by
  refine ⟨((Measure.measurable_coe hE).comp (measurable_law s)).ennreal_toReal,1,by norm_num,?_⟩
  intro D; change ‖(law D E).toReal‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one).trans_eq (by simp)

lemma p_event_loss (Q : PDescriptor) (hQ : EndpointBox Q) (b : Bool) :
    fullLoss .p b Q = signR b * ((native .p (endpoint b) : Measure (ValidTail .p)).real Ep-(law Q).real Ep) := by
  rw [p_loss_formula Q hQ b,native_p_event,p_event_real]
  unfold defect late g coordinate
  cases b <;> norm_num [signR,cR,zR,Measure.real] <;> ring

lemma boxed_p_midpoint (F : CommonFlow)
    (hmid : (∫ Q, (law Q).real Ep ∂F.nuP) = (11758471/22781250 : ℝ)) (b : Bool) :
    (∫ Q, fullLoss .p b Q ∂F.nuP) = radius .p := by
  have he : ∀ᵐ Q ∂F.nuP, fullLoss .p b Q = signR b *
      ((native .p (endpoint b) : Measure (ValidTail .p)).real Ep-(law Q).real Ep) := by
    filter_upwards [F.boxP] with Q hQ
    exact p_event_loss Q hQ b
  rw [integral_congr_ae he, integral_const_mul,
    integral_sub (integrable_const _) ((bounded_event_real .p Ep (Set.to_countable _).measurableSet).integrable _),
    hmid,native_p_event]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  cases b <;> norm_num [signR,cR,zR,radius]

lemma midpoint_loss_lower (F : CommonFlow)
    (hmid : (∫ Q, (law Q).real Ep ∂F.nuP) = (11758471/22781250 : ℝ)) (b : Bool) :
    radius .p ≤ completeLoss F b := by
  rw [← boxed_p_midpoint F hmid b]
  exact le_max_left _ _

lemma normalized_correction (F : CommonFlow) (b : Bool) (n : ℕ) (hn : 4 ≤ n)
    (hface : radius .p ≤ completeLoss F b) :
    radius .p/HR b ≤ slack F b n/(cR b*zR b^n) := by
  have hp : 0 < HR b := by cases b <;> norm_num [HR]
  apply (div_le_iff₀ hp).mpr
  have h := hface.trans (normalized_stability F b n hn)
  simpa [mul_comm] using h

lemma zero_face_correction (U : UnboxedCommonFlow) (μ : PMF Depth)
    (h1 : μ 1 ≠ 0) (h2 : μ 2 ≠ 0) (hJ : supportedRisk U.margins μ = 0)
    (b : Bool) (n : ℕ) (hn : 4 ≤ n) :
    radius .p/HR b ≤ slack (U.zeroFace μ h1 h2 hJ) b n/(cR b*zR b^n) := by
  apply normalized_correction _ b n hn
  have h := original_risk_triangle (U.zeroFace μ h1 h2 hJ) μ h1 h2 b
  change radius .p ≤ supportedRisk U.margins μ + _ at h
  simpa [hJ] using h

lemma midpoint_correction (F : CommonFlow)
    (hmid : (∫ Q, (law Q).real Ep ∂F.nuP) = (11758471/22781250 : ℝ))
    (b : Bool) (n : ℕ) (hn : 4 ≤ n) :
    radius .p/HR b ≤ slack F b n/(cR b*zR b^n) :=
  normalized_correction F b n hn (midpoint_loss_lower F hmid b)

lemma corrected_mean_interval (F : CommonFlow) (n : ℕ)
    (ha : radius .p/HR false ≤ slack F false n/(cR false*zR false^n))
    (hb : radius .p/HR true ≤ slack F true n/(cR true*zR true^n)) :
    (4/9 : ℝ)*(2/9 : ℝ)^n*(1+radius .p/(9839648/2657205 : ℝ)) ≤ meanCoordinate F n ∧
    meanCoordinate F n ≤ (9/25 : ℝ)*(6/25 : ℝ)^n*(1-radius .p/(20723912/5859375 : ℝ)) := by
  have hpa : 0 < (4/9 : ℝ)*(2/9 : ℝ)^n := by positivity
  have hpb : 0 < (9/25 : ℝ)*(6/25 : ℝ)^n := by positivity
  norm_num [HR,slack,signR,cR,zR] at ha hb
  have ha' := (le_div_iff₀ hpa).mp ha
  have hb' := (le_div_iff₀ hpb).mp hb
  constructor <;> nlinarith

lemma midpoint_mean_interval (F : CommonFlow)
    (hmid : (∫ Q, (law Q).real Ep ∂F.nuP) = (11758471/22781250 : ℝ))
    (n : ℕ) (hn : 4 ≤ n) :
    (4/9 : ℝ)*(2/9 : ℝ)^n*(1+radius .p/(9839648/2657205 : ℝ)) ≤ meanCoordinate F n ∧
    meanCoordinate F n ≤ (9/25 : ℝ)*(6/25 : ℝ)^n*(1-radius .p/(20723912/5859375 : ℝ)) :=
  corrected_mean_interval F n (midpoint_correction F hmid false n hn) (midpoint_correction F hmid true n hn)

lemma zero_face_mean_interval (U : UnboxedCommonFlow) (μ : PMF Depth)
    (h1 : μ 1 ≠ 0) (h2 : μ 2 ≠ 0) (hJ : supportedRisk U.margins μ = 0)
    (n : ℕ) (hn : 4 ≤ n) :
    (4/9 : ℝ)*(2/9 : ℝ)^n*(1+radius .p/(9839648/2657205 : ℝ)) ≤ meanCoordinate (U.zeroFace μ h1 h2 hJ) n ∧
    meanCoordinate (U.zeroFace μ h1 h2 hJ) n ≤ (9/25 : ℝ)*(6/25 : ℝ)^n*(1-radius .p/(20723912/5859375 : ℝ)) :=
  corrected_mean_interval _ n (zero_face_correction U μ h1 h2 hJ false n hn)
    (zero_face_correction U μ h1 h2 hJ true n hn)

lemma necessary_repair_floor (F : CommonFlow) (n : ℕ) (hn : 5 ≤ n) (Δ : ℝ)
    (hmean : meanCoordinate F n = (4/9 : ℝ)*(2/9 : ℝ)^n+Δ)
    (hface : radius .p ≤ completeLoss F false) :
    ((4/9 : ℝ)*radius .p/(9839648/2657205 : ℝ))*(2/9 : ℝ)^n ≤ Δ ∧ 0 < Δ := by
  have h := normalized_correction F false n (by omega) hface
  have hp : 0 < (4/9 : ℝ)*(2/9 : ℝ)^n := by positivity
  norm_num [HR,slack,signR,cR,zR,hmean] at h
  have hi := (le_div_iff₀ hp).mp h
  have hc : 0 < ((4/9 : ℝ)*radius .p/(9839648/2657205 : ℝ))*(2/9 : ℝ)^n := by
    unfold radius; positivity
  have he : radius .p/(9839648/2657205 : ℝ)*((4/9 : ℝ)*(2/9 : ℝ)^n) =
      ((4/9 : ℝ)*radius .p/(9839648/2657205 : ℝ))*(2/9 : ℝ)^n := by ring
  rw [he] at hi
  exact ⟨hi,hc.trans_le hi⟩

lemma midpoint_repair_floor (F : CommonFlow)
    (hmid : (∫ Q, (law Q).real Ep ∂F.nuP) = (11758471/22781250 : ℝ))
    (n : ℕ) (hn : 5 ≤ n) (Δ : ℝ)
    (hmean : meanCoordinate F n = (4/9 : ℝ)*(2/9 : ℝ)^n+Δ) :
    ((4/9 : ℝ)*radius .p/(9839648/2657205 : ℝ))*(2/9 : ℝ)^n ≤ Δ ∧ 0 < Δ :=
  necessary_repair_floor F n hn Δ hmean (midpoint_loss_lower F hmid false)

lemma zero_face_repair_floor (U : UnboxedCommonFlow) (μ : PMF Depth)
    (h1 : μ 1 ≠ 0) (h2 : μ 2 ≠ 0) (hJ : supportedRisk U.margins μ = 0)
    (n : ℕ) (hn : 5 ≤ n) (Δ : ℝ)
    (hmean : meanCoordinate (U.zeroFace μ h1 h2 hJ) n = (4/9 : ℝ)*(2/9 : ℝ)^n+Δ) :
    ((4/9 : ℝ)*radius .p/(9839648/2657205 : ℝ))*(2/9 : ℝ)^n ≤ Δ ∧ 0 < Δ := by
  apply necessary_repair_floor _ n hn Δ hmean
  have h := original_risk_triangle (U.zeroFace μ h1 h2 hJ) μ h1 h2 false
  change radius .p ≤ supportedRisk U.margins μ + _ at h
  simpa [hJ] using h


end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelStabilityConsumers
