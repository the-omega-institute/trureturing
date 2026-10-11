/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The surviving stationary class determines the complete upper native law. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelStationaryLocalization
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelNativeLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelEndpointIdentification
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable
open NativeBorelCommonFlow NativeBorelSuperharmonic NativeBorelStationaryLocalization
open NativeBorelNativeLaws NativeBorelRepresentation FourthSegmentStoppedLaw NativeFullResidual
open NativeConditionalControl.Tail

/-- Conditions earned on the original margin, before taking its absorbing core. -/
def CoreAt (F : CommonFlow) (Q : PDescriptor) : Prop :=
  goodP F Q ∧ (3 / 25 : ℝ) ≤ h F Q ∧
  normalizedAction F (threeStepAverage F) Q ≤ threeStepAverage F Q ∧
  normalizedAction F (q F) Q = q F Q ∧
  (q F Q ≠ 0 → excess Q = 0) ∧
  (∀ᵐ W ∂F.B Q, goodB F W) ∧
  (∀ᵐ R ∂F.C Q, sixthFunctional F R = sixthFunctional F Q)

private theorem coreAt_ae (F : CommonFlow) : ∀ᵐ Q ∂F.nuP, CoreAt F Q := by
  obtain ⟨P, S, _, _, hp, _, hP, hS⟩ := common_flow_conull_core F
  filter_upwards [hp, (common_flow_signed_h F).2, (common_flow_q_limit F).2,
    common_flow_stationary_localization F, common_flow_stationary_edges F]
    with Q hQ hh hq hl he
  exact ⟨(hP Q hQ).1, hh.1, hh.2.2.2.2.2, hq.2.2.2, hl.2.2,
    (hP Q hQ).2.mono (fun W hW => (hS W hW).1), he⟩

private def coreSeed (F : CommonFlow) : Set PDescriptor :=
  (toMeasurable F.nuP {Q | ¬ CoreAt F Q})ᶜ

private def absorbingSequence (F : CommonFlow) : ℕ → Set PDescriptor
  | 0 => coreSeed F
  | n + 1 => absorbingSequence F n ∩ {Q | F.C Q (absorbingSequence F n)ᶜ = 0}

private theorem absorbingSequence_measurable (F : CommonFlow) (n : ℕ) :
    MeasurableSet (absorbingSequence F n) := by
  induction n with
  | zero => exact (measurableSet_toMeasurable _ _).compl
  | succ n ih => exact ih.inter ((F.C.measurable_coe ih.compl) (measurableSet_singleton 0))

private theorem absorbingSequence_conull (F : CommonFlow) (n : ℕ) :
    ∀ᵐ Q ∂F.nuP, Q ∈ absorbingSequence F n := by
  induction n with
  | zero =>
    rw [ae_iff]
    simpa only [absorbingSequence, coreSeed, Set.mem_compl_iff, not_not,
      Set.mem_ofPred_eq, Set.ofPred_mem_eq, measure_toMeasurable] using ae_iff.mp (coreAt_ae F)
  | succ n ih =>
    have hc := Measure.ae_ae_of_ae_comp (κ := F.C)
      ((common_flow_word_iteration F).1.symm ▸ ih)
    filter_upwards [ih, hc] with Q hQ hc
    exact ⟨hQ, ae_iff.mp hc⟩

/-- An absorbing conull core for the same acquired C, retaining both full residuals. -/
theorem common_flow_absorbing_core (F : CommonFlow) :
    ∃ G : Set PDescriptor, MeasurableSet G ∧ (∀ᵐ Q ∂F.nuP, Q ∈ G) ∧
      ∀ Q ∈ G, CoreAt F Q ∧
        ∀ᵐ R ∂F.C Q, R ∈ G ∧ sixthFunctional F R = sixthFunctional F Q := by
  let G := ⋂ n, absorbingSequence F n
  refine ⟨G, MeasurableSet.iInter (absorbingSequence_measurable F), ?_, ?_⟩
  · exact (ae_all_iff.mpr (absorbingSequence_conull F)).mono
      (fun Q hQ => Set.mem_iInter.mpr hQ)
  · intro Q hQ
    have hn := Set.mem_iInter.mp hQ
    have hgood : CoreAt F Q := by
      have h0 : Q ∉ toMeasurable F.nuP {Q | ¬ CoreAt F Q} := hn 0
      by_contra hbad
      exact h0 (subset_toMeasurable _ _ hbad)
    refine ⟨hgood, ?_⟩
    have hc : ∀ᵐ R ∂F.C Q, R ∈ G :=
      (ae_all_iff.mpr (fun n => ae_iff.mpr (hn (n + 1)).2)).mono
        (fun R hR => Set.mem_iInter.mpr hR)
    exact hc.and hgood.2.2.2.2.2.2

private theorem sixth_nonzero_iff (F : CommonFlow) (Q : PDescriptor) :
    sixthFunctional F Q ≠ 0 ↔ q F Q ≠ 0 := by
  constructor
  · intro hf hq
    exact hf (by simp [sixthFunctional, hq])
  · intro hq hf
    have hz := ENNReal.div_eq_zero_iff.mp hf
    exact hz.elim (pow_ne_zero 6 hq) (ENNReal.pow_ne_top (h_finite F Q))

private theorem endpoint_factors (F : CommonFlow) (Q : PDescriptor)
    (hgood : goodP F Q) (he : excess Q = 0) :
    u Q = upper ∧ ∀ᵐ W ∂F.B Q, v W = upper := by
  have hg : g Q = endpointCompletion := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (law Q) _)
      (by unfold endpointCompletion; finiteness)).mp
    have := he
    unfold excess at this
    change (g Q).toReal = endpointCompletion.toReal
    norm_num only [endpointCompletion, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    linarith
  have hm : Measurable (fun W : BDescriptor => 1 - v W) := measurable_const.sub measurable_v
  have hb : ∀ W : BDescriptor, (3 / 5 : ℝ≥0∞) ≤ 1 - v W := by
    intro W
    rw [← one_sub_upper]
    exact tsub_le_tsub_left W.property.2.1 1
  have hi : (3 / 5 : ℝ≥0∞) ≤ ∫⁻ W, 1 - v W ∂F.B Q := by
    calc
      _ = ∫⁻ _ : BDescriptor, (3 / 5 : ℝ≥0∞) ∂F.B Q := by simp
      _ ≤ _ := lintegral_mono hb
  have hi1 : (∫⁻ W, 1 - v W ∂F.B Q) ≤ 1 := by
    calc
      _ ≤ ∫⁻ _ : BDescriptor, (1 : ℝ≥0∞) ∂F.B Q := lintegral_mono (fun _ => tsub_le_self)
      _ = 1 := by simp
  have hu : (3 / 5 : ℝ≥0∞) ≤ 1 - u Q := by
    rw [← one_sub_upper]
    exact tsub_le_tsub_left Q.property.2.1 1
  have heq := hgood.2.2.2.1
  rw [hg] at heq
  have huf : 1 - u Q ≠ ∞ := ENNReal.sub_ne_top (by simp)
  have hif : (∫⁻ W, 1 - v W ∂F.B Q) ≠ ∞ := ne_top_of_le_ne_top (by simp) hi1
  have hr := congrArg ENNReal.toReal heq
  rw [ENNReal.toReal_mul] at hr
  have huR := ENNReal.toReal_mono huf hu
  have hiR := ENNReal.toReal_mono hif hi
  norm_num [endpointCompletion] at hr huR hiR
  have hU : (1 - u Q).toReal = 3 / 5 := by nlinarith
  have hI : (∫⁻ W, 1 - v W ∂F.B Q).toReal = 3 / 5 := by nlinarith
  have hI' : (∫⁻ W, 1 - v W ∂F.B Q) = (3 / 5 : ℝ≥0∞) :=
    (ENNReal.toReal_eq_toReal_iff' hif (by finiteness)).mp (by simpa using hI)
  have heRow : ∀ᵐ W ∂F.B Q, (3 / 5 : ℝ≥0∞) = 1 - v W := by
    apply ae_eq_of_ae_le_of_lintegral_le (Filter.Eventually.of_forall hb)
      (by simp only [lintegral_const, measure_univ, mul_one]; finiteness) hm.aemeasurable
    simpa only [lintegral_const, measure_univ, mul_one] using hI'.le
  have hu1 : u Q ≤ 1 := prob_le_one
  have hv1 (W : BDescriptor) : v W ≤ 1 := tsub_le_self
  constructor
  · apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (law Q) _) (by unfold upper; finiteness)).mp
    rw [ENNReal.toReal_sub_of_le hu1 (by simp)] at hU
    change (u Q).toReal = upper.toReal
    norm_num only [upper, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    norm_num at hU
    linarith
  · filter_upwards [heRow] with W hW
    apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.sub_ne_top (by simp))
      (by unfold upper; finiteness)).mp
    have hR := congrArg ENNReal.toReal hW
    rw [ENNReal.toReal_sub_of_le (hv1 W) (by simp)] at hR
    change (v W).toReal = upper.toReal
    norm_num only [upper, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    norm_num at hR
    linarith

private theorem endpoint_row (F : CommonFlow) (Q : PDescriptor)
    (hu : u Q = upper) (hv : ∀ᵐ W ∂F.B Q, v W = upper) :
    F.L Q = endpointRate • F.C Q := by
  ext E hE
  rw [L_apply F Q E hE, hu, one_sub_upper,
    Measure.smul_apply, smul_eq_mul, CommonFlow.C, Kernel.comp_apply' _ _ _ hE]
  rw [lintegral_congr_ae (hv.mono (fun W hW => by rw [hW])),
    lintegral_const_mul _ (F.A.measurable_coe hE)]
  rw [← mul_assoc]
  congr 1
  apply (ENNReal.toReal_eq_toReal_iff' (by unfold upper; finiteness)
    (by unfold endpointRate; finiteness)).mp
  norm_num [upper, endpointRate]


private theorem native_upper_coordinate (n : ℕ) (i : Letter) :
    coordinate n i (nativeEndpoint .p true) =
      (if i = 0 then upper else endpointCompletion) * endpointRate ^ n := by
  have hn := (native_atoms upperRate).1 n i
  change (native .p upperRate : Measure _) {pAtom n i} = _
  have ha : alphaMass upperRate = upper := by
    apply (ENNReal.toReal_eq_toReal_iff' (by simp [alphaMass])
      (by unfold upper; finiteness)).mp
    norm_num [alphaMass, upperRate, upper, unitInterval.coe_toNNReal]
  have hb : betaMass upperRate ^ 2 = endpointCompletion := by
    apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.pow_ne_top (by simp [betaMass]))
      (by unfold endpointCompletion; finiteness)).mp
    norm_num [betaMass, upperRate, endpointCompletion, unitInterval.symm,
      unitInterval.coe_toNNReal]
  have hz : alphaMass upperRate * betaMass upperRate = endpointRate := by
    apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (by simp [alphaMass]) (by simp [betaMass]))
      (by unfold endpointRate; finiteness)).mp
    norm_num [alphaMass, betaMass, upperRate, endpointRate, unitInterval.symm,
      unitInterval.coe_toNNReal]
  rw [hn, hb, hz, ha]

private theorem surviving_identification (F : CommonFlow) (G : Set PDescriptor)
    (hG : ∀ Q ∈ G, CoreAt F Q ∧
      ∀ᵐ R ∂F.C Q, R ∈ G ∧ sixthFunctional F R = sixthFunctional F Q) :
    ∀ Q ∈ G, q F Q ≠ 0 → Q = nativeEndpoint .p true := by
  let H := {Q | Q ∈ G ∧ q F Q ≠ 0}
  have hc (Q : PDescriptor) (hQ : Q ∈ H) : ∀ᵐ R ∂F.C Q, R ∈ H := by
    filter_upwards [(hG Q hQ.1).2] with R hR
    refine ⟨hR.1, (sixth_nonzero_iff F R).mp ?_⟩
    rw [hR.2]
    exact (sixth_nonzero_iff F Q).mpr hQ.2
  have he (Q : PDescriptor) (hQ : Q ∈ H) :
      u Q = upper ∧ (∀ᵐ W ∂F.B Q, v W = upper) :=
    endpoint_factors F Q (hG Q hQ.1).1.1 ((hG Q hQ.1).1.2.2.2.2.1 hQ.2)
  have hg (Q : PDescriptor) (hQ : Q ∈ H) : g Q = endpointCompletion := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (law Q) _)
      (by unfold endpointCompletion; finiteness)).mp
    have hz := (hG Q hQ.1).1.2.2.2.2.1 hQ.2
    unfold excess at hz
    change (g Q).toReal = endpointCompletion.toReal
    norm_num only [endpointCompletion, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    linarith
  have hi (n : ℕ) (i : Letter) : ∀ Q ∈ H,
      iterate F.L (coordinate 0 i) n Q =
        (if i = 0 then upper else endpointCompletion) * endpointRate ^ n := by
    induction n with
    | zero =>
      intro Q hQ
      simp only [iterate, pow_zero, mul_one]
      fin_cases i
      · exact (he Q hQ).1
      · exact hg Q hQ
    | succ n ih =>
      intro Q hQ
      change (∫⁻ R, iterate F.L (coordinate 0 i) n R ∂F.L Q) = _
      rw [endpoint_row F Q (he Q hQ).1 (he Q hQ).2,
        lintegral_smul_measure]
      rw [lintegral_congr_ae ((hc Q hQ).mono (fun R hR => ih R hR)), lintegral_const,
        measure_univ, mul_one, pow_succ]
      ring
  intro Q hQ hq
  have hH : Q ∈ H := ⟨hQ, hq⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Measure.ext_of_singleton
  intro t
  rcases t with ⟨t, ht⟩
  cases t with
  | none =>
    exact (regular_infinity_zero .p Q).trans ((native_atoms upperRate).2.2.2 .p).symm
  | some w =>
    obtain ⟨i, n, rfl⟩ := ht
    change coordinate n i Q = coordinate n i (nativeEndpoint .p true)
    rw [(hG Q hQ).1.1.2.2.1 n i, hi n i Q hH, native_upper_coordinate]

private theorem normalized_g_of_native (F : CommonFlow) (Q : PDescriptor)
    (hgood : goodP F Q) (hn : Q = nativeEndpoint .p true) (n : ℕ) :
    normalizedIterate F g n Q = endpointCompletion := by
  have hi := hgood.2.2.1 n 1
  change coordinate n 1 Q = iterate F.L g n Q at hi
  unfold normalizedIterate
  rw [← hi, hn, native_upper_coordinate]
  simp only [Fin.reduceEq, if_false]
  rw [mul_left_comm, ← mul_pow,
    ENNReal.inv_mul_cancel (by norm_num [endpointRate]) (by unfold endpointRate; finiteness),
    one_pow, mul_one]

private theorem g_le_three_h (F : CommonFlow) (Q : PDescriptor) :
    g Q ≤ 3 * threeStepAverage F Q := by
  unfold threeStepAverage
  rw [ENNReal.mul_div_cancel (by norm_num : (3 : ℝ≥0∞) ≠ 0)
    (by norm_num : (3 : ℝ≥0∞) ≠ ∞)]
  exact le_trans le_self_add le_self_add

private theorem normalized_mono (F : CommonFlow) (f₁ f₂ : PDescriptor → ℝ≥0∞)
    (hle : ∀ Q, f₁ Q ≤ f₂ Q) (n : ℕ) (Q : PDescriptor) :
    normalizedIterate F f₁ n Q ≤ normalizedIterate F f₂ n Q := by
  unfold normalizedIterate
  apply mul_le_mul_of_nonneg_left _ bot_le
  induction n generalizing Q with
  | zero => exact hle Q
  | succ n ih => exact lintegral_mono ih

private theorem normalized_const_mul (F : CommonFlow) (f : PDescriptor → ℝ≥0∞)
    (hf : Measurable f) (k : ℝ≥0∞) (n : ℕ) (Q : PDescriptor) :
    normalizedIterate F (fun R => k * f R) n Q = k * normalizedIterate F f n Q := by
  have hi := measurable_iterate F f hf
  have he : ∀ n Q, iterate F.L (fun R => k * f R) n Q = k * iterate F.L f n Q := by
    intro n
    induction n with
    | zero => intro Q; rfl
    | succ n ih =>
      intro Q
      simp only [iterate, ih, lintegral_const_mul _ (hi n)]
  unfold normalizedIterate
  rw [he]
  ring

/-- Survival is equivalent to the actual upper native probability descriptor. -/
theorem common_flow_surviving_native (F : CommonFlow) :
    ∃ G : Set PDescriptor, MeasurableSet G ∧ (∀ᵐ Q ∂F.nuP, Q ∈ G) ∧
      (∀ Q ∈ G, CoreAt F Q ∧
        ∀ᵐ R ∂F.C Q, R ∈ G ∧ sixthFunctional F R = sixthFunctional F Q) ∧
      ∀ Q ∈ G, q F Q ≠ 0 ↔ Q = nativeEndpoint .p true := by
  obtain ⟨G, hm, ha, hG⟩ := common_flow_absorbing_core F
  refine ⟨G, hm, ha, hG, ?_⟩
  intro Q hQ
  constructor
  · exact surviving_identification F G hG Q hQ
  · intro hn
    have hb (n : ℕ) : endpointCompletion ≤ 3 * qIterate F n Q := by
      rw [← normalized_g_of_native F Q (hG Q hQ).1.1 hn n]
      exact (normalized_mono F g (fun R => 3 * threeStepAverage F R)
        (g_le_three_h F) n Q).trans_eq
          (normalized_const_mul F (threeStepAverage F) (h_measurable F) 3 n Q)
    have hq : q F Q ≠ 0 := by
      intro hz
      have hi : endpointCompletion ≤ 3 * q F Q := by
        unfold q
        rw [ENNReal.mul_iInf_of_ne (by norm_num : (3 : ℝ≥0∞) ≠ 0)
          (by norm_num : (3 : ℝ≥0∞) ≠ ∞)]
        exact le_iInf hb
      rw [hz, mul_zero] at hi
      norm_num [endpointCompletion] at hi
    exact hq

private theorem surviving_h (F : CommonFlow) (Q : PDescriptor)
    (hgood : goodP F Q) (hn : Q = nativeEndpoint .p true) :
    threeStepAverage F Q = endpointCompletion := by
  unfold threeStepAverage
  have hg : g Q = endpointCompletion := by
    simpa only [normalizedIterate, pow_zero, iterate, one_mul] using
      normalized_g_of_native F Q hgood hn 0
  rw [hg, normalized_g_of_native F Q hgood hn 1,
    normalized_g_of_native F Q hgood hn 2]
  have he : endpointCompletion + endpointCompletion + endpointCompletion =
      endpointCompletion * 3 := by ring
  rw [he, ENNReal.mul_div_cancel_right (by norm_num : (3 : ℝ≥0∞) ≠ 0) (by simp)]

private theorem surviving_q (F : CommonFlow) (G : Set PDescriptor)
    (hG : ∀ Q ∈ G, CoreAt F Q ∧
      ∀ᵐ R ∂F.C Q, R ∈ G ∧ sixthFunctional F R = sixthFunctional F Q) :
    ∀ Q ∈ G, q F Q ≠ 0 → q F Q = endpointCompletion := by
  let H := {Q | Q ∈ G ∧ q F Q ≠ 0}
  have hn (Q : PDescriptor) (hQ : Q ∈ H) : Q = nativeEndpoint .p true :=
    surviving_identification F G hG Q hQ.1 hQ.2
  have hc (Q : PDescriptor) (hQ : Q ∈ H) : ∀ᵐ R ∂F.C Q, R ∈ H := by
    filter_upwards [(hG Q hQ.1).2] with R hR
    refine ⟨hR.1, (sixth_nonzero_iff F R).mp ?_⟩
    rw [hR.2]
    exact (sixth_nonzero_iff F Q).mpr hQ.2
  have hi (n : ℕ) : ∀ Q ∈ H, qIterate F n Q = endpointCompletion := by
    induction n with
    | zero =>
      intro Q hQ
      rw [qIterate_zero]
      exact surviving_h F Q (hG Q hQ.1).1.1 (hn Q hQ)
    | succ n ih =>
      intro Q hQ
      have he := endpoint_factors F Q (hG Q hQ.1).1.1
        ((hG Q hQ.1).1.2.2.2.2.1 hQ.2)
      change normalizedIterate F (threeStepAverage F) (n + 1) Q = _
      rw [normalizedIterate_succ F _ (h_measurable F), normalizedAction,
        endpoint_row F Q he.1 he.2, lintegral_smul_measure]
      change endpointRate⁻¹ * (endpointRate * ∫⁻ R, qIterate F n R ∂F.C Q) = _
      rw [lintegral_congr_ae ((hc Q hQ).mono (fun R hR => ih R hR)),
        lintegral_const, measure_univ, mul_one,
        ENNReal.inv_mul_cancel_left (by norm_num [endpointRate])
          (by unfold endpointRate; finiteness)]
  intro Q hQ hq
  unfold q
  simp only [hi _ Q ⟨hQ, hq⟩, iInf_const]

/-- Both original upper-endpoint singleton limits, with the actual surviving density. -/
theorem common_flow_upper_endpoint_limits (F : CommonFlow) :
    (∀ᵐ Q ∂F.nuP,
      q F Q = (if Q = nativeEndpoint .p true then endpointCompletion else 0) ∧
      q F Q / threeStepAverage F Q = (if Q = nativeEndpoint .p true then 1 else 0)) ∧
    (∀ᵐ Q ∂F.nuP, Tendsto (fun n => coordinate n 1 Q / endpointRate ^ n) atTop
      (𝓝 (if Q = nativeEndpoint .p true then endpointCompletion else 0))) ∧
    Tendsto (fun n => (∫⁻ Q, coordinate n 1 Q ∂F.nuP) / endpointRate ^ n) atTop
      (𝓝 (endpointCompletion * F.nuP {nativeEndpoint .p true})) := by
  obtain ⟨G, hmG, haG, hG, hn⟩ := common_flow_surviving_native F
  have hnorm (Q : PDescriptor) (hQ : Q ∈ G) (n : ℕ) :
      coordinate n 1 Q / endpointRate ^ n = normalizedIterate F g n Q := by
    rw [(hG Q hQ).1.1.2.2.1 n 1]
    simp only [normalizedIterate, g, div_eq_mul_inv, ENNReal.inv_pow]
    ring
  have hbound (n : ℕ) (Q : PDescriptor) :
      normalizedIterate F g n Q ≤ 3 * qIterate F n Q :=
    (normalized_mono F g (fun R => 3 * threeStepAverage F R)
      (g_le_three_h F) n Q).trans_eq
        (normalized_const_mul F (threeStepAverage F) (h_measurable F) 3 n Q)
  have hdensity : ∀ᵐ Q ∂F.nuP,
      q F Q = (if Q = nativeEndpoint .p true then endpointCompletion else 0) ∧
      q F Q / threeStepAverage F Q = (if Q = nativeEndpoint .p true then 1 else 0) := by
    filter_upwards [haG] with Q hQ
    by_cases hnative : Q = nativeEndpoint .p true
    · have hq := (hn Q hQ).mpr hnative
      rw [if_pos hnative, surviving_q F G hG Q hQ hq,
        surviving_h F Q (hG Q hQ).1.1 hnative]
      constructor
      · rfl
      · simp only [if_pos hnative]
        exact ENNReal.div_self (a := endpointCompletion) (by norm_num [endpointCompletion])
          (by unfold endpointCompletion; finiteness)
    · have hz : q F Q = 0 := by
        by_contra hq
        exact hnative ((hn Q hQ).mp hq)
      simp [hnative, hz]
  have hlim : ∀ᵐ Q ∂F.nuP,
      Tendsto (fun n => normalizedIterate F g n Q) atTop
        (𝓝 (if Q = nativeEndpoint .p true then endpointCompletion else 0)) := by
    filter_upwards [haG, (common_flow_q_limit F).2] with Q hQ hq
    by_cases hnative : Q = nativeEndpoint .p true
    · simp only [if_pos hnative, normalized_g_of_native F Q (hG Q hQ).1.1 hnative]
      exact tendsto_const_nhds
    · have hz : q F Q = 0 := by
        by_contra hnonzero
        exact hnative ((hn Q hQ).mp hnonzero)
      rw [if_neg hnative]
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (show Tendsto (fun n => 3 * qIterate F n Q) atTop (𝓝 0) from by
          simpa only [hz, mul_zero] using ENNReal.Tendsto.const_mul hq.2.1
            (Or.inr (by norm_num : (3 : ℝ≥0∞) ≠ ∞)))
        (fun _ => bot_le) (fun n => hbound n Q)
  refine ⟨hdensity, ?_, ?_⟩
  · filter_upwards [haG, hlim] with Q hQ hlim
    simpa only [hnorm Q hQ] using hlim
  · have hdom (n : ℕ) : ∀ᵐ Q ∂F.nuP,
        normalizedIterate F g n Q ≤ (30 : ℝ≥0∞) := by
      filter_upwards [(common_flow_q_limit F).2] with Q hQ
      calc
        _ ≤ 3 * qIterate F n Q := hbound n Q
        _ ≤ 3 * qIterate F 0 Q := mul_le_mul_of_nonneg_left (hQ.1 (Nat.zero_le n)) bot_le
        _ = 3 * threeStepAverage F Q := by rw [qIterate_zero]
        _ ≤ 3 * 10 := mul_le_mul_of_nonneg_left (h_global_bound F Q) bot_le
        _ = 30 := by norm_num
    have ht := tendsto_lintegral_of_dominated_convergence (fun _ : PDescriptor => 30)
      (fun n => measurable_normalizedIterate F g measurable_g n) hdom (by simp) hlim
    have hi : (∫⁻ Q, (if Q = nativeEndpoint .p true then endpointCompletion else 0) ∂F.nuP) =
        endpointCompletion * F.nuP {nativeEndpoint .p true} := by
      simpa only [Set.indicator, Set.mem_singleton_iff] using
        lintegral_indicator_const (μ := F.nuP) (measurableSet_singleton (nativeEndpoint .p true))
          endpointCompletion
    rw [hi] at ht
    convert ht using 1
    funext n
    rw [← lintegral_congr_ae (haG.mono (fun Q hQ => hnorm Q hQ n))]
    simp only [div_eq_mul_inv]
    rw [lintegral_mul_const _ (measurable_coordinate n 1)]


private theorem beta_from_native_successors (F : CommonFlow) (W : BDescriptor)
    (hgood : goodB F W) (hv : v W = upper)
    (hA : ∀ᵐ R ∂F.A W, R = nativeEndpoint .p true) :
    W = nativeEndpoint .beta true := by
  have hm : (lawKernel .p) ∘ₘ F.A W = law (nativeEndpoint .p true) := by
    ext E hE
    change (F.A W).bind (lawKernel .p) E = _
    rw [Measure.bind_apply hE (lawKernel .p).aemeasurable]
    change (∫⁻ R, law R E ∂F.A W) = _
    rw [lintegral_congr_ae (hA.mono (fun R hR => congrArg (fun D : PDescriptor => law D E) hR)), lintegral_const,
      measure_univ, mul_one]
  have hres : residualA W = residualA (nativeEndpoint .beta true) :=
    hgood.1.trans (hm.trans (native_endpoint_residuals true).2.symm)
  have hnV : v (nativeEndpoint .beta true) = upper := by
    change emission .beta (native .beta upperRate) = upper
    rw [native_emission]
    apply (ENNReal.toReal_eq_toReal_iff' (by simp [alphaMass])
      (by unfold upper; finiteness)).mp
    norm_num [alphaMass, upperRate, upper, unitInterval.coe_toNNReal]
  have reconstruct (D : BDescriptor) :
      law D = (1 - v D) • Measure.dirac betaStop +
        v D • (residualA D).map prependA := by
    have h0 : v D ≠ 0 := by
      have hl : lower ≠ 0 := by norm_num [lower]
      exact ne_of_gt ((pos_iff_ne_zero.mpr hl).trans_le D.property.1)
    have hf : v D ≠ ∞ := ENNReal.sub_ne_top (by simp)
    rw [NativeBorelCommonFlow.residualA, Measure.map_smul, smul_smul,
      ENNReal.mul_inv_cancel h0 hf, one_smul]
    have hs : 1 - v D = law D {betaStop} := ENNReal.sub_sub_cancel (by simp) prob_le_one
    rw [hs]
    exact partition_reconstruct _ prependA_embedding _ b_not_prefix b_partition _
  apply Subtype.ext
  apply Subtype.ext
  change law W = law (nativeEndpoint .beta true)
  rw [reconstruct W, reconstruct (nativeEndpoint .beta true), hv, hnV, hres]

/-- The original B/A successors on surviving mass are the actual upper native laws. -/
theorem common_flow_surviving_transitions (F : CommonFlow) :
    ∀ᵐ Q ∂F.nuP, q F Q ≠ 0 →
      u Q = upper ∧ F.L Q = endpointRate • F.C Q ∧
        ∀ᵐ W ∂F.B Q, W = nativeEndpoint .beta true ∧
          ∀ᵐ R ∂F.A W, R = nativeEndpoint .p true := by
  obtain ⟨G, _, haG, hG, hn⟩ := common_flow_surviving_native F
  filter_upwards [haG] with Q hQ
  intro hq
  have he := endpoint_factors F Q (hG Q hQ).1.1 ((hG Q hQ).1.2.2.2.2.1 hq)
  refine ⟨he.1, endpoint_row F Q he.1 he.2, ?_⟩
  have hc : ∀ᵐ R ∂F.C Q, R = nativeEndpoint .p true := by
    filter_upwards [(hG Q hQ).2] with R hR
    apply (hn R hR.1).mp
    apply (sixth_nonzero_iff F R).mp
    rw [hR.2]
    exact (sixth_nonzero_iff F Q).mpr hq
  have hA := Kernel.ae_ae_of_ae_comp hc
  filter_upwards [he.2, (hG Q hQ).1.2.2.2.2.2.1, hA] with W hv hb hA
  exact ⟨beta_from_native_successors F W hb hv hA, hA⟩

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelEndpointIdentification
