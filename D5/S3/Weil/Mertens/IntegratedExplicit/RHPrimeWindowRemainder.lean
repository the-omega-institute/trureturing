/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowRemainder
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowRemainder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Under RH the prime-window discrepancy has an endpoint primitive and cluster interval. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster

/-! Integrating the actual zero modes retains the phases at both cutoffs. For a
fixed left cutoff, the error integral converges and the phase orbit supplies
every value in the translated primitive image. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
  (actualZero actualData actualOccurrenceEquiv actual_height_gt_ten firstLiMass firstLiMass_pos)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder

open PrimePhaseCluster (phaseOrbit phaseOrbit_cluster_iff mapClusterPt_of_sub_tendsto_zero)
open PrimeOnlyTailCorrection (primeTail)
open RHPrimeWindowMean (normalizedZeroSeries frequency frequency_real exp_mode_norm
  normalized_hasSum normalizedMass windowError normalizedZeroSeries_continuous
  windowError_integrable mass_log_substitution)

/-- The real primitive evaluated on a sequence of unit phases. -/
def spectralPrimitive (h : ℕ → Circle) : ℝ :=
  (∑' k : ℕ, actualCoeff k * (h k : ℂ) / (Complex.I * (actualZero k).im)).re

/-- The prime-only negative mass after subtraction of its logarithmic main term. -/
def windowDiscrepancy (a B : ℝ) : ℝ :=
  (∫ x in a..B, max (-primeTail x) 0 / Real.sqrt x) - 2 * Real.log (B / a)

/-- The limiting error integral minus the primitive at the fixed left cutoff. -/
def fixedCutoffConstant (a : ℝ) : ℝ :=
  (∫ y in Ioi (Real.log a), windowError y) - spectralPrimitive (phaseOrbit (Real.log a))

private lemma frequency_eq_ordinate (hRH : RiemannHypothesis) (k : ℕ) :
    frequency k = Complex.I * (actualZero k).im := by
  apply Complex.ext
  · simp [frequency_real hRH k, Complex.mul_re]
  · simp [frequency, Complex.sub_im, Complex.mul_im, Complex.div_im]

private lemma phaseOrbit_eq_mode (hRH : RiemannHypothesis) (y : ℝ) (k : ℕ) :
    (phaseOrbit y k : ℂ) = Complex.exp (frequency k * y) := by
  rw [phaseOrbit, Circle.coe_exp, frequency_eq_ordinate hRH, Complex.ofReal_mul]
  congr 1
  ring

private lemma ordinate_norm (k : ℕ) : 10 < ‖Complex.I * (actualZero k).im‖ := by
  simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] using
    actual_height_gt_ten (actualZero k) (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)

private lemma primitive_term_bound (h : ℕ → Circle) (k : ℕ) :
    ‖actualCoeff k * (h k : ℂ) / (Complex.I * (actualZero k).im)‖ ≤ ‖actualCoeff k‖ / 10 := by
  rw [norm_div, norm_mul, Circle.norm_coe, mul_one]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) (ordinate_norm k).le

private lemma primitive_majorant_summable : Summable (fun k : ℕ => ‖actualCoeff k‖ / 10) :=
  actualCoeff_hasSum.summable.norm.div_const 10

private lemma primitive_summable (h : ℕ → Circle) :
    Summable (fun k : ℕ => actualCoeff k * (h k : ℂ) / (Complex.I * (actualZero k).im)) :=
  Summable.of_norm_bounded primitive_majorant_summable (primitive_term_bound h)

private lemma spectralPrimitive_continuous : Continuous spectralPrimitive := by
  apply Complex.continuous_re.comp
  exact continuous_tsum (fun _ => by fun_prop) primitive_majorant_summable
    (fun k h => primitive_term_bound h k)

private lemma zero_series_window_primitive (hRH : RiemannHypothesis) {a b : ℝ} (hab : a ≤ b) :
    (∫ y in a..b, (normalizedZeroSeries y).re) =
      spectralPrimitive (phaseOrbit b) - spectralPrimitive (phaseOrbit a) := by
  let term (k : ℕ) (y : ℝ) := actualCoeff k * Complex.exp (frequency k * y)
  have hs := actualCoeff_hasSum.summable.norm
  have hi : HasSum (fun k : ℕ => ∫ y in a..b, term k y)
      (∫ y in a..b, normalizedZeroSeries y) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k (_ : ℝ) => ‖actualCoeff k‖)
    · intro k
      exact (show Continuous (term k) by dsimp [term]; fun_prop).aestronglyMeasurable
    · intro k
      exact ae_of_all _ fun y => by simp [term, exp_mode_norm hRH]
    · exact ae_of_all _ fun _ _ => hs
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun y _ => normalized_hasSum y
  have hterm (k : ℕ) :
      (∫ y in a..b, term k y) =
        actualCoeff k * (phaseOrbit b k : ℂ) / (Complex.I * (actualZero k).im) -
        actualCoeff k * (phaseOrbit a k : ℂ) / (Complex.I * (actualZero k).im) := by
    have hf : frequency k ≠ 0 := by
      rw [frequency_eq_ordinate hRH, ← norm_pos_iff]
      exact (by norm_num : (0 : ℝ) < 10).trans (ordinate_norm k)
    simp only [term, intervalIntegral.integral_const_mul, integral_exp_mul_complex hf,
      phaseOrbit_eq_mode hRH, ← frequency_eq_ordinate hRH k, ← sub_div, ← mul_sub, mul_div_assoc]
  have hre : (∫ y in a..b, (normalizedZeroSeries y).re) =
      (∫ y in a..b, normalizedZeroSeries y).re := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    exact integral_re (normalizedZeroSeries_continuous.intervalIntegrable a b).1
  rw [hre, ← hi.tsum_eq, spectralPrimitive, spectralPrimitive]
  rw [tsum_congr hterm, (primitive_summable (phaseOrbit b)).tsum_sub
    (primitive_summable (phaseOrbit a)), Complex.sub_re]

private lemma window_error_identity (hRH : RiemannHypothesis) {a B : ℝ}
    (ha : 2 ≤ a) (haB : a ≤ B) :
    windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
      spectralPrimitive (phaseOrbit (Real.log a)) =
        ∫ y in Real.log a..Real.log B, windowError y := by
  have ha0 : 0 < a := by linarith
  have hlog := Real.log_le_log ha0 haB
  have hlo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ha
  have hiE : IntervalIntegrable windowError volume (Real.log a) (Real.log B) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlog).mpr
      ((windowError_integrable hRH).mono_set fun _ hy => hlo.trans_lt hy.1)
  have hiZ : IntervalIntegrable (fun y => (normalizedZeroSeries y).re) volume
      (Real.log a) (Real.log B) :=
    (Complex.continuous_re.comp normalizedZeroSeries_continuous).intervalIntegrable _ _
  have hdensity : normalizedMass = fun y => windowError y + (2 + (normalizedZeroSeries y).re) := by
    funext y
    dsimp [windowError]
    ring
  rw [windowDiscrepancy, mass_log_substitution ha haB, Real.log_div (ha0.trans_le haB).ne' ha0.ne',
    hdensity, intervalIntegral.integral_add hiE (intervalIntegrable_const.add hiZ),
    intervalIntegral.integral_add intervalIntegrable_const hiZ, intervalIntegral.integral_const,
    smul_eq_mul, zero_series_window_primitive hRH hlog]
  ring

private lemma uniform_error (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, 2 ≤ X ∧ ∀ a B : ℝ, X ≤ a → a ≤ B →
      |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
        spectralPrimitive (phaseOrbit (Real.log a))| < ε := by
  have htail : Tendsto (fun a : ℝ => ∫ y in Ioi (Real.log a), |windowError y|) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero Real.tendsto_log_atTop
  have hsmall := (Metric.tendsto_nhds.mp htail) ε hε
  obtain ⟨X, hX⟩ := eventually_atTop.mp hsmall
  refine ⟨max 2 X, le_max_left _ _, fun a B ha hab => ?_⟩
  have ha2 := (le_max_left 2 X).trans ha
  have ha0 : 0 < a := by linarith
  have hlog := Real.log_le_log ha0 hab
  have hlo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ha2
  rw [window_error_identity hRH ha2 hab]
  calc
    _ ≤ ∫ y in Real.log a..Real.log B, |windowError y| :=
      intervalIntegral.abs_integral_le_integral_abs hlog
    _ ≤ ∫ y in Ioi (Real.log a), |windowError y| := by
      rw [intervalIntegral.integral_of_le hlog]
      exact setIntegral_mono_set (((windowError_integrable hRH).mono_set (Ioi_subset_Ioi hlo)).norm)
        (ae_of_all _ fun _ => abs_nonneg _) (ae_of_all _ Ioc_subset_Ioi_self)
    _ < ε := by
      have hx := hX a ((le_max_right 2 X).trans ha)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at hx
      exact hx

private lemma primitive_varies (hRH : RiemannHypothesis) :
    ∃ t : ℝ, spectralPrimitive (phaseOrbit 0) < spectralPrimitive (phaseOrbit t) := by
  let f (y : ℝ) := (normalizedZeroSeries y).re
  have hf : Continuous f := Complex.continuous_re.comp normalizedZeroSeries_continuous
  have hf0 : 0 < f 0 := by
    have hsum : normalizedZeroSeries 0 = (firstLiMass : ℂ) := by
      apply HasSum.unique ?_ actualCoeff_hasSum
      simpa using normalized_hasSum 0
    simpa only [f, hsum, Complex.ofReal_re] using firstLiMass_pos
  have hnear : ∀ᶠ y in 𝓝 (0 : ℝ), 0 < f y :=
    hf.continuousAt (Ioi_mem_nhds hf0)
  obtain ⟨δ, hδ, hδf⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  have hhalf := half_pos hδ
  have hpos : 0 < ∫ y in 0..δ / 2, f y := by
    apply intervalIntegral.integral_pos hhalf hf.continuousOn
    · intro y hy
      refine (hδf (y := y) ?_).le
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hy.1.le]
      exact hy.2.trans_lt (half_lt_self hδ)
    · exact ⟨0, ⟨le_rfl, hhalf.le⟩, hf0⟩
  refine ⟨δ / 2, sub_pos.mp ?_⟩
  rwa [← zero_series_window_primitive hRH hhalf.le]

private lemma fixed_cutoff_error (hRH : RiemannHypothesis) {a : ℝ} (ha : 2 ≤ a) :
    Tendsto (fun B : ℝ => windowDiscrepancy a B -
      (fixedCutoffConstant a + spectralPrimitive (phaseOrbit (Real.log B)))) atTop (𝓝 0) := by
  have hlo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ha
  have hlimit := intervalIntegral_tendsto_integral_Ioi (Real.log a)
    ((windowError_integrable hRH).mono_set (Ioi_subset_Ioi hlo)) Real.tendsto_log_atTop
  have hcenter := hlimit.sub_const (∫ y in Ioi (Real.log a), windowError y)
  rw [sub_self] at hcenter
  refine hcenter.congr' ?_
  filter_upwards [eventually_ge_atTop a] with B hB
  rw [← window_error_identity hRH ha hB, fixedCutoffConstant]
  ring

private lemma fixed_cutoff_cluster (hRH : RiemannHypothesis) {a : ℝ} (ha : 2 ≤ a) :
    {y | MapClusterPt y atTop (windowDiscrepancy a)} =
      (fun h => fixedCutoffConstant a + spectralPrimitive h) '' closure (range phaseOrbit) := by
  let H := closure (range phaseOrbit)
  let P := fun h => fixedCutoffConstant a + spectralPrimitive h
  have hP : Continuous P := spectralPrimitive_continuous.const_add _
  have hclosed : IsClosed (P '' H) := (isClosed_closure.isCompact.image hP).isClosed
  have herror := fixed_cutoff_error hRH ha
  ext y
  change MapClusterPt y atTop (windowDiscrepancy a) ↔ y ∈ P '' H
  constructor
  · intro hy
    exact hclosed.mem_of_mapClusterPt (mapClusterPt_of_sub_tendsto_zero herror hy)
      (Eventually.of_forall fun B =>
        mem_image_of_mem P (subset_closure (mem_range_self (Real.log B))))
  · rintro ⟨h, hh, rfl⟩
    have horbit := ((phaseOrbit_cluster_iff h).mpr hh).continuousAt_comp hP.continuousAt
    have hlog : MapClusterPt (P h) atTop (fun B => P (phaseOrbit (Real.log B))) := by
      apply MapClusterPt.of_comp Real.tendsto_exp_atTop
      simpa only [Function.comp_def, Real.log_exp] using horbit
    exact mapClusterPt_of_sub_tendsto_zero (by simpa only [neg_sub, neg_zero] using herror.neg) hlog

private lemma fixed_cutoff_interval (hRH : RiemannHypothesis) (a : ℝ) :
    ∃ lower upper : ℝ, lower < upper ∧
      (fun h => fixedCutoffConstant a + spectralPrimitive h) '' closure (range phaseOrbit) =
        Icc lower upper := by
  let H := closure (range phaseOrbit)
  let P := fun h => fixedCutoffConstant a + spectralPrimitive h
  have hP : Continuous P := spectralPrimitive_continuous.const_add _
  have hphase : Continuous phaseOrbit := continuous_pi fun k => by unfold phaseOrbit; fun_prop
  have hconn : IsConnected (P '' H) :=
    (isConnected_range hphase).closure.image P hP.continuousOn
  have hcompact : IsCompact (P '' H) := isClosed_closure.isCompact.image hP
  obtain ⟨t, ht⟩ := primitive_varies hRH
  have hmem (s : ℝ) : P (phaseOrbit s) ∈ P '' H :=
    mem_image_of_mem P (subset_closure (mem_range_self s))
  exact ⟨sInf (P '' H), sSup (P '' H),
    (csInf_le hcompact.bddBelow (hmem 0)).trans_lt
      ((add_lt_add_right ht (fixedCutoffConstant a)).trans_le (le_csSup hcompact.bddAbove (hmem t))),
    eq_Icc_of_connected_compact hconn hcompact⟩

/-- Under RH, the endpoint difference removes the discrepancy uniformly for late cutoffs.
For a fixed left cutoff the cluster set is the translated primitive image, a nondegenerate
compact real interval. -/
theorem prime_window_remainder_of_rh (hRH : RiemannHypothesis) :
    (∀ ε : ℝ, 0 < ε → ∃ X : ℝ, 2 ≤ X ∧ ∀ a B : ℝ, X ≤ a → a ≤ B →
      |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
        spectralPrimitive (phaseOrbit (Real.log a))| < ε) ∧
    (∀ a : ℝ, 2 ≤ a →
      {y | MapClusterPt y atTop (windowDiscrepancy a)} =
        (fun h => fixedCutoffConstant a + spectralPrimitive h) '' closure (range phaseOrbit) ∧
      ∃ lower upper : ℝ, lower < upper ∧
        {y | MapClusterPt y atTop (windowDiscrepancy a)} = Icc lower upper) := by
  refine ⟨fun ε hε => uniform_error hRH hε, fun a ha => ?_⟩
  have hcluster := fixed_cutoff_cluster hRH ha
  rw [hcluster]
  exact ⟨rfl, fixed_cutoff_interval hRH a⟩

end D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder
