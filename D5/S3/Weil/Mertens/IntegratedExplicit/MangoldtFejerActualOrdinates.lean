/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerActualOrdinates
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positivity at actual scaled zeta ordinates gives the sharp asymptotic Fejér bound. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtFejerOptimality
import D5.S3.Weil.ZeroData.CumulativeRiemannVonMangoldt
import D5.S3.Weil.ZetaRvm.NcountWindow

/-! The positive zeta ordinates sample each fixed positive frequency on a tail of
scales. The resulting Fejér bound is uniform in the choice of probability measure. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtFejerActualOrdinates

open Filter MeasureTheory Real Set
open scoped Topology
open MangoldtFejerOptimality (cosineTransform integral_gap_eq_sub_tsum)
open D5.S3.Weil.ZeroData.CumulativeRiemannVonMangoldt (cumulative_count_asymptotic)

private theorem scaled_count_asymptotic {a : ℝ} (ha : 0 < a) :
    Tendsto (fun T : ℝ => (Zeta23.Ncount 0 (a * T) : ℝ) / (T * log T))
      atTop (𝓝 (a / (2 * π))) := by
  have hscale : Tendsto (fun T : ℝ => a * T) atTop atTop := tendsto_id.const_mul_atTop ha
  have hcount : Tendsto (fun u : ℝ => (Zeta23.Ncount 0 u : ℝ) / (u * log u))
      atTop (𝓝 (1 / (2 * π))) := by
    simpa only [Zeta23.zetaZeroConfig_N] using cumulative_count_asymptotic
  have hlog : Tendsto (fun T : ℝ => log a / log T) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp tendsto_log_atTop).const_mul (log a)
  have hratio : Tendsto (fun T : ℝ => a * (1 + log a / log T)) atTop (𝓝 a) := by
    simpa only [add_zero, mul_one] using (hlog.const_add 1).const_mul a
  rw [show a / (2 * π) = (1 / (2 * π)) * a by ring]
  apply ((hcount.comp hscale).mul hratio).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ), hscale.eventually (eventually_gt_atTop 1)]
    with T hT haT
  dsimp only [Function.comp_def]
  have hT0 : 0 < T := zero_lt_one.trans hT
  have haTlog : log (a * T) ≠ 0 := (log_pos haT).ne'
  rw [log_mul ha.ne' hT0.ne'] at haTlog ⊢
  field_simp [ha.ne', hT0.ne', (log_pos hT).ne', haTlog]
  ring

private theorem eventually_exists_zero_in_scaled_window {a b : ℝ} (ha : 0 < a)
    (hab : a < b) :
    ∀ᶠ T : ℝ in atTop, (Zeta23.zerosIn (a * T) (b * T)).Nonempty := by
  have hlim : 0 < b / (2 * π) - a / (2 * π) :=
    sub_pos.mpr (div_lt_div_of_pos_right hab (by positivity))
  have hdiff := (scaled_count_asymptotic (ha.trans hab)).sub (scaled_count_asymptotic ha)
  filter_upwards [hdiff.eventually (lt_mem_nhds hlim), eventually_gt_atTop (1 : ℝ)]
    with T hcount hT
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hlt : Zeta23.Ncount 0 (a * T) < Zeta23.Ncount 0 (b * T) := by
    have hdiv : (Zeta23.Ncount 0 (a * T) : ℝ) / (T * log T) <
        (Zeta23.Ncount 0 (b * T) : ℝ) / (T * log T) := sub_pos.mp hcount
    exact_mod_cast (div_lt_div_iff_of_pos_right (mul_pos hT0 (log_pos hT))).mp hdiv
  have hadd := Zeta23.Ncount_add (mul_nonneg ha.le hT0.le)
    (mul_le_mul_of_nonneg_right hab.le hT0.le)
  by_contra hempty
  have hzero : Zeta23.Ncount (a * T) (b * T) = 0 := by
    simp [Zeta23.Ncount, Set.not_nonempty_iff_eq_empty.mp hempty]
  rw [hadd, hzero, add_zero] at hlt
  exact (lt_irrefl _) hlt

private theorem eventually_scaled_ordinate_near {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∃ ρ : ℂ, Zeta23.IsNontrivialZero ρ ∧
      0 < ρ.im ∧ |ρ.im / T - c| < δ := by
  let a := max (c / 2) (c - δ / 2)
  let b := c + δ / 2
  have ha : 0 < a := (half_pos hc).trans_le (le_max_left _ _)
  have hac : a < c := max_lt (by linarith) (by linarith)
  have hab : a < b := hac.trans (by dsimp [b]; linarith)
  filter_upwards [eventually_exists_zero_in_scaled_window ha hab, eventually_gt_atTop (0 : ℝ)]
    with T hwindow hT
  obtain ⟨ρ, hρ, hlo, hhi⟩ := hwindow
  refine ⟨ρ, hρ, (mul_pos ha hT).trans hlo, abs_lt.mpr ⟨?_, ?_⟩⟩
  · have ha' : c - δ / 2 ≤ a := le_max_right _ _
    linarith [(lt_div_iff₀ hT).mpr hlo]
  · have hb' := (div_le_iff₀ hT).mpr hhi
    dsimp [b] at hb'
    linarith

private theorem integrable_cosine (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    Integrable (fun b : ℝ => cos (t * b)) μ := by
  have hc : Continuous (fun b : ℝ => cos (t * b)) := by fun_prop
  exact Integrable.of_bound hc.aestronglyMeasurable 1
    (.of_forall fun b => by simpa only [Real.norm_eq_abs] using abs_cos_le_one (t * b))

private theorem abs_cosineTransform_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    |cosineTransform μ t| ≤ 1 := by
  simpa [cosineTransform, Real.norm_eq_abs] using
    (norm_integral_le_of_norm_le_const (μ := μ) (.of_forall fun b : ℝ =>
      show ‖cos (t * b)‖ ≤ 1 by rw [Real.norm_eq_abs]; exact abs_cos_le_one _))

private theorem abs_cosineTransform_sub_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ b ∂μ, b ∈ Icc (0 : ℝ) (1 / 2)) (s t : ℝ) :
    |cosineTransform μ s - cosineTransform μ t| ≤ |s - t| / 2 := by
  unfold cosineTransform
  rw [← integral_sub (integrable_cosine μ s) (integrable_cosine μ t)]
  have hbound : ∀ᵐ b ∂μ, ‖cos (s * b) - cos (t * b)‖ ≤ |s - t| / 2 := by
    filter_upwards [hμ] with b hb
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |s * b - t * b| := abs_cos_sub_cos_le _ _
      _ = |s - t| * b := by rw [← sub_mul, abs_mul, abs_of_nonneg hb.1]
      _ ≤ |s - t| / 2 := by linarith [mul_le_mul_of_nonneg_left hb.2 (abs_nonneg (s - t))]
  simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const hbound

/-- For all sufficiently large real scales, positivity at the scaled positive
ordinates of the actual zeta zeros bounds the Fejér coefficient uniformly over
probability measures supported almost everywhere on `[0, 1/2]`. -/
theorem eventually_fejer_averaging_coefficient_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      (∀ᵐ b ∂μ, b ∈ Icc (0 : ℝ) (1 / 2)) →
      (∀ ρ : ℂ, Zeta23.IsNontrivialZero ρ → 0 < ρ.im →
        0 ≤ cosineTransform μ (ρ.im / T)) →
      (∫ b, (b / 2 - b ^ 2) ∂μ) / 2 ≤ 1 / 48 + ε := by
  classical
  let w (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 2
  let η : ℝ := 4 * π ^ 2 * ε
  have hw : Summable w := hasSum_zeta_two.summable
  have hη : 0 < η := by dsimp [η]; positivity
  have hsum := hw.hasSum
  rw [HasSum, Metric.tendsto_nhds] at hsum
  obtain ⟨s, hs⟩ := (hsum η hη).exists
  let tail : Set ℕ := (↑s : Set ℕ)ᶜ
  have htail : (∑' n : tail, w n) < η := by
    rw [Real.dist_eq, abs_sub_comm, ← hw.sum_add_tsum_compl (s := s), add_sub_cancel_left] at hs
    exact (le_abs_self _).trans_lt hs
  have hsamples : ∀ᶠ T : ℝ in atTop, ∀ n ∈ s, 0 < n →
      ∃ ρ : ℂ, Zeta23.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ |ρ.im / T - 4 * π * n| < ε :=
    (eventually_all_finset s).mpr fun n _ => by
      by_cases hn : 0 < n
      · exact (eventually_scaled_ordinate_near (c := 4 * π * n) (by positivity) hε).mono
          fun _ h _ => h
      · exact .of_forall fun _ hn' => (hn hn').elim
  filter_upwards [hsamples] with T hT
  intro μ hprob hμ hcos
  let f (n : ℕ) : ℝ := cosineTransform μ (4 * π * n) / (n : ℝ) ^ 2
  have hf_norm (n : ℕ) : ‖f n‖ ≤ w n := by
    rw [Real.norm_eq_abs]
    dsimp only [f]
    rw [abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))]
    exact div_le_div_of_nonneg_right (abs_cosineTransform_le_one μ _) (sq_nonneg _)
  have hf : Summable f := hw.of_norm_bounded hf_norm
  have hhead : -η ≤ ∑ n ∈ s, f n := by
    have hterm (n : ℕ) (hn : n ∈ s) : -ε * w n ≤ f n := by
      rcases n.eq_zero_or_pos with rfl | hn0
      · simp [w, f]
      obtain ⟨ρ, hρ, hρ0, hclose⟩ := hT n hn hn0
      have hlip := abs_cosineTransform_sub_le μ hμ (ρ.im / T) (4 * π * n)
      have hsample := hcos ρ hρ hρ0
      have hmoment : -ε ≤ cosineTransform μ (4 * π * n) := by
        linarith [le_abs_self (cosineTransform μ (ρ.im / T) - cosineTransform μ (4 * π * n))]
      simpa only [w, f, mul_one_div] using div_le_div_of_nonneg_right hmoment (sq_nonneg (n : ℝ))
    have hsum_le : (∑ n ∈ s, w n) ≤ π ^ 2 / 6 :=
      (hw.sum_le_tsum s (fun n _ => by dsimp [w]; positivity)).trans_eq hasSum_zeta_two.tsum_eq
    calc
      -η ≤ -ε * (π ^ 2 / 6) := by dsimp [η]; nlinarith [mul_nonneg (sq_nonneg π) hε.le]
      _ ≤ -ε * (∑ n ∈ s, w n) := mul_le_mul_of_nonpos_left hsum_le (neg_nonpos.mpr hε.le)
      _ ≤ _ := by rw [Finset.mul_sum]; exact Finset.sum_le_sum hterm
  have hrest : -η ≤ ∑' n : tail, f n := by
    have h : (∑' n : tail, -w n.val) ≤ ∑' n : tail, f n :=
      (hw.subtype tail).neg.tsum_mono (hf.subtype tail) fun n => by
        change -w n.val ≤ f n.val
        have habs : |f n.val| ≤ w n.val := by
          rw [← Real.norm_eq_abs]
          exact hf_norm n.val
        exact (abs_le.mp habs).1
    rw [tsum_neg] at h
    exact (neg_le_neg htail.le).trans h
  have hlower : -2 * η ≤ ∑' n, f n := by
    rw [← hf.sum_add_tsum_compl (s := s)]
    calc
      -2 * η = -η + -η := by ring
      _ ≤ _ := add_le_add hhead hrest
  have hquot : -2 * ε ≤ (∑' n, f n) / (4 * π ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * π ^ 2)).mpr
    convert hlower using 1
    dsimp [η]
    ring
  rw [integral_gap_eq_sub_tsum μ hμ]
  change (1 / 24 - (∑' n, f n) / (4 * π ^ 2)) / 2 ≤ 1 / 48 + ε
  linarith

/-- The coefficients attainable by laws with nonnegative cosine transform at the
scaled positive zeta ordinates. -/
def fejerAveragingCoefficients (T : ℝ) : Set ℝ :=
  {q | ∃ (μ : Measure ℝ), IsProbabilityMeasure μ ∧
    (∀ᵐ b ∂μ, b ∈ Icc (0 : ℝ) (1 / 2)) ∧
    (∀ ρ : ℂ, Zeta23.IsNontrivialZero ρ → 0 < ρ.im →
      0 ≤ cosineTransform μ (ρ.im / T)) ∧
    (∫ b, (b / 2 - b ^ 2) ∂μ) / 2 = q}

/-- The supremum over admissible laws tends to `1 / 48` as the scale grows. -/
theorem tendsto_sSup_fejerAveragingCoefficients :
    Tendsto (fun T => sSup (fejerAveragingCoefficients T)) atTop (𝓝 (1 / 48)) := by
  have hmem (T : ℝ) : 1 / 48 ∈ fejerAveragingCoefficients T := by
    obtain ⟨μ, hprob, hμ, hcos, hval⟩ :=
      MangoldtFejerOptimality.isGreatest_fejer_averaging_coefficient.1
    exact ⟨μ, hprob, hμ, fun ρ _ _ => hcos (ρ.im / T), hval⟩
  have hupper {ε : ℝ} (hε : 0 < ε) :
      ∀ᶠ T : ℝ in atTop, ∀ q ∈ fejerAveragingCoefficients T, q ≤ 1 / 48 + ε := by
    filter_upwards [eventually_fejer_averaging_coefficient_le hε] with T hT
    rintro q ⟨μ, hprob, hμ, hcos, rfl⟩
    let _ := hprob
    exact hT μ hμ hcos
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [hupper zero_lt_one] with T hT
    exact ha.trans_le (le_csSup ⟨1 / 48 + 1, fun _ hq => hT _ hq⟩ (hmem T))
  · intro a ha
    have hε : 0 < (a - 1 / 48) / 2 := by linarith
    filter_upwards [hupper hε] with T hT
    exact (csSup_le ⟨_, hmem T⟩ hT).trans_lt (by linarith)

#print axioms eventually_fejer_averaging_coefficient_le
#print axioms tendsto_sSup_fejerAveragingCoefficients

end D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtFejerActualOrdinates
