/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeAttainedShortWindows
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeAttainedShortWindows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An attained zeta abscissa gives recurring whole windows of positive prime tail. -/

import D5.S3.Analytic.Laplace.MaximalRealPartProjection
import D5.S3.Arith.Robin.Analytic.ActualUnattainedChebyshevWindows
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection

/-! Positive fixed-ratio windows for the actual prime-only Chebyshev tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped ComplexConjugate Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Arith.Robin.Analytic.ActualUnattainedAbscissaFilter
  (actual_conjugate_occurrence actual_occurrence_of_zero)
open D5.S3.Arith.Robin.Analytic.ActualUnattainedChebyshevWindows (q_integrable_average)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZeroData.ActualHighZeroFilter (exists_actual_high_zero_filter)
open PositiveSpectralKernel (expMoment)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedShortWindows

open ActualFilteredExplicitFormula
  (actual_filtered_explicit_formula averagedActualCorrection averagedActualCorrection_bounds)
open ActualFilteredLeadingPair (actual_filtered_leading_pair)
open CountableResolvent (spectralExp)
open MaximalRealPartProjection
open PrimeOnlyTailCorrection (primeTail prime_power_window_correction)

private theorem actual_zero_nonreal (j : ℕ) : (actualZero j).im ≠ 0 := by
  intro h
  have hh := actual_height_gt_ten (actualZero j)
    (actualData.zero_isNontrivial (actualOccurrenceEquiv j).1)
  rw [h, abs_zero] at hh
  norm_num at hh

/-- The complete tail has recurrent positive peaks of uniform normalized height. -/
private theorem normalized_positive_peaks {ρ : ℂ} (hρ : IsNontrivialZero ρ)
    (hβ : 1 / 2 < ρ.re) :
    ∃ W c : ℝ, 0 < W ∧ 0 < c ∧ ∀ᶠ T : ℝ in atTop,
      ∃ u ∈ Icc T (T + W), c < Real.exp ((1 - ρ.re) * u) * Q (Real.exp u) := by
  classical
  obtain ⟨j, hj⟩ := actual_occurrence_of_zero hρ
  obtain ⟨p, hpβ, hpγ⟩ : ∃ p : ℕ, (actualZero p).re = ρ.re ∧ 0 < (actualZero p).im := by
    rcases lt_or_gt_of_ne (actual_zero_nonreal j) with hneg | hpos
    · obtain ⟨k, hk⟩ := actual_conjugate_occurrence j
      exact ⟨k, by simp [hk, hj], by simpa [hk] using hneg⟩
    · exact ⟨j, congrArg Complex.re hj, hpos⟩
  let z := actualZero p
  let b : ℝ := (1 / 2 + z.re) / 2
  have hb : 1 / 2 < b := by dsimp [b, z]; linarith only [hpβ, hβ]
  have hbz : b < z.re := by dsimp [b, z]; linarith only [hpβ, hβ]
  obtain ⟨ν, hprob, hν, hfilter, hmoment⟩ :=
    exists_actual_high_zero_filter hb (H := 0) le_rfl p hpγ
  let _ : IsProbabilityMeasure ν := hprob
  have hkill (k : ℕ) (hk : b < (actualZero k).re) (hkp : actualZero k ≠ z)
      (hkc : actualZero k ≠ conj z) : expMoment ν (actualZero k - 1) = 0 := by
    rcases lt_or_gt_of_ne (actual_zero_nonreal k) with hneg | hpos
    · obtain ⟨l, hl⟩ := actual_conjugate_occurrence k
      have hbl : b < (actualZero l).re := by simpa [hl] using hk
      have hpl : 0 < (actualZero l).im := by simpa [hl] using hneg
      have hlne : actualZero l ≠ z := by
        intro he
        apply hkc
        simpa [hl] using congrArg (fun v : ℂ => conj v) he
      simpa [hl] using (hfilter l hbl hpl hlne).2
    · exact (hfilter k hk hpos hkp).1
  let h : ℝ := ∑' k : ℕ, if b < (actualZero k).re ∧ 0 < (actualZero k).im ∧
    actualZero k ≠ z then 2 * Real.pi / (actualZero k).im else 0
  have hνh : ν (Icc 0 h) = 1 := hν
  have hh : 0 ≤ h := by
    by_contra! hneg
    simp [Icc_eq_empty_of_lt hneg] at hνh
  let a := actualCoeff p * expMoment ν (z - 1)
  let C : ℝ := 2 * (analyticOrderNatAt riemannZeta z : ℝ) * ‖a‖
  let E : ℝ := (∑' k : ℕ, ‖actualCoeff k‖) + Real.log (2 * Real.pi)
  have hpair := actual_filtered_leading_pair ν p hνh (by linarith only [hb]) hbz hpγ hmoment hkill
  change a ≠ 0 ∧ 0 < C ∧ b - 1 < z.re - 1 ∧ 0 ≤ E ∧
    ∃ R : ℝ → ℝ, ∀ t : ℝ, Real.log 2 ≤ t →
      (∫ s : ℝ, Q (Real.exp (t + s)) ∂ν) =
        -(C * Real.exp ((z.re - 1) * t) * Real.cos (z.im * t + a.arg)) + R t ∧
      |R t| ≤ E * Real.exp ((b - 1) * t) at hpair
  obtain ⟨_, hC, _, _, R, hR⟩ := hpair
  have hlimit : Tendsto (fun t : ℝ => E * Real.exp ((b - z.re) * t)) atTop (𝓝 0) := by
    have hdecay := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (sub_neg.mpr hbz))
    simpa only [Function.comp_def, id_eq, mul_zero] using hdecay.const_mul E
  let P := 2 * Real.pi / z.im
  let W := P + h
  let c := C * Real.exp ((z.re - 1) * P) / 4
  have hP : 0 < P := div_pos Real.two_pi_pos hpγ
  have hnegative : z.re - 1 ≤ 0 := sub_nonpos.mpr
    (actualData.zero_isNontrivial (actualOccurrenceEquiv p).1).2.2.le
  obtain ⟨T₀, hsmall⟩ := eventually_atTop.mp (hlimit.eventually_lt_const (half_pos hC))
  refine ⟨W, c, add_pos_of_pos_of_nonneg hP hh, by dsimp [c]; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.log 2), eventually_ge_atTop T₀] with T hT hT₀
  have hA := (PositiveAverageCosineWindow.exists_signed_values
    (f := fun t => Q (Real.exp t)) (scale := fun t => Real.exp ((z.re - 1) * t))
    (start := T) (width := P) (support := h) (phase := a.arg + Real.pi)
    (lower := Real.exp ((z.re - 1) * (T + P)))
    hpγ le_rfl hC (Real.exp_pos _)
    (fun t ht => Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.2 hnegative)) (by
      intro t ht
      have hlog := hT.trans ht.1
      obtain ⟨hidentity, hbound⟩ := hR t hlog
      refine ⟨ν, hprob, hνh, q_integrable_average hνh hlog, ?_⟩
      rw [hidentity, ← add_assoc, Real.cos_add_pi, mul_neg, add_sub_cancel_left]
      refine hbound.trans ?_
      have hexp : Real.exp ((b - 1) * t) =
          Real.exp ((b - z.re) * t) * Real.exp ((z.re - 1) * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp, ← mul_assoc]
      exact (mul_le_mul_of_nonneg_right (hsmall t (hT₀.trans ht.1)).le
        (Real.exp_nonneg _)).trans_eq
        (by ring))).1
  obtain ⟨u, hu, hupeak⟩ := hA
  refine ⟨u, by simpa only [W, add_assoc] using hu, ?_⟩
  have hlevel : C * Real.exp ((z.re - 1) * (T + P)) / 4 =
      c * Real.exp ((z.re - 1) * T) := by
    rw [mul_add, Real.exp_add]
    dsimp only [c]
    ring
  rw [hlevel] at hupeak
  have hdecay : Real.exp ((z.re - 1) * u) ≤ Real.exp ((z.re - 1) * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hu.1 hnegative)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hscaled := mul_lt_mul_of_pos_left
    ((mul_le_mul_of_nonneg_left hdecay hc).trans_lt hupeak)
    (Real.exp_pos ((1 - z.re) * u))
  have hone : Real.exp ((1 - z.re) * u) * Real.exp ((z.re - 1) * u) = 1 := by
    rw [← Real.exp_add, show (1 - z.re) * u + (z.re - 1) * u = 0 by ring, Real.exp_zero]
  rw [mul_left_comm, hone, mul_one] at hscaled
  simpa only [z, hpβ] using hscaled

private theorem dirac_zero_support : (Measure.dirac (0 : ℝ)) (Icc 0 0) = 1 :=
  Measure.dirac_apply_of_mem (show (0 : ℝ) ∈ Icc 0 0 from ⟨le_rfl, le_rfl⟩)

private theorem unaveraged_formula {t : ℝ} (ht : Real.log 2 ≤ t) :
    Q (Real.exp t) = -(actualH t * (Real.exp (-t) : ℂ)).re +
      averagedActualCorrection (Measure.dirac 0) t := by
  have hf := actual_filtered_explicit_formula (Measure.dirac 0) dirac_zero_support ht
  have hm (k : ℕ) : expMoment (Measure.dirac 0) (actualZero k - 1) = 1 := by
    rw [expMoment, integral_dirac]
    change Complex.exp ((actualZero k - 1) * ((0 : ℝ) : ℂ)) = 1
    simp
  simp only [integral_dirac, add_zero, hm, mul_one] at hf
  rw [hf, actualH, ← tsum_mul_right]
  congr 3
  apply tsum_congr
  intro k
  rw [spectralExp, mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  simp only [Complex.ofReal_neg]
  ring

/-- At the abscissa scale the complete tail differs from the projected series by o(1). -/
private theorem normalized_complete_tail_approx {β : ℝ} (hβ : 0 < β)
    (hmax : ∀ k, (actualZero k).re ≤ β) :
    Tendsto (fun t : ℝ => Real.exp ((1 - β) * t) * Q (Real.exp t) +
      (maximalSeries actualCoeff actualZero β t).re) atTop (𝓝 0) := by
  let corr := averagedActualCorrection (Measure.dirac (0 : ℝ))
  have hexp (t : ℝ) : Real.exp ((1 - β) * t) * Real.exp (-t) = Real.exp (-β * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hproj := (Complex.continuous_re.tendsto 0).comp
    (tendsto_exp_mul_tsum_sub_maximalSeries actualCoeff_hasSum.summable.norm hmax)
  have hreal : Tendsto (fun t : ℝ => -((Real.exp (-β * t) : ℂ) * actualH t -
      maximalSeries actualCoeff actualZero β t).re) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.zero_re, neg_zero, actualH] using hproj.neg
  have hcorr : Tendsto (fun t : ℝ => Real.exp ((1 - β) * t) * corr t) atTop (𝓝 0) := by
    have hdecay := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hβ))
    have hbound : Tendsto (fun t : ℝ => -Real.log (2 * Real.pi) * Real.exp (-β * t))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, id_eq, mul_zero] using
        hdecay.const_mul (-Real.log (2 * Real.pi))
    have hbounds : ∀ᶠ t : ℝ in atTop, -Real.log (2 * Real.pi) * Real.exp (-β * t) ≤
        Real.exp ((1 - β) * t) * corr t ∧ Real.exp ((1 - β) * t) * corr t ≤ 0 := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      obtain ⟨hlower, hupper⟩ :=
        averagedActualCorrection_bounds (Measure.dirac 0) dirac_zero_support ht
      refine ⟨?_, mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) hupper⟩
      calc
        _ = Real.exp ((1 - β) * t) * -(Real.log (2 * Real.pi) * Real.exp (-t)) := by
          rw [← hexp t]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlower (Real.exp_nonneg _)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hbound tendsto_const_nhds
      (hbounds.mono fun _ ht => ht.1) (hbounds.mono fun _ ht => ht.2)
  refine (by simpa only [zero_add] using hreal.add hcorr :
    Tendsto (fun t : ℝ => -((Real.exp (-β * t) : ℂ) * actualH t -
      maximalSeries actualCoeff actualZero β t).re + Real.exp ((1 - β) * t) * corr t)
      atTop (𝓝 0)).congr' ?_
  filter_upwards [eventually_ge_atTop (Real.log 2)] with t ht
  rw [unaveraged_formula ht, Complex.sub_re, Complex.mul_re, Complex.mul_re]
  simp only [corr, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  rw [← hexp t]
  ring

/-- At any scale with exponent strictly above one half, removing prime powers changes
the normalized tail by a quantity that tends to zero. -/
private theorem normalized_prime_power_error {β : ℝ} (hβ : 1 / 2 < β) :
    Tendsto (fun t : ℝ => Real.exp ((1 - β) * t) * (Q (Real.exp t) - primeTail (Real.exp t)))
      atTop (𝓝 0) := by
  have hbase := prime_power_window_correction.1.comp Real.tendsto_exp_atTop
  have hdecay := Real.tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg (sub_neg.mpr hβ))
  have h := hdecay.mul hbase
  rw [zero_mul] at h
  refine h.congr' (Eventually.of_forall fun t => ?_)
  change Real.exp ((1 / 2 - β) * t) *
      (Real.sqrt (Real.exp t) * (Q (Real.exp t) - primeTail (Real.exp t))) = _
  have hsqrt : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  rw [hsqrt, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- A uniform modulus and a positive margin give a whole log interval at each late peak. -/
private theorem positive_prime_tail_log_windows {ρ : ℂ} (hρ : IsNontrivialZero ρ)
    (hβ : 1 / 2 < ρ.re) (hmax : ∀ z : ℂ, IsNontrivialZero z → z.re ≤ ρ.re) :
    ∃ W Δ : ℝ, 0 < W ∧ 0 < Δ ∧ ∀ᶠ T : ℝ in atTop,
      ∃ u ∈ Icc T (T + W), ∀ v ∈ Icc u (u + Δ), 0 < primeTail (Real.exp v) := by
  let F (t : ℝ) := Real.exp ((1 - ρ.re) * t) * primeTail (Real.exp t)
  let G (t : ℝ) := -(maximalSeries actualCoeff actualZero ρ.re t).re
  have hbound (k : ℕ) : (actualZero k).re ≤ ρ.re :=
    hmax _ (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)
  have hcomplete := normalized_complete_tail_approx (by linarith only [hβ]) hbound
  have herr := normalized_prime_power_error hβ
  have happrox : Tendsto (fun t => F t - G t) atTop (𝓝 0) := by
    have h := hcomplete.sub herr
    rw [sub_self] at h
    refine h.congr' (Eventually.of_forall fun t => ?_)
    dsimp only [F, G]
    ring
  have hG : UniformContinuous G :=
    (Complex.uniformContinuous_re.comp
      (uniformContinuous_maximalSeries actualCoeff_hasSum.summable.norm)).neg
  obtain ⟨W, c, hW, hc, hpeaks⟩ := normalized_positive_peaks hρ hβ
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hG (c / 4) (by positivity)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (by
    filter_upwards [hpeaks, (Metric.tendsto_nhds.mp happrox) (c / 8) (by positivity),
      (Metric.tendsto_nhds.mp herr) (c / 8) (by positivity)] with t hp ha he
    exact ⟨hp, by simpa only [Real.dist_eq, sub_zero] using ha,
      by simpa only [Real.dist_eq, sub_zero] using he⟩ :
    ∀ᶠ T in atTop,
      (∃ u ∈ Icc T (T + W), c < Real.exp ((1 - ρ.re) * u) * Q (Real.exp u)) ∧
      |F T - G T| < c / 8 ∧
      |Real.exp ((1 - ρ.re) * T) * (Q (Real.exp T) - primeTail (Real.exp T))| < c / 8)
  refine ⟨W, δ / 2, hW, half_pos hδ, ?_⟩
  filter_upwards [eventually_ge_atTop T₀] with T hT
  obtain ⟨u, hu, hpeak⟩ := (hT₀ T hT).1
  have hu₀ := hT.trans hu.1
  have hFu : 7 * c / 8 < F u := by
    have he := (abs_lt.mp (hT₀ u hu₀).2.2).2
    dsimp only [F]
    rw [mul_sub] at he
    linarith only [he, hpeak]
  refine ⟨u, hu, fun v hv => ?_⟩
  have hv₀ := hu₀.trans hv.1
  have huv : dist u v < δ := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hv.1)]
    linarith only [hv.2, hδ]
  have hGuv := hmod huv
  rw [Real.dist_eq] at hGuv
  have huclose := (abs_lt.mp (hT₀ u hu₀).2.1).2
  have hvclose := (abs_lt.mp (hT₀ v hv₀).2.1).1
  have hGstep := (abs_lt.mp hGuv).2
  have hF : 0 < F v := by linarith only [hc, hFu, huclose, hvclose, hGstep]
  exact pos_of_mul_pos_right hF (Real.exp_nonneg _)

/-- If an actual zero attains the maximal real part above one half, each sufficiently
late multiplicative range contains the start of a whole positive prime-tail window.
Its negative mass also vanishes on every narrower window from the same start. -/
theorem prime_tail_positive_short_windows_of_attained_zero (ρ : ℂ) (hρ : IsNontrivialZero ρ)
    (hβ : 1 / 2 < ρ.re) (hmax : ∀ z : ℂ, IsNontrivialZero z → z.re ≤ ρ.re) :
    ∃ κ₀ K X₀ : ℝ, 1 < κ₀ ∧ 1 ≤ K ∧ 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∃ A ∈ Icc X (K * X),
        (∀ x ∈ Icc A (κ₀ * A), 0 < primeTail x) ∧
        ∀ κ ∈ Icc 1 κ₀, (∫ x in A..κ * A, max (-primeTail x) 0 / Real.sqrt x) = 0 := by
  obtain ⟨W, Δ, hW, hΔ, hlogWindows⟩ := positive_prime_tail_log_windows hρ hβ hmax
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hlogWindows
  let T₁ := max T₀ (Real.log 2)
  refine ⟨Real.exp Δ, Real.exp W, Real.exp T₁, Real.one_lt_exp_iff.mpr hΔ,
    Real.one_le_exp hW.le, ?_, ?_⟩
  · rw [← Real.exp_log (show 0 < (2 : ℝ) by norm_num)]
    exact Real.exp_le_exp.mpr (le_max_right _ _)
  intro X hX
  have hXpos := (Real.exp_pos T₁).trans_le hX
  have hstart : T₀ ≤ Real.log X :=
    (le_max_left _ _).trans ((Real.le_log_iff_exp_le hXpos).2 hX)
  obtain ⟨u, hu, hwhole⟩ := hT₀ _ hstart
  have hA : Real.exp u ∈ Icc X (Real.exp W * X) := by
    refine ⟨?_, ?_⟩
    · rw [← Real.exp_log hXpos]
      exact Real.exp_le_exp.mpr hu.1
    · simpa only [Real.exp_add, Real.exp_log hXpos, mul_comm] using Real.exp_le_exp.mpr hu.2
  have hpos (x : ℝ) (hx : x ∈ Icc (Real.exp u) (Real.exp Δ * Real.exp u)) :
      0 < primeTail x := by
    have hx₀ := (Real.exp_pos u).trans_le hx.1
    have hlog : Real.log x ∈ Icc u (u + Δ) := by
      refine ⟨(Real.le_log_iff_exp_le hx₀).2 hx.1, (Real.log_le_iff_le_exp hx₀).2 ?_⟩
      simpa only [Real.exp_add, mul_comm] using hx.2
    simpa only [Real.exp_log hx₀] using hwhole (Real.log x) hlog
  refine ⟨Real.exp u, hA, hpos, ?_⟩
  intro κ hκ
  have horder : Real.exp u ≤ κ * Real.exp u :=
    le_mul_of_one_le_left (Real.exp_nonneg _) hκ.1
  have hsub : Icc (Real.exp u) (κ * Real.exp u) ⊆
      Icc (Real.exp u) (Real.exp Δ * Real.exp u) :=
    Icc_subset_Icc le_rfl (mul_le_mul_of_nonneg_right hκ.2 (Real.exp_nonneg _))
  calc
    _ = ∫ _ in Real.exp u..κ * Real.exp u, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le horder]
      intro x hx
      change max (-primeTail x) 0 / Real.sqrt x = 0
      rw [max_eq_right (neg_nonpos.mpr (hpos x (hsub hx)).le), zero_div]
    _ = 0 := intervalIntegral.integral_zero

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedShortWindows
