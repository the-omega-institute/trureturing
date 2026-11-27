/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtPointwiseWindows
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/MangoldtPointwiseWindows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One-sided Mangoldt bounds on arbitrarily late power windows characterize RH. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth
import D5.S3.Weil.Mertens.ZeroAbscissaPower

/-! # Pointwise windows for the complete Mangoldt remainder

The prime-only pole criterion supplies the converse from one-sided control throughout
arbitrarily late intervals. The forward direction uses the absolute RH envelope. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter MeasureTheory Set Real
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q U)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (firstLiMass firstLiMass_lt_third)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtPointwiseWindows

private lemma eventual_correction :
    ∀ᶠ x : ℝ in atTop, Real.sqrt x * (Q x - primeTail x) ≤ 3 :=
  (PrimeOnlyTailCorrection.prime_power_window_correction.1.eventually_lt_const
    (by norm_num : (2 : ℝ) < 3)).mono fun _ h => h.le

private lemma scaled_neg_tail {x κ : ℝ} (hx : 2 ≤ x)
    (hgap : Real.sqrt x * (Q x - primeTail x) ≤ 3)
    (hU : U x ≤ x ^ ((1 : ℝ) / 2 + κ)) :
    Real.sqrt x * (-primeTail x) ≤ x ^ κ + 3 := by
  have hx0 : 0 < x := by linarith
  have hs := Real.sqrt_pos.mpr hx0
  rw [Real.rpow_add hx0, ← Real.sqrt_eq_rpow] at hU
  have h := (div_le_iff₀ hs).mpr (hU.trans_eq (mul_comm ..))
  have he : Real.sqrt x * (-Q x) = U x / Real.sqrt x := by
    rw [← D5.S3.Weil.Mertens.ZeroAbscissaPower.primitive_eq_negative_tail hx]
    field_simp [hs.ne', hx0.ne']
    nlinarith [congrArg (U x * ·) (Real.sq_sqrt hx0.le)]
  linarith only [hgap, he, h, mul_sub (Real.sqrt x) (Q x) (primeTail x),
    mul_neg (Real.sqrt x) (Q x), mul_neg (Real.sqrt x) (primeTail x)]

/-- Once the prime-power correction is at most three, any full interval of pointwise
Mangoldt bounds contributes at most four times the endpoint power times its log length. -/
private lemma window_bound {a z κ : ℝ} (ha : 2 ≤ a) (haz : a ≤ z) (hκ : 0 ≤ κ)
    (hgap : ∀ x ≥ a, Real.sqrt x * (Q x - primeTail x) ≤ 3)
    (hU : ∀ x ∈ Icc a z, U x ≤ x ^ ((1 : ℝ) / 2 + κ)) :
    (∫ x in a..z, max (-primeTail x) 0 / Real.sqrt x) ≤ 4 * z ^ κ * Real.log (z / a) := by
  have ha1 : 1 ≤ a := by linarith
  have hp (t : ℝ) (ht : t ∈ uIcc a z) : 0 < t :=
    zero_lt_one.trans_le (ha1.trans ((uIcc_of_le haz) ▸ ht).1)
  have hzi : 1 ≤ z ^ κ := Real.one_le_rpow (ha1.trans haz) hκ
  have hi : IntervalIntegrable (fun x : ℝ => (4 * z ^ κ) * x⁻¹) volume a z :=
    (continuousOn_const.mul (continuousOn_id.inv₀ fun t ht => (hp t ht).ne')).intervalIntegrable
  calc
    _ ≤ ∫ x in a..z, (4 * z ^ κ) * x⁻¹ := by
      rw [intervalIntegral.integral_of_le haz, intervalIntegral.integral_of_le haz]
      apply integral_mono_of_nonneg
        (ae_of_all _ fun x => div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)) hi.1
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
      have ht0 := zero_lt_one.trans_le (ha1.trans ht.1.le)
      have hs := Real.sqrt_pos.mpr ht0
      have hd := scaled_neg_tail (ha.trans ht.1.le) (hgap t ht.1.le) (hU t ⟨ht.1.le, ht.2⟩)
      have hpow := Real.rpow_le_rpow ht0.le ht.2 hκ
      rw [← div_eq_mul_inv, div_le_div_iff₀ hs ht0]
      conv_lhs => arg 2; rw [← Real.sq_sqrt ht0.le, sq]
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ hs.le
      rw [max_mul_of_nonneg _ _ hs.le, zero_mul, mul_comm (-primeTail t)]
      exact max_le (by linarith) (by linarith)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_inv (fun h => (hp 0 h).false)]

/-- Convert a pointwise window into the prime-only mass used in the pole criterion. -/
private lemma rh_of_pointwise_windows {b : ℝ} (hb : 1 < b)
    (windows : ∀ κ : ℝ, 0 < κ → ∃ᶠ Y : ℝ in atTop,
      ∀ x ∈ Icc Y (Y ^ b), U x ≤ x ^ ((1 : ℝ) / 2 + κ)) : RiemannHypothesis := by
  apply (PrimeWindowPoleGrowth.rh_iff_frequently_small_prime_windows hb).2
  intro η hη
  have hb0 := zero_lt_one.trans hb
  let κ := η / (2 * b)
  have hκ : 0 < κ := div_pos hη (by positivity)
  have hbκ : b * κ = η / 2 := by dsimp [κ]; field_simp
  obtain ⟨T, hT⟩ := eventually_atTop.mp eventual_correction
  have hc : 0 < (4 * (b - 1))⁻¹ := inv_pos.mpr (mul_pos (by norm_num) (sub_pos.mpr hb))
  have hlog := (isLittleO_log_rpow_atTop (half_pos hη)).bound hc
  apply ((windows κ hκ).and_eventually ((eventually_ge_atTop (max T 2)).and hlog)).mono
  rintro Y ⟨hw, hY, hl⟩
  have hY2 := (le_max_right T (2 : ℝ)).trans hY
  have hY1 : 1 ≤ Y := by linarith
  have hY0 := zero_lt_one.trans_le hY1
  have hYY : Y ≤ Y ^ b := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hY1 hb.le
  have hfin := window_bound hY2 hYY hκ.le
    (fun x hx => hT x ((le_max_left _ _).trans (hY.trans hx))) hw
  rw [← Real.rpow_mul hY0.le, hbκ, Real.log_div (Real.rpow_pos_of_pos hY0 _).ne' hY0.ne',
    Real.log_rpow hY0] at hfin
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hY1),
    abs_of_pos (Real.rpow_pos_of_pos hY0 (η / 2))] at hl
  have hscale : 4 * (b - 1) * Real.log Y ≤ Y ^ (η / 2) := by
    rwa [← div_eq_inv_mul, le_div_iff₀ (inv_pos.mp hc), mul_comm] at hl
  calc
    _ ≤ _ := hfin
    _ = Y ^ (η / 2) * (4 * (b - 1) * Real.log Y) := by ring
    _ ≤ Y ^ (η / 2) * Y ^ (η / 2) :=
      mul_le_mul_of_nonneg_left hscale (Real.rpow_nonneg hY0.le _)
    _ = _ := by rw [← Real.rpow_add hY0]; congr 1; ring

private theorem sqrt_windows_of_rh {C b : ℝ} (hC : firstLiMass < C) (rh : RiemannHypothesis) :
    ∀ R : ℝ, ∃ Y ≥ max R 2, ∀ x ∈ Icc Y (Y ^ b), U x ≤ C * Real.sqrt x := by
  have he := Real.tendsto_log_atTop.eventually ((RHSharpActualEnvelope.actual_G_control rh).1
    (C - firstLiMass) (sub_pos.mpr hC))
  obtain ⟨T, ht⟩ := eventually_atTop.mp he
  intro R
  refine ⟨max (max R 2) T, le_max_left _ _, ?_⟩
  intro x hx
  have h := ht x ((le_max_right _ _).trans hx.1)
  have hx0 : 0 < x := by
    linarith only [((le_max_right R (2 : ℝ)).trans (le_max_left _ _)).trans hx.1]
  change |exp (-log x / 2) * _| < firstLiMass + (C - firstLiMass) at h
  rw [exp_log hx0, abs_mul, abs_of_pos (exp_pos _), add_sub_cancel _ _] at h
  have hinv : exp (-log x / 2) = (Real.sqrt x)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0, ← exp_neg]
    congr 1
    ring
  rw [hinv, ← div_eq_inv_mul] at h
  exact (le_abs_self _).trans ((div_le_iff₀ (Real.sqrt_pos.mpr hx0)).mp h.le)

private theorem power_windows_of_sqrt {C b : ℝ}
    (h : ∀ R : ℝ, ∃ Y ≥ max R 2, ∀ x ∈ Icc Y (Y ^ b), U x ≤ C * Real.sqrt x) :
    ∀ κ : ℝ, 0 < κ → ∃ᶠ Y : ℝ in atTop,
      ∀ x ∈ Icc Y (Y ^ b), U x ≤ x ^ ((1 : ℝ) / 2 + κ) := by
  intro κ hk
  apply frequently_atTop.mpr
  intro R
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((tendsto_rpow_atTop hk).eventually_ge_atTop C)
  obtain ⟨Y, hY, H⟩ := h (max R T)
  have hYR := (le_max_left _ _).trans hY
  refine ⟨Y, (le_max_left _ _).trans hYR, ?_⟩
  intro x hx
  have hx0 : 0 < x := by linarith only [((le_max_right _ _).trans hY).trans hx.1]
  apply (H x hx).trans
  rw [Real.rpow_add hx0, ← Real.sqrt_eq_rpow, mul_comm]
  exact mul_le_mul_of_nonneg_left (hT x ((le_max_right _ _).trans (hYR.trans hx.1)))
    (Real.sqrt_nonneg _)

/-- Arbitrarily small power losses suffice in a one-sided bound on arbitrarily late windows. -/
theorem rh_iff_pointwise_power_windows {b : ℝ} (hb : 1 < b) :
    RiemannHypothesis ↔ ∀ κ : ℝ, 0 < κ → ∃ᶠ Y : ℝ in atTop,
      ∀ x ∈ Icc Y (Y ^ b), U x ≤ x ^ ((1 : ℝ) / 2 + κ) :=
  ⟨fun rh => power_windows_of_sqrt (sqrt_windows_of_rh firstLiMass_lt_third rh),
    rh_of_pointwise_windows hb⟩

/-- A fixed coefficient strictly larger than the first Li mass suffices at the square-root scale. -/
theorem rh_iff_pointwise_sqrt_windows {C b : ℝ} (hC : firstLiMass < C) (hb : 1 < b) :
    RiemannHypothesis ↔ ∀ R : ℝ, ∃ Y ≥ max R 2,
      ∀ x ∈ Icc Y (Y ^ b), U x ≤ C * Real.sqrt x :=
  ⟨sqrt_windows_of_rh hC, fun h => rh_of_pointwise_windows hb (power_windows_of_sqrt h)⟩

end D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtPointwiseWindows
