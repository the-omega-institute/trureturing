/- GID: D5/S1/Scale/Units
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every golden integer unit is a signed integral power of phi. -/

import D5.S1.Scale.Log

namespace D5.S1.Scale

open D5.S0.Carrier

private theorem abs_embedding_bounds_of_logScale_zero {x : GoldenInt}
    (hx : x ≠ 0) (hscale : logScale x = some 0) :
    1 ≤ |embedding x| ∧ |embedding x| < Real.goldenRatio := by
  rw [logScale_ne_zero hx] at hscale
  have hfloor : ⌊Real.logb Real.goldenRatio |embedding x|⌋ = 0 :=
    Option.some.inj hscale
  have hlogb := Int.floor_eq_iff.mp hfloor
  simp only [Int.cast_zero, zero_add] at hlogb
  have habs_pos : 0 < |embedding x| := by
    apply abs_pos.mpr
    exact (embedding_eq_zero_iff x).not.mpr hx
  have hlog_golden_pos : 0 < Real.log Real.goldenRatio :=
    Real.log_pos Real.one_lt_goldenRatio
  have hlog_nonneg : 0 ≤ Real.log |embedding x| := by
    have h := (le_div_iff₀ hlog_golden_pos).mp (by
      simpa [Real.logb] using hlogb.1)
    simpa using h
  have hlog_lt : Real.log |embedding x| < Real.log Real.goldenRatio := by
    have h := (div_lt_iff₀ hlog_golden_pos).mp (by
      simpa [Real.logb] using hlogb.2)
    simpa using h
  constructor
  · apply (Real.strictMonoOn_log.le_iff_le (by norm_num) habs_pos).mp
    simpa using hlog_nonneg
  · exact (Real.strictMonoOn_log.lt_iff_lt habs_pos Real.goldenRatio_pos).mp hlog_lt

private theorem reduced_unit_eq_one_or_neg_one (x : GoldenInt)
    (hnorm : norm x = 1 ∨ norm x = -1)
    (hone : 1 ≤ |embedding x|)
    (hphi : |embedding x| < Real.goldenRatio) :
    x = 1 ∨ x = -1 := by
  have hnorm_abs : |(norm x : ℝ)| = 1 := by
    rcases hnorm with hnorm | hnorm <;> rw [hnorm] <;> norm_num
  have hproduct := abs_embedding_mul_abs_conj x
  rw [hnorm_abs] at hproduct
  have hconj : |embedding (conj x)| ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hone) (abs_nonneg (embedding (conj x)))]
  have hembedding_lt_two : |embedding x| < 2 :=
    hphi.trans Real.goldenRatio_lt_two
  have houtside : 1 ≤ embedding x ∨ 1 ≤ -embedding x := le_abs.mp hone
  have hphi_bounds :
      -Real.goldenRatio < embedding x ∧ embedding x < Real.goldenRatio :=
    abs_lt.mp hphi
  have hx_bounds : -2 < embedding x ∧ embedding x < 2 :=
    abs_lt.mp hembedding_lt_two
  have hconj_bounds : -1 ≤ embedding (conj x) ∧ embedding (conj x) ≤ 1 :=
    abs_le.mp hconj
  have htrace :
      embedding x + embedding (conj x) = ((2 * x.a + x.b : ℤ) : ℝ) := by
    simp [embedding_apply, conj]
    ring
  have hdiff :
      embedding x - embedding (conj x) =
        (x.b : ℝ) * (2 * Real.goldenRatio - 1) := by
    simp [embedding_apply, conj]
    ring
  have htrace_lower_real : (-3 : ℝ) < ((2 * x.a + x.b : ℤ) : ℝ) := by
    rw [← htrace]
    linarith
  have htrace_upper_real : ((2 * x.a + x.b : ℤ) : ℝ) < 3 := by
    rw [← htrace]
    linarith
  have htrace_lower : (-3 : ℤ) < 2 * x.a + x.b := by
    exact_mod_cast htrace_lower_real
  have htrace_upper : 2 * x.a + x.b < (3 : ℤ) := by
    exact_mod_cast htrace_upper_real
  have hfactor : (1 : ℝ) < 2 * Real.goldenRatio - 1 := by
    linarith [Real.one_lt_goldenRatio]
  have hdiff_lower : (-3 : ℝ) < embedding x - embedding (conj x) := by
    linarith
  have hdiff_upper : embedding x - embedding (conj x) < 3 := by
    linarith
  have hb_lower_real : (-3 : ℝ) < (x.b : ℝ) := by
    by_contra hb
    have hb' : (x.b : ℝ) ≤ -3 := le_of_not_gt hb
    have hmul :
        (x.b : ℝ) * (2 * Real.goldenRatio - 1) ≤
          -3 * (2 * Real.goldenRatio - 1) :=
      mul_le_mul_of_nonneg_right hb' (le_of_lt (by linarith))
    rw [hdiff] at hdiff_lower
    nlinarith
  have hb_upper_real : (x.b : ℝ) < 3 := by
    by_contra hb
    have hb' : (3 : ℝ) ≤ (x.b : ℝ) := le_of_not_gt hb
    have hmul :
        3 * (2 * Real.goldenRatio - 1) ≤
          (x.b : ℝ) * (2 * Real.goldenRatio - 1) :=
      mul_le_mul_of_nonneg_right hb' (le_of_lt (by linarith))
    rw [hdiff] at hdiff_upper
    nlinarith
  have hb_lower : (-3 : ℤ) < x.b := by exact_mod_cast hb_lower_real
  have hb_upper : x.b < (3 : ℤ) := by exact_mod_cast hb_upper_real
  have ha_lower : (-3 : ℤ) < x.a := by omega
  have ha_upper : x.a < (3 : ℤ) := by omega
  rcases x with ⟨a, b⟩
  simp only at ha_lower ha_upper hb_lower hb_upper hnorm ⊢
  interval_cases a <;> interval_cases b
  all_goals norm_num [D5.S0.Carrier.norm] at hnorm
  all_goals rcases houtside with houtside | houtside
  all_goals norm_num [embedding_apply] at houtside
  all_goals norm_num [embedding_apply] at hphi_bounds
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | nlinarith [Real.one_lt_goldenRatio, Real.goldenRatio_lt_two]

private theorem phiUnitZPowMul_neg_cancel (n : ℤ) (x : GoldenInt) :
    phiUnitZPowMul n (phiUnitZPowMul (-n) x) = x := by
  simp [phiUnitZPowMul]

/-- The units of the golden integer ring are exactly the signed integral powers of `phi`. -/
theorem golden_units_eq_signed_phi_pow (x : GoldenInt) :
    IsUnit x ↔ ∃ (s : Bool) (n : ℤ), x = signedPhiPower s n := by
  constructor
  · intro hx
    have hx_norm := (isUnit_iff_norm_eq_one_or_neg_one x).mp hx
    have hx_ne : x ≠ 0 := by
      intro hzero
      subst x
      norm_num at hx_norm
    let k : ℤ := ⌊Real.logb Real.goldenRatio |embedding x|⌋
    let y : GoldenInt := phiUnitZPowMul (-k) x
    have hy_ne : y ≠ 0 := phiUnitZPowMul_ne_zero (-k) hx_ne
    have hlog_x : logScale x = some k := logScale_ne_zero hx_ne
    have hlog_y : logScale y = some 0 := by
      calc
        logScale y = (logScale x).map (-k + ·) :=
          logScale_phiUnit_zpow_mul (-k) hx_ne
        _ = some 0 := by simp [hlog_x]
    have hy_bounds := abs_embedding_bounds_of_logScale_zero hy_ne hlog_y
    have hy_unit : IsUnit y := by
      exact (phiUnit ^ (-k)).isUnit.mul hx
    have hy_norm := (isUnit_iff_norm_eq_one_or_neg_one y).mp hy_unit
    rcases reduced_unit_eq_one_or_neg_one y hy_norm hy_bounds.1 hy_bounds.2 with hy | hy
    · refine ⟨false, k, ?_⟩
      calc
        x = phiUnitZPowMul k y := by
          rw [← phiUnitZPowMul_neg_cancel k x]
        _ = signedPhiPower false k := by simp [hy, phiUnitZPowMul, signedPhiPower]
    · refine ⟨true, k, ?_⟩
      calc
        x = phiUnitZPowMul k y := by
          rw [← phiUnitZPowMul_neg_cancel k x]
        _ = signedPhiPower true k := by simp [hy, phiUnitZPowMul, signedPhiPower]
  · rintro ⟨s, n, rfl⟩
    exact signedPhiPower_isUnit s n

end D5.S1.Scale
