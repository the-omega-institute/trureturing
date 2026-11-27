/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedRootTransfer
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedRootTransfer
   mirror-E: none(waiver:analytic-integral-transport)
   anchors: []
   utility: none
   digest: Exact weighted power integral with two-sided bounds for its logarithmic correction. -/

import D5.S3.Analytic.ExponentialSum.TwoScaleEndpointMoments
import D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedZeroLaplace

/-! Explicit logarithmic corrections to the power main terms of the Robin weight. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedZeroLaplace

namespace D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedRootTransfer

/-- Exact integration of the logarithmic weight multiplied by its own
decaying exponential. The index need only be positive. -/
private theorem integral_exp_mul_H_same {a u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    (∫ v in Ioi u, Real.exp (-a * v) * H a v) = Real.exp (-a * u) / u := by
  have hInt : IntegrableOn (fun v => Real.exp (-a * v) * H a v) (Ioi u) := by
    apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) u).mul_const (H a u)).mono'
    · exact (show ContinuousOn (fun v => Real.exp (-a * v) * H a v) (Ioi u) by
        intro v hv
        have hv0 := hu.trans hv
        unfold H
        fun_prop (disch := positivity)).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (Real.exp_nonneg _) (H_nonneg ha.le (hu.trans hv)))]
      exact mul_le_mul_of_nonneg_left (H_antitone ha.le hu hv.le) (Real.exp_nonneg _)
  have hDeriv (v : ℝ) (hv : 0 < v) :
      HasDerivAt (fun t => -(Real.exp (-a * t) / t))
        (Real.exp (-a * v) * H a v) v := by
    have h := ((((hasDerivAt_id v).const_mul (-a)).exp).div
      (hasDerivAt_id v) hv.ne').neg
    convert h using 1
    · ext t; simp
    · simp only [id_eq]
      unfold H
      field_simp [hv.ne'] <;> ring
  have hEnd : Filter.Tendsto (fun t => -(Real.exp (-a * t) / t))
      Filter.atTop (nhds 0) := by
    have he : Filter.Tendsto (fun t : ℝ => Real.exp (-a * t)) Filter.atTop (nhds 0) := by
      apply Real.tendsto_exp_atBot.comp
      exact Filter.tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos ha)
    have hi : Filter.Tendsto (fun t : ℝ => t⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv] using (he.mul hi).neg
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun v hv => hDeriv v (hu.trans_le hv)) hInt hEnd

/-- The exact power main term for a weighted Chebyshev root. The correction
multiplies a positive integral by the signed coefficient `-r / (j - r)`. -/
theorem power_main_eq {j r u : ℝ} (hr : r < j) (hu : 0 < u) :
    (∫ v in Ioi u, Real.exp ((r - j) * v) * H j v) =
      (j / (j - r)) * (Real.exp ((r - j) * u) / u) -
        (r / (j - r)) * (∫ v in Ioi u, Real.exp ((r - j) * v) / v ^ 2) := by
  let a := j - r
  have ha : 0 < a := sub_pos.mpr hr
  have hA : r - j = -a := by simp [a]
  rw [hA]
  have hI (k : ℝ) (hk : 0 ≤ k) :
      IntegrableOn (fun v => Real.exp (-a * v) * H k v) (Ioi u) := by
    apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) u).mul_const (H k u)).mono'
    · exact (show ContinuousOn (fun v => Real.exp (-a * v) * H k v) (Ioi u) by
        intro v hv
        have hv0 := hu.trans hv
        unfold H
        fun_prop (disch := positivity)).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (Real.exp_nonneg _) (H_nonneg hk (hu.trans hv)))]
      exact mul_le_mul_of_nonneg_left (H_antitone hk hu hv.le) (Real.exp_nonneg _)
  have hF : IntegrableOn (fun v => Real.exp (-a * v) / v ^ 2) (Ioi u) := by
    simpa only [H, zero_div, zero_add, mul_one_div] using hI 0 le_rfl
  have hSplit : (∫ v in Ioi u, Real.exp (-a * v) * H j v) =
      (∫ v in Ioi u, (j / a) * (Real.exp (-a * v) * H a v) -
        (r / a) * (Real.exp (-a * v) / v ^ 2)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    have hv0 := hu.trans hv
    unfold H
    field_simp [ha.ne', hv0.ne']
    dsimp [a]
    ring
  rw [hSplit, integral_sub ((hI a ha.le).const_mul _) (hF.const_mul _),
    integral_const_mul, integral_const_mul, integral_exp_mul_H_same ha hu]

open Filter
open scoped Topology

/-- Two-sided bounds for the inverse-square correction in the power main term. -/
theorem exponential_inverse_square_tail_bounds {a u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    Real.exp (-a * u) / (a * (u + 1 / a) ^ 2) ≤
      (∫ v in Ioi u, Real.exp (-a * v) / v ^ 2) ∧
    (∫ v in Ioi u, Real.exp (-a * v) / v ^ 2) ≤
      Real.exp (-a * u) / (a * u ^ 2) := by
  let m := u + 1 / a
  have hm : 0 < m := add_pos hu (one_div_pos.mpr ha)
  have hExp := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) u
  have hMass : (∫ v in Ioi u, Real.exp (-a * v)) = Real.exp (-a * u) / a := by
    rw [integral_exp_mul_Ioi (neg_lt_zero.mpr ha), neg_div_neg_eq]
  have hPointUpper (v : ℝ) (hv : v ∈ Ioi u) :
      Real.exp (-a * v) / v ^ 2 ≤ Real.exp (-a * v) * (1 / u ^ 2) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (Real.exp_nonneg _) (pow_pos hu 2)
      (pow_le_pow_left₀ hu.le hv.le 2)
  have hMajorant := hExp.mul_const (1 / u ^ 2)
  have hCorrection : IntegrableOn (fun v => Real.exp (-a * v) / v ^ 2) (Ioi u) := by
    apply hMajorant.mono'
    · exact (show ContinuousOn (fun v => Real.exp (-a * v) / v ^ 2) (Ioi u) by
        intro v hv
        have hv0 : 0 < v := hu.trans hv
        fun_prop (disch := positivity)).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_nonneg _) (sq_nonneg v))]
      exact hPointUpper v hv
  have hFirstOnPositive :
      IntegrableOn (fun v : ℝ => v * Real.exp (-a * v)) (Ioi 0) := by
    simpa only [pow_one, neg_mul] using (TwoScaleEndpointMoments.exponential_moment a ha 1).1
  have hFirst := hFirstOnPositive.mono_set (Ioi_subset_Ioi hu.le)
  have hCentered : IntegrableOn (fun v => (v - m) * Real.exp (-a * v)) (Ioi u) := by
    simp only [sub_mul]
    exact hFirst.sub' (hExp.const_mul m)
  have hCenteredIntegral : (∫ v in Ioi u, (v - m) * Real.exp (-a * v)) = 0 := by
    let primitive (v : ℝ) : ℝ := (v - u) * Real.exp (-a * v) / (-a)
    have hDeriv (v : ℝ) : HasDerivAt primitive ((v - m) * Real.exp (-a * v)) v := by
      have h := (((hasDerivAt_id' v).sub_const u).mul
        (((hasDerivAt_id' v).const_mul (-a)).exp)).div_const (-a)
      change HasDerivAt primitive _ v at h
      apply h.congr_deriv
      dsimp only [m]
      field_simp [ha.ne'] <;> ring
    have hExpLimit : Tendsto (fun v : ℝ => Real.exp (-a * v)) atTop (𝓝 0) := by
      simpa only [Real.rpow_zero, one_mul] using
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 a ha
    have hFirstLimit : Tendsto (fun v : ℝ => v * Real.exp (-a * v)) atTop (𝓝 0) := by
      simpa only [Real.rpow_one] using
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha
    have hEnd : Tendsto primitive atTop (𝓝 0) := by
      simpa only [primitive, sub_mul, mul_zero, sub_zero, zero_div] using
        (hFirstLimit.sub (hExpLimit.const_mul u)).div_const (-a)
    simpa only [primitive, sub_self, zero_mul, zero_div, sub_zero] using
      integral_Ioi_of_hasDerivAt_of_tendsto' (fun v _ => hDeriv v) hCentered hEnd
  have hConstantTerm := hExp.const_mul (1 / m ^ 2)
  have hLinearTerm := hCentered.const_mul (2 / m ^ 3)
  constructor
  · calc
      _ = (1 / m ^ 2) * (Real.exp (-a * u) / a) := by
        dsimp only [m]
        rw [div_mul_eq_div_div] <;> ring
      _ = ∫ v in Ioi u,
          (1 / m ^ 2) * Real.exp (-a * v) - (2 / m ^ 3) * ((v - m) * Real.exp (-a * v)) := by
        rw [integral_sub hConstantTerm hLinearTerm, integral_const_mul, integral_const_mul,
          hMass, hCenteredIntegral, mul_zero, sub_zero]
      _ ≤ _ := by
        apply setIntegral_mono_on (hConstantTerm.sub' hLinearTerm) hCorrection measurableSet_Ioi
        intro v hv
        have hv0 : 0 < v := hu.trans hv
        have hGap :
            1 / v ^ 2 - (1 / m ^ 2 - (2 / m ^ 3) * (v - m)) =
              (v - m) ^ 2 * (2 * v + m) / (m ^ 3 * v ^ 2) := by
          field_simp [hm.ne', hv0.ne'] <;> ring
        have hTangent : 1 / m ^ 2 - (2 / m ^ 3) * (v - m) ≤ 1 / v ^ 2 := by
          apply sub_nonneg.mp
          rw [hGap]
          positivity
        calc
          _ = (1 / m ^ 2 - (2 / m ^ 3) * (v - m)) * Real.exp (-a * v) := by ring
          _ ≤ (1 / v ^ 2) * Real.exp (-a * v) :=
            mul_le_mul_of_nonneg_right hTangent (Real.exp_nonneg _)
          _ = _ := by ring
  · calc
      _ ≤ ∫ v in Ioi u, Real.exp (-a * v) * (1 / u ^ 2) :=
        setIntegral_mono_on hCorrection hMajorant measurableSet_Ioi hPointUpper
      _ = _ := by
        rw [integral_mul_const, hMass, mul_one_div, div_mul_eq_div_div]

/-- The square-root main term at weight index one, with the correction
retained on both sides. -/
theorem square_root_power_main_bounds {u : ℝ} (hu : 0 < u) :
    2 * (Real.exp (-(1 / 2 : ℝ) * u) / u) -
        2 * Real.exp (-(1 / 2 : ℝ) * u) / u ^ 2 ≤
      (∫ v in Ioi u, Real.exp (-(1 / 2 : ℝ) * v) * H 1 v) ∧
    (∫ v in Ioi u, Real.exp (-(1 / 2 : ℝ) * v) * H 1 v) ≤
      2 * (Real.exp (-(1 / 2 : ℝ) * u) / u) -
        2 * Real.exp (-(1 / 2 : ℝ) * u) / (u + 2) ^ 2 := by
  have hMain := power_main_eq (j := 1) (r := 1 / 2) (by norm_num) hu
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num,
    show (1 : ℝ) / (1 - 1 / 2) = 2 by norm_num,
    show (1 / 2 : ℝ) / (1 - 1 / 2) = 1 by norm_num, one_mul] at hMain
  obtain ⟨hLower, hUpper⟩ :=
    exponential_inverse_square_tail_bounds (a := 1 / 2) (by norm_num) hu
  rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num] at hLower
  have hHalf (t : ℝ) :
      Real.exp (-(1 / 2 : ℝ) * u) / ((1 / 2 : ℝ) * t ^ 2) =
        2 * Real.exp (-(1 / 2 : ℝ) * u) / t ^ 2 := by
    rw [div_mul_eq_div_div, div_div_eq_mul_div, div_one, mul_comm (2 : ℝ)]
  rw [hHalf] at hLower hUpper
  rw [hMain]
  exact ⟨sub_le_sub_left hUpper _, sub_le_sub_left hLower _⟩

end D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedRootTransfer
