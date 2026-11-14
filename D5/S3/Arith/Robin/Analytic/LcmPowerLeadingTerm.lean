/- GID: D5/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The leading coefficient of the LCM power function at large exponents. -/

import D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen
import D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCoefficient
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Topology
open D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen
open D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCoefficient

namespace D5.S3.Arith.Robin.Analytic.LcmPowerLeadingTerm

def normalizedF (κ x t : ℝ) : ℝ :=
  Real.log (((x - t) ^ κ - (1 - t) ^ κ) /
    ((x - x * t) ^ κ - (1 - x * t) ^ κ)) / (κ * Real.log x)

private lemma normalizedF_zero {κ x : ℝ} (hκ : 1 < κ) (hx : 1 < x) :
    normalizedF κ x 0 = 0 := by
  have hxk : 1 < x ^ κ := Real.one_lt_rpow hx (by linarith)
  simp [normalizedF, (sub_pos.mpr hxk).ne']

private lemma normalizedF_derivative {κ x : ℝ} (hκ : 1 < κ) (hx : 1 < x) :
    HasDerivAt (normalizedF κ x) (coefficient κ x) 0 := by
  have hx0 : 0 < x := by linarith
  have hκ0 : κ ≠ 0 := by linarith
  have hxk : 1 < x ^ κ := Real.one_lt_rpow hx (by linarith)
  have hk : x ^ κ - 1 ≠ 0 := (sub_pos.mpr hxk).ne'
  have hn := (((hasDerivAt_const (0 : ℝ) x).sub (hasDerivAt_id 0)).rpow_const
      (p := κ) (Or.inl (by simpa using hx0.ne'))).sub
    (((hasDerivAt_const (0 : ℝ) 1).sub (hasDerivAt_id 0)).rpow_const
      (p := κ) (Or.inl (by norm_num)))
  have hd := (((hasDerivAt_const (0 : ℝ) x).sub ((hasDerivAt_id 0).const_mul x)).rpow_const
      (p := κ) (Or.inl (by simpa using hx0.ne'))).sub
    (((hasDerivAt_const (0 : ℝ) 1).sub ((hasDerivAt_id 0).const_mul x)).rpow_const
      (p := κ) (Or.inl (by norm_num)))
  simp only [Pi.sub_apply, id_eq, sub_zero, mul_zero, Real.one_rpow] at hn hd
  have h := ((hn.div hd (by simpa using hk)).log
    (by simpa [hk] using (one_ne_zero : (1 : ℝ) ≠ 0))).div_const (κ * Real.log x)
  convert h using 1
  · rfl
  · simp only [Pi.sub_apply, Pi.div_apply, id_eq, sub_zero, mul_zero, Real.one_rpow,
      zero_sub, one_mul, mul_one, div_self hk]
    unfold coefficient
    field_simp [hk, hκ0, (Real.log_pos hx).ne']
    <;> ring

/-- Factoring out the large power gives a function at an argument tending to zero. -/
theorem lcmPowerF_normalized {κ x : ℝ} (hx : 1 < x) {n : ℕ} (hn : 1 ≤ n) :
    lcmPowerF κ x n = normalizedF κ x ((x ^ n)⁻¹) := by
  have hx0 : 0 < x := by linarith
  have hz : 0 < x ^ n := pow_pos hx0 n
  have hxn : x ≤ x ^ n := by
    simpa only [pow_one] using (pow_le_pow_right₀ hx.le hn)
  have hi : (x ^ n)⁻¹ ≤ x⁻¹ := (inv_le_inv₀ hz hx0).2 hxn
  have hti : x * (x ^ n)⁻¹ ≤ 1 := by
    calc x * (x ^ n)⁻¹ ≤ x * x⁻¹ := mul_le_mul_of_nonneg_left hi hx0.le
         _ = 1 := mul_inv_cancel₀ hx0.ne'
  have ht1 : (x ^ n)⁻¹ ≤ 1 := hi.trans (inv_le_one_of_one_le₀ hx.le)
  have hscale (u : ℝ) (hu : 0 ≤ u) :
      (x ^ n * u) ^ κ = (x ^ n) ^ κ * u ^ κ := Real.mul_rpow hz.le hu
  have ha : x ^ ((n : ℝ) + 1) = x ^ n * x := by
    rw [Real.rpow_add_one hx0.ne', Real.rpow_natCast]
  have he (u : ℝ) : x ^ n * (u - (x ^ n)⁻¹) = x ^ n * u - 1 := by
    rw [mul_sub, mul_inv_cancel₀ hz.ne']
  have he' (u : ℝ) : x ^ n * (u - x * (x ^ n)⁻¹) = x ^ n * u - x := by
    field_simp
  have he1 : x ^ n * (1 - (x ^ n)⁻¹) = x ^ n - 1 := by simpa using he 1
  have he1' : x ^ n * (1 - x * (x ^ n)⁻¹) = x ^ n - x := by simpa using he' 1
  unfold lcmPowerF normalizedF
  rw [ha, Real.rpow_natCast, ← he x, ← he1, ← he' x, ← he1']
  rw [hscale _ (by linarith), hscale _ (by linarith),
    hscale _ (by linarith), hscale _ (by linarith)]
  congr 2
  rw [← mul_sub, ← mul_sub, mul_div_mul_left _ _ (Real.rpow_pos_of_pos hz κ).ne']

/-- For fixed kappa, the scaled threshold tends to its positive leading coefficient. -/
theorem lcmPowerF_scaled_limit {κ x : ℝ} (hκ : 1 < κ) (hx : 1 < x) :
    Tendsto (fun n : ℕ => lcmPowerF κ x n * x ^ n) atTop (𝓝 (coefficient κ x)) := by
  have hx0 : 0 < x := by linarith
  have ht : Tendsto (fun n : ℕ => (x ^ n)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hx0.le)
        (inv_lt_one_of_one_lt₀ hx))
  have ht' : Tendsto (fun n : ℕ => (x ^ n)⁻¹) atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Filter.Eventually.of_forall
      (fun n => by simpa using inv_ne_zero (pow_ne_zero n hx0.ne'))⟩
  have hs := (normalizedF_derivative hκ hx).tendsto_slope.comp ht'
  dsimp only [Function.comp_def] at hs
  simp only [slope_def_field, normalizedF_zero hκ hx, sub_zero, div_inv_eq_mul] at hs
  apply hs.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [lcmPowerF_normalized hx hn]

/-- The parameter dependence is continuous for every positive integral exponent. -/
theorem continuousOn_lcmPowerF {x : ℝ} (hx : 1 < x) {n : ℕ} (hn : 1 ≤ n) :
    ContinuousOn (fun κ : ℝ => lcmPowerF κ x n) (Ioi 1) := by
  intro κ hκ
  have hκ : 1 < κ := hκ
  have hx0 : 0 < x := by linarith
  have hκ0 : κ ≠ 0 := by linarith
  have hz : 0 < x ^ n := pow_pos hx0 n
  have hxn : x ≤ x ^ n := by
    simpa only [pow_one] using (pow_le_pow_right₀ hx.le hn)
  have ha : x ^ ((n : ℝ) + 1) = x ^ n * x := by
    rw [Real.rpow_add_one hx0.ne', Real.rpow_natCast]
  have hc : x ^ n < x ^ n * x := by nlinarith
  have hnum : 0 < (x ^ ((n : ℝ) + 1) - 1) ^ κ - (x ^ (n : ℝ) - 1) ^ κ := by
    rw [ha, Real.rpow_natCast]
    exact sub_pos.mpr (Real.rpow_lt_rpow (by linarith) (by linarith) (by linarith))
  have hden : 0 < (x ^ ((n : ℝ) + 1) - x) ^ κ - (x ^ (n : ℝ) - x) ^ κ := by
    rw [ha, Real.rpow_natCast]
    exact sub_pos.mpr (Real.rpow_lt_rpow (by linarith) (by linarith) (by linarith))
  have cn : ContinuousAt (fun κ : ℝ =>
      (x ^ ((n : ℝ) + 1) - 1) ^ κ - (x ^ (n : ℝ) - 1) ^ κ) κ :=
    (Real.continuousAt_const_rpow' hκ0).sub (Real.continuousAt_const_rpow' hκ0)
  have cd : ContinuousAt (fun κ : ℝ =>
      (x ^ ((n : ℝ) + 1) - x) ^ κ - (x ^ (n : ℝ) - x) ^ κ) κ :=
    (Real.continuousAt_const_rpow' hκ0).sub (Real.continuousAt_const_rpow' hκ0)
  exact ((cn.div cd hden.ne').log (div_pos hnum hden).ne' |>.div
    (continuousAt_id.mul continuousAt_const) (mul_ne_zero hκ0 (Real.log_pos hx).ne')).continuousWithinAt

end D5.S3.Arith.Robin.Analytic.LcmPowerLeadingTerm
