/- GID: D5/S3/Weil/Mertens/ThetaTailRegularity
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/ThetaTailRegularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform modulus and one-sided L1 amplitude control of the actual theta tail. -/

import D5.S3.Weil.Mertens.ActualThetaTailLaplace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Quantitative regularity of the actual activation-weighted theta tail. -/

namespace D5.S3.Weil.Mertens.ThetaTailRegularity

open Real Set MeasureTheory Filter
open ActualThetaTailLaplace
open ThetaLaplaceContinuation (q)

noncomputable section

private lemma threshold_le_one : u₀ ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  dsimp [u₀]
  linarith

private lemma kernel_bound {u : ℝ} (hu : 1 ≤ u) : ‖k u‖ ≤ 2 := by
  have he : 0 < Real.exp u := Real.exp_pos u
  have ht := Chebyshev.theta_nonneg (Real.exp u)
  have hl : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at *
    linarith
  have hb := (Chebyshev.theta_le_log4_mul_x he.le).trans
    (mul_le_mul_of_nonneg_right hl he.le)
  have hq : |q u| ≤ 1 := by
    rw [q, Real.exp_neg, abs_mul, abs_of_pos (inv_pos.mpr he)]
    apply (inv_mul_le_iff₀ he).mpr
    rw [abs_le]
    constructor <;> linarith
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hw : 0 ≤ (u + 1) / u ^ 2 := by positivity
  have hw2 : (u + 1) / u ^ 2 ≤ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hu0)).mpr
    nlinarith [sq_nonneg (u - 1)]
  rw [k, show q u * (u + 1) / u ^ 2 = q u * ((u + 1) / u ^ 2) by ring,
    norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw]
  exact (mul_le_mul_of_nonneg_right hq hw).trans (by simpa using hw2)

/-- A uniform modulus for the actual tail, including the endpoint one. -/
theorem theta_tail_lipschitz {u v : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) :
    |f u - f v| ≤ 2 * |u - v| := by
  have hk := actual_theta_tail_laplace_ode.2.1
  have hi := intervalIntegral.integral_Ioi_sub_Ioi'
    (hk.mono_set (Ioi_subset_Ioi (threshold_le_one.trans hu)))
    (hk.mono_set (Ioi_subset_Ioi (threshold_le_one.trans hv)))
  have he : f u - f v = -(∫ t in u..v, k t) := by
    dsimp [f]
    linarith
  rw [he, abs_neg, ← Real.norm_eq_abs]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := u) (b := v) (C := 2) (f := k) (fun t ht =>
      kernel_bound ((le_min hu hv).trans ht.1.le))
  simpa only [abs_sub_comm v u] using h

/-- The one-sided triangular area controls every positive actual tail peak.
The interval starts at the peak, so the cutoff itself is allowed. -/
theorem theta_tail_peak_sq_le_mass {U a : ℝ} (hU : 1 ≤ U) (ha : U ≤ a)
    (hF : 0 < f a) :
    (f a) ^ 2 ≤ 4 * ∫ u in Ioi U, |f u| := by
  let b := a + f a / 2
  have hab : a ≤ b := by dsimp [b]; linarith
  have hi : IntegrableOn (fun u => |f u|) (Ioi U) := by
    change Integrable (fun u => |f u|) (volume.restrict (Ioi U))
    simpa only [Real.norm_eq_abs] using
      (actual_theta_tail_laplace_ode.2.2.2.2.1.mono_set
        (Ioi_subset_Ioi (threshold_le_one.trans hU))).norm
  have hif : IntervalIntegrable (fun u => |f u|) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hi.mono_set (fun u hu => lt_of_le_of_lt ha hu.1)
  have hig : IntervalIntegrable (fun u => f a - 2 * (u - a)) volume a b :=
    (continuous_const.sub (continuous_const.mul
      (continuous_id.sub continuous_const))).intervalIntegrable _ _
  have htriangle : (f a) ^ 2 / 4 ≤ ∫ u in a..b, |f u| := by
    have hm := intervalIntegral.integral_mono_on hab hig hif (fun u hu => by
      have hl := theta_tail_lipschitz (hU.trans (ha.trans hu.1)) (hU.trans ha)
      rw [abs_of_nonneg (sub_nonneg.mpr hu.1)] at hl
      have hn := neg_abs_le (f u - f a)
      have hp := le_abs_self (f u)
      linarith)
    have he : (∫ u in a..b, f a - 2 * (u - a)) = (f a) ^ 2 / 4 := by
      have him : IntervalIntegrable (fun u : ℝ => 2 * (u - a)) volume a b :=
        (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable a b
      rw [intervalIntegral.integral_sub intervalIntegrable_const him,
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (f := fun u : ℝ => u) (g := fun _ : ℝ => a)
          (continuous_id.intervalIntegrable a b) intervalIntegrable_const,
        intervalIntegral.integral_id, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      dsimp [b]
      ring
    exact he ▸ hm
  have hmass : (∫ u in a..b, |f u|) ≤ ∫ u in Ioi U, |f u| := by
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_mono_set hi (Eventually.of_forall fun _ => abs_nonneg _)
      (Eventually.of_forall fun u hu => lt_of_le_of_lt ha hu.1)
  linarith

#print axioms theta_tail_lipschitz
#print axioms theta_tail_peak_sq_le_mass

end
end D5.S3.Weil.Mertens.ThetaTailRegularity
