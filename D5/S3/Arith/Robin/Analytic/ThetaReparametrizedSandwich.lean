/- GID: D5/S3/Arith/Robin/Analytic/ThetaReparametrizedSandwich
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/ThetaReparametrizedSandwich
   mirror-E: none(waiver:pointwise-actual-tail-comparison)
   anchors: []
   utility: none
   digest: Actual arithmetic B is trapped by theta-reparametrized tails with the exact finite correction. -/

import D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope
import D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature
import D5.S3.Arith.Robin.MellinWeightedVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.InvLog

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set MeasureTheory
open scoped Interval Topology

namespace D5.S3.Arith.Robin.Analytic.ThetaReparametrizedSandwich

open D5.S3.Arith.Robin.ActualRobinClockCovariance
  (g activationDensity g_has_deriv_at density_integrable)
open D5.S3.Arith.Robin.ThetaTailRobinWitness (theta_tail_mertens_robin)
open D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature
  (loglog_tangent_gap_quadratic)
open D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (B N)
open D5.S3.Weil.Mertens.ActualThetaTailLaplace (F)

private abbrev w := activationDensity

private lemma density_nonneg {t : ℝ} (ht : 1 < t) : 0 ≤ w t := by
  exact D5.S3.Arith.Robin.MellinWeightedVariation.weight_nonneg ht

private lemma weighted_density_integrable {a b : ℝ} (ha : 1 < a) (hb : 1 < b)
    (c : ℝ) : IntervalIntegrable (fun t => (c - t) * w t) volume a b := by
  have hi : IntervalIntegrable w volume a b := by
    rcases le_total a b with hab | hba
    · exact density_integrable ha hab
    · exact (density_integrable hb hba).symm
  exact hi.continuousOn_mul (continuous_const.sub continuous_id).continuousOn

/- A single FTC computation, using the original derivative of g. This is an
oriented identity on uIcc, so it also applies when b < a or b = a. -/
private lemma loglog_oriented_taylor {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    Real.log (Real.log b) - Real.log (Real.log a) - (b - a) / (a * Real.log a) =
      -(∫ t in a..b, (b - t) * w t) := by
  have hdomain : ∀ t ∈ uIcc a b, 1 < t := by
    intro t ht
    exact (lt_min ha hb).trans_le ht.1
  have hderiv : ∀ t ∈ uIcc a b,
      HasDerivAt (fun u : ℝ => (b - u) * g u + Real.log (Real.log u))
        (-((b - t) * w t)) t := by
    intro t ht
    have ht1 := hdomain t ht
    have hloglog : HasDerivAt (fun u : ℝ => Real.log (Real.log u)) (g t) t := by
      simpa [g, one_div, div_eq_mul_inv, mul_inv_rev, mul_comm] using
        Real.hasDerivAt_log_log (ne_of_gt (by linarith : 0 < t))
          (ne_of_gt ht1) (by linarith : t ≠ -1)
    have hline : HasDerivAt (fun u : ℝ => b - u) (-1) t := by
      simpa only [id_eq] using (hasDerivAt_id t).const_sub b
    have hd := (hline.mul (g_has_deriv_at ht1)).add hloglog
    apply hd.congr_deriv
    dsimp only [w]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (weighted_density_integrable ha hb b).neg
  rw [intervalIntegral.integral_neg] at hFTC
  simp only [sub_self, zero_mul, zero_add] at hFTC
  dsimp only [g] at hFTC
  rw [mul_one_div] at hFTC
  linarith only [hFTC]

/- The original actual Mertens-tail identity suffices for the literal B
decomposition; no psi-tail or spectral assertion is needed. -/
private lemma actual_B_decomposition {x : ℝ} (hx : 2 ≤ x) :
    B x = -F x + (Mertens.E₃ x + Mertens.E₂p x) + N x := by
  have hm := (theta_tail_mertens_robin x hx).2.1
  change F x = Mertens.E₂p x -
    (Chebyshev.theta x - x) / (x * Real.log x) at hm
  dsimp only [B, N]
  linarith only [hm]

/- Exact telescope before taking signs. The source is interval integrable
because each ordered segment is a restriction of an actual integrable tail.
No derivative or continuity of theta is asserted. -/
private lemma actual_reparametrized_telescope {x : ℝ}
    (hx : 2 < x) (htheta : 2 < Chebyshev.theta x) :
    -F x + N x - (-F (Chebyshev.theta x)) =
      ∫ t in x..Chebyshev.theta x, (Chebyshev.theta t - Chebyshev.theta x) * w t := by
  have hx1 : 1 < x := by linarith
  have hy1 : 1 < Chebyshev.theta x := by linarith
  have htx := theta_tail_mertens_robin x hx.le
  have hty := theta_tail_mertens_robin (Chebyshev.theta x) htheta.le
  have htail : -F x - (-F (Chebyshev.theta x)) =
      ∫ t in x..Chebyshev.theta x, (Chebyshev.theta t - t) * w t := by
    simpa only [F, neg_neg] using
      (intervalIntegral.integral_Ioi_sub_Ioi' htx.1 hty.1)
  have hN : N x = -(∫ t in x..Chebyshev.theta x, (Chebyshev.theta x - t) * w t) := by
    simpa only [N] using (loglog_oriented_taylor hx1 hy1)
  have hi : IntervalIntegrable (fun t => (Chebyshev.theta t - t) * w t)
      volume x (Chebyshev.theta x) := by
    rcases le_total x (Chebyshev.theta x) with hxy | hyx
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxy]
      exact htx.1.mono_set Ioc_subset_Ioi_self
    · have hi' : IntervalIntegrable (fun t => (Chebyshev.theta t - t) * w t)
          volume (Chebyshev.theta x) x := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hyx]
        exact hty.1.mono_set Ioc_subset_Ioi_self
      exact hi'.symm
  calc
    -F x + N x - (-F (Chebyshev.theta x)) =
        (∫ t in x..Chebyshev.theta x, (Chebyshev.theta t - t) * w t) -
          (∫ t in x..Chebyshev.theta x, (Chebyshev.theta x - t) * w t) := by
      linarith only [htail, hN]
    _ = ∫ t in x..Chebyshev.theta x,
        ((Chebyshev.theta t - t) * w t - (Chebyshev.theta x - t) * w t) :=
      (intervalIntegral.integral_sub hi
        (weighted_density_integrable hx1 hy1 (Chebyshev.theta x))).symm
    _ = ∫ t in x..Chebyshev.theta x, (Chebyshev.theta t - Chebyshev.theta x) * w t := by
      apply intervalIntegral.integral_congr
      intro t _
      ring

private lemma actual_defect_nonneg {x : ℝ}
    (hx : 2 < x) (htheta : 2 < Chebyshev.theta x) :
    0 ≤ ∫ t in x..Chebyshev.theta x, (Chebyshev.theta t - Chebyshev.theta x) * w t := by
  by_cases hxy : x ≤ Chebyshev.theta x
  · apply intervalIntegral.integral_nonneg hxy
    intro t ht
    exact mul_nonneg (sub_nonneg.mpr (Chebyshev.theta_mono ht.1))
      (density_nonneg (by linarith [ht.1] : 1 < t))
  · have hyx : Chebyshev.theta x ≤ x := le_of_not_ge hxy
    rw [intervalIntegral.integral_symm]
    have hreverse : 0 ≤ ∫ t in Chebyshev.theta x..x,
        -((Chebyshev.theta t - Chebyshev.theta x) * w t) := by
      apply intervalIntegral.integral_nonneg hyx
      intro t ht
      exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (Chebyshev.theta_mono ht.2))
        (density_nonneg (by linarith [ht.1] : 1 < t)))
    simpa only [intervalIntegral.integral_neg] using hreverse

/- Use the original full-domain curvature result, including both endpoint
orders, for the upper inequality. Do not reproduce its calculus proof. -/
private lemma actual_N_nonpos {x : ℝ}
    (hx : 2 < x) (htheta : 2 < Chebyshev.theta x) : N x ≤ 0 := by
  have hx1 : 1 < x := by linarith
  have hy1 : 1 < Chebyshev.theta x := by linarith
  have hcurv := (loglog_tangent_gap_quadratic hx1 hy1).1
  dsimp only at hcurv
  have hzero : 0 ≤ w (max x (Chebyshev.theta x)) * (Chebyshev.theta x - x) ^ 2 / 2 :=
    div_nonneg (mul_nonneg
      (density_nonneg (hx1.trans_le (le_max_left _ _))) (sq_nonneg _)) (by norm_num)
  have hcurv' : w (max x (Chebyshev.theta x)) * (Chebyshev.theta x - x) ^ 2 / 2 ≤
      Real.log (Real.log x) + (Chebyshev.theta x - x) / (x * Real.log x) -
        Real.log (Real.log (Chebyshev.theta x)) := by
    simpa only [w, activationDensity, add_comm] using hcurv
  dsimp only [N]
  linarith only [hzero, hcurv']

/-- The actual global theta-reparametrized sandwich, with the exact finite
Mertens correction. This is a conditional pointwise monotonicity result. -/
theorem actual_theta_reparametrized_sandwich {x : ℝ}
    (hx : 2 < x) (htheta : 2 < Chebyshev.theta x) :
    -D5.S3.Weil.Mertens.ActualThetaTailLaplace.F (Chebyshev.theta x) +
        (Mertens.E₃ x + Mertens.E₂p x) ≤
      D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.B x ∧
    D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.B x ≤
      -D5.S3.Weil.Mertens.ActualThetaTailLaplace.F x +
        (Mertens.E₃ x + Mertens.E₂p x) := by
  have hdecomp := actual_B_decomposition hx.le
  have htelescope := actual_reparametrized_telescope hx htheta
  have hsign := actual_defect_nonneg hx htheta
  have hN := actual_N_nonpos hx htheta
  constructor
  · linarith only [hdecomp, htelescope, hsign]
  · linarith only [hdecomp, hN]

#print axioms actual_theta_reparametrized_sandwich

end D5.S3.Arith.Robin.Analytic.ThetaReparametrizedSandwich
