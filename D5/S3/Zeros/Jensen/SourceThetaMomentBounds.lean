/- GID: D5/S3/Zeros/Jensen/SourceThetaMomentBounds
   generality: I
   mirror-B: D5/B/S3/Zeros/Jensen/SourceThetaMomentBounds
   mirror-E: none(waiver:universal-analytic-estimate)
   anchors: []
   utility: none
   digest: Literal theta moments are positive and finite under a summable Gaussian bound. -/

import D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Jensen.SourceThetaMomentBounds

open MeasureTheory
open NormalizedJensenDegreeLowering
open D5.S3.Zeros.CompletedZeta

/-- The literal positive-integer summand of the fixed even theta kernel. -/
def thetaSummand (n : ℕ) (x : ℝ) : ℝ :=
  (4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (9 * |x| / 2) -
    6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * |x| / 2)) *
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * |x|))

/-- Summable coefficients of the common Gaussian majorant. -/
def thetaMajorant (n : ℕ) : ℝ :=
  4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 *
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 / 2)

private theorem gaussian_exponent_bound (m t : ℝ) (hm : 1 ≤ m) (ht : 0 ≤ t) :
    9 * t / 2 - Real.pi * m ^ 2 * Real.exp (2 * t) ≤
      -Real.pi * m ^ 2 / 2 - t ^ 2 := by
  have hm2 : 1 ≤ m ^ 2 := by nlinarith
  have he : 1 ≤ Real.exp (2 * t) := Real.one_le_exp (by linarith)
  have hprod : (m ^ 2 + Real.exp (2 * t)) / 2 ≤ m ^ 2 * Real.exp (2 * t) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm2) (sub_nonneg.mpr he)]
  have hquad := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * t by linarith)
  have hpi : 3 ≤ Real.pi := le_of_lt Real.pi_gt_three
  have hfirst := mul_le_mul_of_nonneg_left hprod Real.pi_pos.le
  have hsecond := mul_le_mul_of_nonneg_right hpi (Real.exp_pos (2 * t)).le
  nlinarith [sq_nonneg (t - 3 / 8)]

/-- Every literal summand is positive and dominated by the same Gaussian. -/
theorem source_theta_summand_bounds (n : ℕ) (x : ℝ) :
    0 < thetaSummand n x ∧
      thetaSummand n x ≤ thetaMajorant n * Real.exp (-x ^ 2) := by
  let m : ℝ := ((n + 1 : ℕ) : ℝ)
  let t : ℝ := |x|
  have hm : 1 ≤ m := by dsimp [m]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have ht : 0 ≤ t := abs_nonneg x
  have hm2 : 1 ≤ m ^ 2 := by nlinarith
  have he : 1 ≤ Real.exp (2 * t) := Real.one_le_exp (by linarith)
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hsplit : Real.exp (9 * t / 2) = Real.exp (5 * t / 2) * Real.exp (2 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfactor : 0 < 4 * Real.pi * m ^ 2 * Real.exp (2 * t) - 6 := by
    have h1 := mul_le_mul_of_nonneg_left he (show 0 ≤ Real.pi * m ^ 2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hm2 Real.pi_pos.le
    nlinarith
  have hpositive : 0 < thetaSummand n x := by
    change 0 < (4 * Real.pi ^ 2 * m ^ 4 * Real.exp (9 * t / 2) -
      6 * Real.pi * m ^ 2 * Real.exp (5 * t / 2)) *
      Real.exp (-Real.pi * m ^ 2 * Real.exp (2 * t))
    rw [hsplit]
    have hfact : 4 * Real.pi ^ 2 * m ^ 4 * (Real.exp (5 * t / 2) * Real.exp (2 * t)) -
        6 * Real.pi * m ^ 2 * Real.exp (5 * t / 2) =
        Real.pi * m ^ 2 * Real.exp (5 * t / 2) *
          (4 * Real.pi * m ^ 2 * Real.exp (2 * t) - 6) := by ring
    rw [hfact]
    positivity
  refine ⟨hpositive, ?_⟩
  change (4 * Real.pi ^ 2 * m ^ 4 * Real.exp (9 * t / 2) -
    6 * Real.pi * m ^ 2 * Real.exp (5 * t / 2)) *
      Real.exp (-Real.pi * m ^ 2 * Real.exp (2 * t)) ≤
    4 * Real.pi ^ 2 * m ^ 4 * Real.exp (-Real.pi * m ^ 2 / 2) * Real.exp (-x ^ 2)
  calc
    _ ≤ (4 * Real.pi ^ 2 * m ^ 4 * Real.exp (9 * t / 2)) *
        Real.exp (-Real.pi * m ^ 2 * Real.exp (2 * t)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact sub_le_self _ (by positivity)
    _ = 4 * Real.pi ^ 2 * m ^ 4 *
        Real.exp (9 * t / 2 - Real.pi * m ^ 2 * Real.exp (2 * t)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 4 * Real.pi ^ 2 * m ^ 4 * Real.exp (-Real.pi * m ^ 2 / 2 - t ^ 2) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (gaussian_exponent_bound m t hm ht)) (by positivity)
    _ = _ := by
      rw [Real.exp_sub]
      simp only [t, sq_abs, Real.exp_neg, div_eq_mul_inv, mul_assoc]

/-- The Gaussian coefficients have a finite sum. -/
theorem source_theta_majorant_summable : Summable thetaMajorant := by
  have hs := (Real.summable_pow_mul_exp_neg_nat_mul 4
    (show 0 < Real.pi / 2 by positivity)).comp_injective Nat.succ_injective
  apply (hs.mul_left (4 * Real.pi ^ 2)).of_nonneg_of_le
    (fun n => by dsimp [thetaMajorant]; positivity)
  intro n
  dsimp [thetaMajorant, Function.comp_def]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hm : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hsq : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq Real.pi_pos.le]

/-- The literal theta series converges at every real argument. -/
theorem source_theta_summable (x : ℝ) : Summable (fun n => thetaSummand n x) :=
  (source_theta_majorant_summable.mul_right (Real.exp (-x ^ 2))).of_nonneg_of_le
    (fun n => (source_theta_summand_bounds n x).1.le)
    (fun n => (source_theta_summand_bounds n x).2)

/-- Uniform summability preserves the continuity of the literal even kernel. -/
theorem source_theta_continuous : Continuous sourceThetaKernel := by
  apply continuous_tsum (f := thetaSummand)
    (fun n => by unfold thetaSummand; fun_prop) source_theta_majorant_summable
  intro n x
  rw [Real.norm_eq_abs, abs_of_pos (source_theta_summand_bounds n x).1]
  exact (source_theta_summand_bounds n x).2.trans
    (mul_le_of_le_one_right (by dsimp [thetaMajorant]; positivity)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg x))))

/-- The absolute-value extension is even. -/
theorem source_theta_even (x : ℝ) : sourceThetaKernel (-x) = sourceThetaKernel x := by
  simp only [sourceThetaKernel, abs_neg]

/-- The actual kernel is strictly positive and bounded by an explicit Gaussian. -/
theorem source_theta_gaussian_bound (x : ℝ) :
    0 < sourceThetaKernel x ∧
      sourceThetaKernel x ≤ (∑' n, thetaMajorant n) * Real.exp (-x ^ 2) := by
  change 0 < ∑' n, thetaSummand n x ∧
    (∑' n, thetaSummand n x) ≤ (∑' n, thetaMajorant n) * Real.exp (-x ^ 2)
  constructor
  · exact (source_theta_summand_bounds 0 x).1.trans_le
      ((source_theta_summable x).le_tsum 0 (fun n _ => (source_theta_summand_bounds n x).1.le))
  · simpa only [tsum_mul_right] using
      ((source_theta_summable x).tsum_le_tsum (fun n => (source_theta_summand_bounds n x).2)
        (source_theta_majorant_summable.mul_right (Real.exp (-x ^ 2))))

/-- All actual raw even moments are integrable and strictly positive. -/
theorem source_theta_raw_moments (k : ℕ) :
    Integrable (fun x : ℝ => x ^ (2 * k) * sourceThetaKernel x) ∧
      0 < ∫ x : ℝ, x ^ (2 * k) * sourceThetaKernel x := by
  have hc : Continuous (fun x : ℝ => x ^ (2 * k) * sourceThetaKernel x) :=
    (continuous_id.pow _).mul source_theta_continuous
  have hp (x : ℝ) : 0 ≤ x ^ (2 * k) := by rw [pow_mul]; positivity
  have hg : Integrable (fun x : ℝ => x ^ (2 * k) * Real.exp (-x ^ 2)) := by
    simpa only [Real.rpow_natCast, neg_one_mul] using
      (integrable_rpow_mul_exp_neg_mul_sq (b := 1) (by norm_num)
        (s := ((2 * k : ℕ) : ℝ)) (by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _)))
  have hi : Integrable (fun x : ℝ => x ^ (2 * k) * sourceThetaKernel x) := by
    apply (hg.const_mul (∑' n, thetaMajorant n)).mono' hc.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (hp x) (source_theta_gaussian_bound x).1.le)]
    calc
      _ ≤ x ^ (2 * k) * ((∑' n, thetaMajorant n) * Real.exp (-x ^ 2)) :=
        mul_le_mul_of_nonneg_left (source_theta_gaussian_bound x).2 (hp x)
      _ = _ := by ring
  refine ⟨hi, integral_pos_of_integrable_nonneg_nonzero hc hi
    (fun x => mul_nonneg (hp x) (source_theta_gaussian_bound x).1.le) (x := 1) ?_⟩
  simpa only [one_pow, one_mul] using (source_theta_gaussian_bound 1).1.ne'

/-- Unit constant coefficient determines the literal xi denominator and all signs. -/
theorem source_theta_normalization (h0 : sourceThetaCoefficient 0 = 1) :
    (xiReading (1 / 2 : ℂ)).re = ∫ x : ℝ, sourceThetaKernel x ∧
    0 < (xiReading (1 / 2 : ℂ)).re ∧
    (∫ x : ℝ, sourceThetaDensity x) = 1 ∧
    (∀ k : ℕ, 0 < sourceThetaCoefficient k) := by
  have hz0 : (xiReading (1 / 2 : ℂ)).re ≠ 0 := by
    intro hz
    simp only [sourceThetaCoefficient, sourceThetaMoment, sourceThetaDensity, hz,
      div_zero, mul_zero, integral_zero, zero_div] at h0
    norm_num at h0
  have hm (k : ℕ) : sourceThetaMoment k =
      (∫ x : ℝ, x ^ (2 * k) * sourceThetaKernel x) / (xiReading (1 / 2 : ℂ)).re := by
    simp only [sourceThetaMoment, sourceThetaDensity, ← mul_div_assoc, integral_div]
  have hmass : (∫ x : ℝ, sourceThetaKernel x) / (xiReading (1 / 2 : ℂ)).re = 1 := by
    simpa [sourceThetaCoefficient, hm] using h0
  have hz : (xiReading (1 / 2 : ℂ)).re = ∫ x : ℝ, sourceThetaKernel x :=
    ((div_eq_one_iff_eq hz0).mp hmass).symm
  have hpos : 0 < (xiReading (1 / 2 : ℂ)).re := by
    rw [hz]
    simpa using (source_theta_raw_moments 0).2
  refine ⟨hz, hpos, ?_, ?_⟩
  · simpa [sourceThetaCoefficient, sourceThetaMoment] using h0
  · intro k
    rw [sourceThetaCoefficient, hm]
    exact div_pos (div_pos (source_theta_raw_moments k).2 hpos) (by positivity)

end D5.S3.Zeros.Jensen.SourceThetaMomentBounds
