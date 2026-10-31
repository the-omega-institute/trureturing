/- GID: D5/S3/Analytic/OriginalHalfBinomialIntegral
   generality: I
   mirror-B: D5/B/S3/Analytic/OriginalHalfBinomialIntegral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Analytic.Binomial, mathlib/module/Mathlib.Analysis.SpecialFunctions.Integrals.Basic, mathlib/module/Mathlib.MeasureTheory.Integral.DominatedConvergence]
   utility: none
   digest: The original half-binomial-square series is its normalized elliptic sine integral. -/

import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace D5.S3.Analytic.OriginalHalfBinomialIntegral

open MeasureTheory Set
open scoped BigOperators Topology
open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

private def b (n : ℕ) : ℝ := (Nat.centralBinom n : ℝ) / 4 ^ n

private theorem b_nonneg (n : ℕ) : 0 ≤ b n := by unfold b; positivity

private theorem b_le_one (n : ℕ) : b n ≤ 1 := by
  rw [b, div_le_one (by positivity)]
  exact_mod_cast Nat.centralBinom_le_four_pow n

private theorem b_succ (n : ℕ) :
    b (n + 1) = ((2 * (n : ℝ) + 1) / (2 * n + 2)) * b n := by
  have hc : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) =
      2 * (2 * n + 1) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  have hn : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
  unfold b
  rw [pow_succ]
  field_simp
  nlinarith [hc]

private theorem half_eq (n : ℕ) :
    halfBinomial n = (-1 : ℂ) ^ n * (b n : ℂ) := by
  induction n with
  | zero => simp [halfBinomial, b]
  | succ n ih =>
    rw [half_successor, ih, b_succ, pow_succ]
    push_cast
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hn2 : (2 * (n : ℂ) + 2) ≠ 0 := by
      have : (2 * (n : ℂ) + 2) = 2 * ((n : ℂ) + 1) := by ring
      rw [this]; exact mul_ne_zero (by norm_num) hn
    field_simp
    ring

private theorem b_multichoose (n : ℕ) :
    Ring.multichoose (1 / 2 : ℝ) n = b n := by
  have hpoch (n : ℕ) : (ascPochhammer ℝ n).eval (1 / 2) =
      (n.factorial : ℝ) * b n := by
    induction n with
    | zero => simp [b]
    | succ n ih =>
      rw [ascPochhammer_succ_eval, ih, b_succ, Nat.factorial_succ]
      push_cast
      have hn : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
      field_simp
      ring
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1 / 2 : ℝ) n
  rw [Polynomial.ascPochhammer_smeval_eq_eval, hpoch, nsmul_eq_mul] at h
  exact (mul_left_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n)) h

private theorem binomial_hasSum (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    HasSum (fun n : ℕ => b n * u ^ n) (1 / Real.sqrt (1 - u)) := by
  have hu : u ∈ Metric.eball (0 : ℝ) 1 := by
    simpa [edist_dist, dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hu0,
      ENNReal.ofReal_lt_one] using hu1
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2)).hasSum_sub hu
  simpa only [sub_zero, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
    ← Ring.multichoose_eq, b_multichoose, ← Real.sqrt_eq_rpow] using h

private theorem sine_moment (n : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin θ ^ (2 * n)) = Real.pi / 2 * b n := by
  induction n with
  | zero => simp [b]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega,
      integral_sin_pow, ih, b_succ]
    simp only [Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two, Real.cos_pi_div_two,
      zero_pow (by omega : 2 * n + 1 ≠ 0), one_pow, mul_zero, zero_mul, sub_self,
      zero_div, zero_add]
    push_cast
    ring

private theorem kernel_integrable (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IntervalIntegrable (fun θ : ℝ => 1 / Real.sqrt (1 - r * Real.sin θ ^ 2))
      volume 0 (Real.pi / 2) := by
  have hd (θ : ℝ) : 0 < 1 - r * Real.sin θ ^ 2 := by
    have := mul_le_of_le_one_right hr0 (Real.sin_sq_le_one θ)
    linarith
  apply Continuous.intervalIntegrable
  exact continuous_const.div
    ((continuous_const.sub (continuous_const.mul (Real.continuous_sin.pow 2))).sqrt)
    (fun θ => ne_of_gt (Real.sqrt_pos.2 (hd θ)))

private theorem summand_bound (r : ℝ) (hr0 : 0 ≤ r) (n : ℕ) (θ : ℝ) :
    ‖b n * r ^ n * Real.sin θ ^ (2 * n)‖ ≤ r ^ n := by
  rw [pow_mul]
  have hs : 0 ≤ (Real.sin θ ^ 2) ^ n := pow_nonneg (sq_nonneg _) _
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (b_nonneg n) (pow_nonneg hr0 _)) hs)]
  calc
    b n * r ^ n * (Real.sin θ ^ 2) ^ n ≤ b n * r ^ n * 1 :=
      mul_le_mul_of_nonneg_left
        (pow_le_one₀ (sq_nonneg _) (Real.sin_sq_le_one θ))
        (mul_nonneg (b_nonneg n) (pow_nonneg hr0 _))
    _ ≤ 1 * r ^ n := by
      simpa using mul_le_mul_of_nonneg_right (b_le_one n) (pow_nonneg hr0 n)
    _ = r ^ n := one_mul _

private theorem integral_hasSum (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => (Real.pi / 2) * (b n ^ 2 * r ^ n))
      (∫ θ in (0 : ℝ)..Real.pi / 2, 1 / Real.sqrt (1 - r * Real.sin θ ^ 2)) := by
  have hg : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)
    (F := fun n θ => b n * r ^ n * Real.sin θ ^ (2 * n))
    (f := fun θ => 1 / Real.sqrt (1 - r * Real.sin θ ^ 2))
    (fun n _ => r ^ n)
    (fun n => (show Continuous (fun θ : ℝ => b n * r ^ n * Real.sin θ ^ (2 * n))
      by fun_prop).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall (fun θ _ => summand_bound r hr0 n θ))
    (Filter.Eventually.of_forall (fun _ _ => hg))
    intervalIntegrable_const ?_
  · convert h using 1
    ext n
    rw [intervalIntegral.integral_const_mul, sine_moment]
    ring
  · apply Filter.Eventually.of_forall
    intro θ _
    have hu0 : 0 ≤ r * Real.sin θ ^ 2 := mul_nonneg hr0 (sq_nonneg _)
    have hu1 : r * Real.sin θ ^ 2 < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right hr0 (Real.sin_sq_le_one θ)) hr1
    convert binomial_hasSum (r * Real.sin θ ^ 2) hu0 hu1 using 1
    ext n
    rw [mul_pow, pow_mul]
    ring

/-- Euler's elliptic sine integral for the literal original complex coefficient series. -/
theorem original_series_eq_integral (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => halfBinomial n ^ 2 * (r : ℂ) ^ n) ∧
    IntervalIntegrable (fun θ : ℝ => 1 / Real.sqrt (1 - r * Real.sin θ ^ 2))
      volume 0 (Real.pi / 2) ∧
    (∑' n : ℕ, halfBinomial n ^ 2 * (r : ℂ) ^ n) =
      (((2 / Real.pi) * (∫ θ in (0 : ℝ)..Real.pi / 2,
        1 / Real.sqrt (1 - r * Real.sin θ ^ 2)) : ℝ) : ℂ) := by
  have h := (integral_hasSum r hr0 hr1).mul_left (2 / Real.pi)
  have hr : HasSum (fun n : ℕ => b n ^ 2 * r ^ n)
      ((2 / Real.pi) * (∫ θ in (0 : ℝ)..Real.pi / 2,
        1 / Real.sqrt (1 - r * Real.sin θ ^ 2))) := by
    convert h using 1
    ext n
    field_simp
  have hc := Complex.ofRealCLM.hasSum hr
  have heq (n : ℕ) : halfBinomial n ^ 2 * (r : ℂ) ^ n =
      ((b n ^ 2 * r ^ n : ℝ) : ℂ) := by
    rw [half_eq, mul_pow, ← pow_mul]
    simp only [mul_comm n 2, pow_mul, neg_one_sq, one_pow, one_mul]
    push_cast
    rfl
  have hc' : HasSum (fun n : ℕ => halfBinomial n ^ 2 * (r : ℂ) ^ n)
      (((2 / Real.pi) * (∫ θ in (0 : ℝ)..Real.pi / 2,
        1 / Real.sqrt (1 - r * Real.sin θ ^ 2)) : ℝ) : ℂ) := by
    simpa only [heq, Complex.ofRealCLM_apply] using hc
  exact ⟨hc'.summable, kernel_integrable r hr0 hr1, hc'.tsum_eq⟩

end D5.S3.Analytic.OriginalHalfBinomialIntegral
