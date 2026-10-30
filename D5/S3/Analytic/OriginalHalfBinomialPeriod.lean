/- GID: D5/S3/Analytic/OriginalHalfBinomialPeriod
   generality: I
   mirror-B: D5/B/S3/Analytic/OriginalHalfBinomialPeriod
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.LocallyUniformLimit, mathlib/module/Mathlib.Analysis.SpecificLimits.Normed]
   utility: none
   digest: The complex Picard-Fuchs equation for the original half-binomial-square period. -/

import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace D5.S3.Analytic.OriginalHalfBinomialPeriod

open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

/-- The period uses the literal original factorial-product coefficients. -/
def period (z : ℂ) : ℂ := ∑' n : ℕ, (halfBinomial n) ^ 2 * z ^ n

private def coefficient (n : ℕ) : ℂ := (halfBinomial n) ^ 2

private lemma coefficient_recurrence (n : ℕ) :
    (n + 1 : ℂ) ^ 2 * coefficient (n + 1) =
      (n + 1 / 2 : ℂ) ^ 2 * coefficient n := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [coefficient, half_successor]
  field_simp
  <;> ring

private lemma half_norm_le (n : ℕ) : ‖halfBinomial n‖ ≤ 1 := by
  induction n with
  | zero => simp [halfBinomial]
  | succ n ih =>
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hnum : (-1 / 2 - (n : ℂ)) = (((-1 / 2 - (n : ℝ)) : ℝ) : ℂ) := by
      push_cast
      rfl
    have hden : (n + 1 : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [half_successor, norm_div, norm_mul, hnum, hden, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonpos (by have := Nat.cast_nonneg (α := ℝ) n; linarith),
      abs_of_pos hn]
    apply (div_le_one hn).mpr
    calc
      _ ≤ -(-1 / 2 - (n : ℝ)) * 1 := by gcongr
      _ ≤ (n : ℝ) + 1 := by linarith

private lemma coefficient_norm_le (n : ℕ) : ‖coefficient n‖ ≤ 1 := by
  simpa only [coefficient, norm_pow, one_pow] using
    pow_le_pow_left₀ (norm_nonneg _) (half_norm_le n) 2

private lemma majorant_summable {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ => (n + 1 : ℝ) ^ 2 * r ^ n) := by
  have hs := ((summable_pow_mul_geometric_of_norm_lt_one 2
    (by simpa [Real.norm_eq_abs, abs_of_pos hr] using hr1)).nat_add 1).mul_right r⁻¹
  convert hs using 1
  ext n
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

private lemma series_derivative (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ (n + 1 : ℝ) ^ 2) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (n + 1 : ℂ) * a (n + 1) * z ^ n)
      (deriv (fun w : ℂ => ∑' n : ℕ, a n * w ^ n) z) ∧
    DifferentiableAt ℂ (fun w : ℂ => ∑' n : ℕ, a n * w ^ n) z := by
  obtain ⟨r, hzr, hr1⟩ := exists_between hz
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg z) hzr
  have hs := majorant_summable hr hr1
  have hb (n : ℕ) (w : ℂ) (hw : w ∈ Metric.ball (0 : ℂ) r) :
      ‖a n * w ^ n‖ ≤ (n + 1 : ℝ) ^ 2 * r ^ n := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul (ha n)
      (pow_le_pow_left₀ (norm_nonneg _) (by simpa using hw.le) n)
      (by positivity) (by positivity)
  have hd (n : ℕ) : DifferentiableOn ℂ (fun w : ℂ => a n * w ^ n)
      (Metric.ball 0 r) := (differentiable_const.mul (differentiable_id.pow n)).differentiableOn
  have hmem : z ∈ Metric.ball (0 : ℂ) r := by simpa using hzr
  have hsum := Complex.hasSum_deriv_of_summable_norm hs hd Metric.isOpen_ball hb hmem
  have hshift := (hasSum_nat_add_iff' 1).mpr hsum
  simp only [Finset.sum_range_one, deriv_const_mul_field, deriv_pow,
    Nat.cast_zero, zero_mul, sub_zero, Nat.add_sub_cancel] at hshift
  constructor
  · convert hshift using 1
    ext n
    push_cast
    ring
  · exact (Complex.differentiableOn_tsum_of_summable_norm hs hd Metric.isOpen_ball hb)
      |>.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)

end D5.S3.Analytic.OriginalHalfBinomialPeriod
