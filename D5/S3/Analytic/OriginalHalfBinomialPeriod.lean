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
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-! The literal original half-binomial-square sum satisfies the complex Gauss equation. -/

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
  ring

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
      _ ≤ -(-1 / 2 - (n : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left ih (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      _ ≤ (n : ℝ) + 1 := by linarith

private lemma coefficient_norm_le (n : ℕ) : ‖coefficient n‖ ≤ 1 := by
  simpa only [coefficient, norm_pow, one_pow] using
    pow_le_pow_left₀ (norm_nonneg _) (half_norm_le n) 2

private lemma majorant_summable {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ => (n + 1 : ℝ) ^ 2 * r ^ n) := by
  have hgeom := summable_pow_mul_geometric_of_norm_lt_one 2 (r := r)
    (by simpa [Real.norm_eq_abs, abs_of_pos hr] using hr1)
  have hs := ((summable_nat_add_iff 1).mpr hgeom).mul_right r⁻¹
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
      (pow_le_pow_left₀ (norm_nonneg _) (by
        exact (show ‖w‖ < r by simpa using hw).le) n)
      (by positivity) (by positivity)
  have hd (n : ℕ) : DifferentiableOn ℂ (fun w : ℂ => a n * w ^ n)
      (Metric.ball 0 r) := fun w _ =>
        ((hasDerivAt_pow n w).const_mul (a n)).differentiableAt.differentiableWithinAt
  have hmem : z ∈ Metric.ball (0 : ℂ) r := by simpa using hzr
  have hsum := Complex.hasSum_deriv_of_summable_norm hs hd Metric.isOpen_ball hb hmem
  have hshift := (hasSum_nat_add_iff' 1).mpr hsum
  simp only [Finset.sum_range_one, deriv_const_mul_field, deriv_pow_field,
    Nat.cast_zero, zero_mul, mul_zero, sub_zero, Nat.add_sub_cancel] at hshift
  constructor
  · convert hshift using 1
    ext n
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  · exact (Complex.differentiableOn_tsum_of_summable_norm hs hd Metric.isOpen_ball hb)
      |>.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)

private def firstCoefficient (n : ℕ) : ℂ := (n + 1 : ℂ) * coefficient (n + 1)

private lemma first_coefficient_bound (n : ℕ) :
    ‖firstCoefficient n‖ ≤ (n + 1 : ℝ) ^ 2 := by
  have hn : 1 ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.le_add_left 1 n
  have he : ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by
    rw [show (n + 1 : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
  calc
    _ = ‖(n + 1 : ℂ)‖ * ‖coefficient (n + 1)‖ := norm_mul _ _
    _ ≤ (n + 1 : ℝ) * 1 := by rw [he]; gcongr; exact coefficient_norm_le _
    _ ≤ (n + 1 : ℝ) ^ 2 := by nlinarith

private lemma period_derivative {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => firstCoefficient n * z ^ n) (deriv period z) ∧
      DifferentiableAt ℂ period z := by
  apply series_derivative coefficient _ hz
  intro n
  exact (coefficient_norm_le n).trans (by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith)

/-- The native period and its first derivative are complex differentiable throughout
the open unit disk, where the exact Picard-Fuchs equation holds, including zero. -/
theorem picard_fuchs {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ period z ∧ DifferentiableAt ℂ (deriv period) z ∧
      z * (1 - z) * deriv (deriv period) z +
        (1 - 2 * z) * deriv period z - (1 / 4 : ℂ) * period z = 0 := by
  let first : ℂ → ℂ := fun w => ∑' n : ℕ, firstCoefficient n * w ^ n
  have he : deriv period =ᶠ[𝓝 z] first := by
    filter_upwards [Metric.isOpen_ball.mem_nhds
      (show z ∈ Metric.ball (0 : ℂ) 1 by simpa using hz)] with w hw
    exact (period_derivative (by simpa using hw)).1.tsum_eq.symm
  have hfirst := series_derivative firstCoefficient first_coefficient_bound hz
  have h1 := (period_derivative hz).1
  have h2 : HasSum (fun n : ℕ => (n + 1 : ℂ) * firstCoefficient (n + 1) * z ^ n)
      (deriv (deriv period) z) := by
    rw [he.deriv_eq]
    exact hfirst.1
  have hza : HasSum (fun n : ℕ => (n : ℂ) * firstCoefficient n * z ^ n)
      (z * deriv (deriv period) z) := by
    rw [← hasSum_nat_add_iff' 1]
    convert h2.mul_left z using 1
    · ext n
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      ring
    · simp
  have hl : HasSum (fun n : ℕ => (n + 1 / 2 : ℂ) ^ 2 * coefficient n * z ^ n)
      (z * deriv (deriv period) z + deriv period z) := by
    convert hza.add h1 using 1
    ext n
    dsimp [firstCoefficient]
    linear_combination -(z ^ n) * coefficient_recurrence n
  have heuler : HasSum (fun n : ℕ => (n : ℂ) * coefficient n * z ^ n)
      (z * deriv period z) := by
    rw [← hasSum_nat_add_iff' 1]
    convert h1.mul_left z using 1
    · ext n
      simp only [firstCoefficient, Nat.cast_add, Nat.cast_one, pow_succ]
      ring
    · simp
  have hsecond : HasSum
      (fun n : ℕ => ((n : ℂ) - 1) * (n : ℂ) * coefficient n * z ^ n)
      (z ^ 2 * deriv (deriv period) z) := by
    rw [← hasSum_nat_add_iff' 1]
    convert hza.mul_left z using 1
    · ext n
      simp only [firstCoefficient, Nat.cast_add, Nat.cast_one, pow_succ]
      ring
    · simp
      ring
  have h0 : HasSum (fun n : ℕ => coefficient n * z ^ n) (period z) := by
    apply Summable.hasSum
    apply Summable.of_norm_bounded (summable_norm_geometric_of_norm_lt_one hz)
    intro n
    simpa only [norm_mul, norm_pow, one_mul] using
      mul_le_mul_of_nonneg_right (coefficient_norm_le n) (pow_nonneg (norm_nonneg z) n)
  have hr : HasSum (fun n : ℕ => (n + 1 / 2 : ℂ) ^ 2 * coefficient n * z ^ n)
      (z ^ 2 * deriv (deriv period) z + 2 * (z * deriv period z) +
        (1 / 4 : ℂ) * period z) := by
    convert (hsecond.add (heuler.mul_left 2)).add (h0.mul_left (1 / 4)) using 1
    ext n
    ring
  refine ⟨(period_derivative hz).2, he.differentiableAt_iff.mpr hfirst.2, ?_⟩
  linear_combination hl.unique hr

end D5.S3.Analytic.OriginalHalfBinomialPeriod
