/- GID: D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/AnnealedPottsMomentBoundRefutation.claim; result=D5.S3.StatisticalMechanics.AnnealedPottsMomentBoundRefutation.result; claim=D5.S3.StatisticalMechanics.AnnealedPottsMomentBoundRefutation.claim
   digest: A two-block density tests the general annealed Potts moment lower bound. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.StatisticalMechanics.AnnealedPottsMomentBoundRefutation

open MeasureTheory Set Filter
open scoped Topology

/-- Moments with respect to a density on the real line. -/
def moment (f : ℝ → ℝ) (n : ℕ) : ℝ := ∫ w, w ^ n * f w

/-- The size-biased order parameter in Section 1, equation (1). -/
def F0 (f : ℝ → ℝ) (q t : ℝ) : ℝ :=
  (∫ w, w * ((Real.exp (t * w) - 1) / (Real.exp (t * w) + q - 1)) * f w) /
    moment f 1

/-- The criticality function in Section 1, equation (6). -/
def K (f : ℝ → ℝ) (q t : ℝ) : ℝ :=
  (∫ w, Real.log ((Real.exp (t * w) + q - 1) / q) * f w) / moment f 1 -
    (q - 1) / (2 * q) * t * F0 f q t - t / q

/-- The general lower inequality in equation (84), with uniqueness explicit. -/
def claim : Prop :=
  ∀ (q : ℝ), 2 < q → ∀ f : ℝ → ℝ,
    Integrable f →
    (∀ w, 0 ≤ f w) →
    (∀ w, w ≤ 0 → f w = 0) →
    (∫ w, f w) = 1 →
    Integrable (fun w => w ^ 4 * f w) →
    (∃! t : ℝ, 0 < t ∧ K f q t = 0) →
    ∀ t : ℝ, 0 < t → K f q t = 0 →
      2 * (moment f 3 / moment f 4) * Real.log (q - 1) < t

private def block (a : ℝ) : ℝ → ℝ :=
  (Icc (a - 1 / 1000) (a + 1 / 1000)).indicator (fun _ => 500)

/-- The mixture of uniform blocks of half-width 1/1000 centered at 1 and 11. -/
def density (w : ℝ) : ℝ := 1331 / 1340 * block 1 w + 9 / 1340 * block 11 w

private lemma block_nonneg (a w : ℝ) : 0 ≤ block a w := by
  unfold block Set.indicator
  split_ifs <;> norm_num

private lemma density_nonneg (w : ℝ) : 0 ≤ density w := by
  exact add_nonneg (mul_nonneg (by norm_num) (block_nonneg 1 w))
    (mul_nonneg (by norm_num) (block_nonneg 11 w))

private lemma density_zero (w : ℝ) (hw : w ≤ 0) : density w = 0 := by
  have h1 : w ∉ Icc (1 - 1 / 1000 : ℝ) (1 + 1 / 1000) := by
    intro h; linarith [h.1]
  have h11 : w ∉ Icc (11 - 1 / 1000 : ℝ) (11 + 1 / 1000) := by
    intro h; linarith [h.1]
  simp only [density, block, indicator_of_notMem h1, indicator_of_notMem h11,
    mul_zero, add_zero]

private lemma weighted_block_integrable (h : ℝ → ℝ) (hh : Continuous h) (a : ℝ) :
    Integrable (fun w => h w * block a w) := by
  have hi := (hh.mul (continuous_const (y := (500 : ℝ)))).integrableOn_Icc
    (a := a - 1 / 1000) (b := a + 1 / 1000) (μ := volume)
  convert hi.integrable_indicator measurableSet_Icc using 1
  ext w
  by_cases hw : w ∈ Icc (a - 1 / 1000) (a + 1 / 1000)
  · simp only [block, indicator_of_mem hw, Pi.mul_apply]
  · simp only [block, indicator_of_notMem hw, mul_zero]

private lemma weighted_density_integrable (h : ℝ → ℝ) (hh : Continuous h) :
    Integrable (fun w => h w * density w) := by
  convert ((weighted_block_integrable h hh 1).const_mul (1331 / 1340)).add
    ((weighted_block_integrable h hh 11).const_mul (9 / 1340)) using 1
  ext w
  simp only [density, Pi.add_apply]
  ring

private lemma integral_weighted_block (h : ℝ → ℝ) (hh : Continuous h) (a : ℝ) :
    (∫ w, h w * block a w) = 500 * ∫ w in (a - 1 / 1000)..(a + 1 / 1000), h w := by
  have heq : (fun w => h w * block a w) =
      (Icc (a - 1 / 1000) (a + 1 / 1000)).indicator (fun w => 500 * h w) := by
    ext w
    by_cases hw : w ∈ Icc (a - 1 / 1000) (a + 1 / 1000)
    · simp only [block, indicator_of_mem hw, mul_comm]
    · simp only [block, indicator_of_notMem hw, mul_zero]
  rw [heq, integral_indicator measurableSet_Icc, integral_const_mul,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]

private lemma integral_weighted_density (h : ℝ → ℝ) (hh : Continuous h) :
    (∫ w, h w * density w) =
      1331 / 1340 * (500 * ∫ w in (999 / 1000 : ℝ)..(1001 / 1000), h w) +
      9 / 1340 * (500 * ∫ w in (10999 / 1000 : ℝ)..(11001 / 1000), h w) := by
  have heq : (fun w => h w * density w) =
      fun w => (1331 / 1340) * (h w * block 1 w) +
        (9 / 1340) * (h w * block 11 w) := by
    ext w; simp only [density]; ring
  rw [heq, integral_add
    ((weighted_block_integrable h hh 1).const_mul _)
    ((weighted_block_integrable h hh 11).const_mul _), integral_const_mul,
    integral_const_mul, integral_weighted_block h hh 1, integral_weighted_block h hh 11]
  norm_num

private lemma density_integrable : Integrable density := by
  simpa using weighted_density_integrable (fun _ => 1) continuous_const

private lemma density_mass : (∫ w, density w) = 1 := by
  have h := integral_weighted_density (fun _ => 1) continuous_const
  norm_num at h ⊢
  exact h

private lemma density_moment_formula (n : ℕ) :
    moment density n =
      (1331 / 1340 : ℝ) * 500 *
        (((1001 / 1000) ^ (n + 1) - (999 / 1000) ^ (n + 1)) / (n + 1)) +
      9 / 1340 * 500 *
        (((11001 / 1000) ^ (n + 1) - (10999 / 1000) ^ (n + 1)) / (n + 1)) := by
  rw [moment, integral_weighted_density (fun w => w ^ n) (continuous_id.pow n),
    integral_pow, integral_pow]
  ring

private lemma density_moments :
    moment density 1 = 143 / 134 ∧
    moment density 3 = 1331000143 / 134000000 ∧
    moment density 4 = 33275001210000067 / 335000000000000 := by
  rw [density_moment_formula 1, density_moment_formula 3, density_moment_formula 4]
  norm_num

private lemma density_fourth_integrable : Integrable (fun w => w ^ 4 * density w) :=
  weighted_density_integrable _ (continuous_id.pow 4)

private lemma density_unique_zero : ∃! t : ℝ, 0 < t ∧ K density 3 t = 0 := by
  sorry

private lemma density_small_zero :
    ∃ t : ℝ, 0 < t ∧ K density 3 t = 0 ∧
      t ≤ 2 * (moment density 3 / moment density 4) * Real.log (3 - 1) := by
  sorry

/-- The two-block density contradicts the proposed general moment lower bound. -/
theorem result : ¬ claim := by
  intro hc
  obtain ⟨t, ht, hKt, hbound⟩ := density_small_zero
  have h := hc 3 (by norm_num) density density_integrable density_nonneg density_zero
    density_mass density_fourth_integrable density_unique_zero t ht hKt
  exact (not_lt_of_ge hbound) h

end D5.S3.StatisticalMechanics.AnnealedPottsMomentBoundRefutation
