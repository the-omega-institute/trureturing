/- GID: D5/S3/Combinatorics/Splines/MiroRoigTranStrictSign
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Splines/MiroRoigTranStrictSign
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Miró-Roig--Tran alternating binomial coefficient is negative for every n at least two. -/

import D5.S3.Analytic.Curvature.CardinalSplineStrictCurvature

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Splines.MiroRoigTranStrictSign

open Finset Set
open scoped BigOperators
open D5.S3.Analytic.Curvature.CardinalSplineRecurrence
open D5.S3.Analytic.Curvature.CardinalSplineStrictCurvature

/-
proof_shape: coefficient: definition; result: content
escape_witness: `result` actively uses the same-batch global cardinal-spline curvature theorem,
  whose proof propagates a global reflected-difference invariant from the exact order-four base,
  and the exact positive normalization below from the literal integer sum to that curvature value.
admission_basis: result=open-problem-resolution(issue-9765); coefficient=N/A(definition)
Direct frozen dependencies: none (same-batch spline providers and pinned Mathlib only)
-/

/-- The integer coefficient conjectured to be negative by Miró-Roig and Tran after
Proposition 3.12 of arXiv:2001.06143v1. The affine term is formed in `ℤ`. -/
def coefficient (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1),
    (-1 : ℤ) ^ k * (Nat.choose (2 * n + 2) k : ℤ) *
      (2 * (n : ℤ) ^ 2 - 1 - (2 * (n : ℤ) - 1) * (k : ℤ)) ^ (2 * n - 1)

private lemma normalization (n : ℕ) (hn : 2 ≤ n) :
    ((coefficient n : ℤ) : ℝ) =
      (2 * (n : ℝ) - 1) ^ (2 * n - 1) * ((2 * n - 1).factorial : ℝ) *
        C (2 * n + 2) ((2 * (n : ℝ) ^ 2 - 1) / (2 * n - 1)) := by
  have hp : 0 < (2 * (n : ℝ) - 1) := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hexp : 2 * n + 2 - 3 = 2 * n - 1 := by omega
  let f : ℕ → ℝ := fun k =>
    (-1 : ℝ) ^ k * (Nat.choose (2 * n + 2) k : ℝ) *
      max ((2 * (n : ℝ) ^ 2 - 1) / (2 * n - 1) - k) 0 ^ (2 * n - 1)
  have hsum :
      (∑ k ∈ range (2 * n + 2 + 1), f k) = ∑ k ∈ range (n + 1), f k := by
    symm
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    · intro k hkBig hkSmall
      simp only [Finset.mem_range] at hkBig
      simp only [Finset.mem_range, not_lt] at hkSmall
      dsimp [f]
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hkR : (n : ℝ) + 1 ≤ k := by exact_mod_cast hkSmall
      have hp : 0 < (2 * (n : ℝ) - 1) := by nlinarith
      have hsub : (2 * (n : ℝ) ^ 2 - 1) / (2 * n - 1) - k ≤ 0 := by
        apply sub_nonpos.mpr
        apply (div_le_iff₀ hp).2
        nlinarith
      rw [max_eq_right hsub]
      rw [zero_pow (by omega : 2 * n - 1 ≠ 0)]
      ring
  have hcast : ((coefficient n : ℤ) : ℝ) =
      ∑ k ∈ range (n + 1),
        (-1 : ℝ) ^ k * (Nat.choose (2 * n + 2) k : ℝ) *
          (2 * (n : ℝ) ^ 2 - 1 - (2 * (n : ℝ) - 1) * k) ^ (2 * n - 1) := by
    unfold coefficient
    push_cast
    rfl
  have hscaled :
      (2 * (n : ℝ) - 1) ^ (2 * n - 1) * (∑ k ∈ range (n + 1), f k) =
        ((coefficient n : ℤ) : ℝ) := by
    rw [hcast]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    dsimp [f]
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hkR : (k : ℝ) ≤ n := by exact_mod_cast (by omega : k ≤ n)
    have hp : 0 < (2 * (n : ℝ) - 1) := by nlinarith
    have hnum : 0 ≤ 2 * (n : ℝ) ^ 2 - 1 - (2 * n - 1) * k := by nlinarith
    have heq : (2 * (n : ℝ) ^ 2 - 1) / (2 * n - 1) - k =
        (2 * (n : ℝ) ^ 2 - 1 - (2 * n - 1) * k) / (2 * n - 1) := by
      field_simp
    rw [heq, max_eq_left (div_nonneg hnum hp.le), div_pow]
    field_simp
  rw [← hscaled]
  unfold C T
  rw [hexp, hsum]
  field_simp [Nat.factorial_ne_zero]

/-- For every `n ≥ 2`, the literal Miró-Roig--Tran alternating integer coefficient is
strictly negative. -/
theorem result (n : ℕ) (hn : 2 ≤ n) : coefficient n < 0 := by
  have hp : 0 < (2 * (n : ℝ) - 1) := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hscale :
      0 < (2 * (n : ℝ) - 1) ^ (2 * n - 1) * ((2 * n - 1).factorial : ℝ) :=
    mul_pos (pow_pos hp _) (by positivity)
  have hcurvature :
      C (2 * n + 2) ((2 * (n : ℝ) ^ 2 - 1) / (2 * n - 1)) < 0 :=
    cardinalSpline_strict_curvature (2 * n + 2) (by omega) (by
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hp : 0 < (2 * (n : ℝ) - 1) := by nlinarith
      constructor
      · unfold s
        push_cast
        apply (le_div_iff₀ hp).2
        norm_num
        nlinarith
      · unfold s
        push_cast
        apply (div_le_iff₀ hp).2
        norm_num
        nlinarith)
  have hreal : ((coefficient n : ℤ) : ℝ) < 0 := by
    rw [normalization n hn]
    exact mul_neg_of_pos_of_neg hscale hcurvature
  exact_mod_cast hreal

end D5.S3.Combinatorics.Splines.MiroRoigTranStrictSign
