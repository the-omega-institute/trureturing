/- GID: D5/S3/Quantum/Analysis/RefinedBMV/NearScalar/AnalyticTail
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Proof component of the four-copy refined BMV comparison near a scalar. -/

import Mathlib

/-! Scalar Taylor remainder in the direct four-copy near-scalar BMV proof. -/

open scoped BigOperators

namespace D5.S3.Quantum.Analysis.RefinedBMVNearScalarAnalyticTail

private theorem pow_four_div_factorial_le {n : ℕ} (hn : 3 ≤ n) :
    (n : ℝ) ^ 4 / (n.factorial : ℝ) ≤ 27 / 2 := by
  refine Nat.le_induction ?_ ?_ n hn
  · norm_num [show Nat.factorial 3 = 6 by decide]
  · intro m hm ih
    have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have hpoly : 0 ≤ (m : ℝ) ^ 3 + 2 * (m : ℝ) ^ 2 + 3 * m + 6 := by
      positivity
    have hcube : ((m : ℝ) + 1) ^ 3 ≤ (m : ℝ) ^ 4 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hm') hpoly]
    have hfac : 0 < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    have hsucc : 0 < (m : ℝ) + 1 := by positivity
    calc
      ((m + 1 : ℕ) : ℝ) ^ 4 / ((m + 1).factorial : ℝ) =
          ((m : ℝ) + 1) ^ 3 / (m.factorial : ℝ) := by
            simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
            field_simp [ne_of_gt hsucc, ne_of_gt hfac] <;> ring
      _ ≤ (m : ℝ) ^ 4 / (m.factorial : ℝ) :=
        (div_le_div_iff_of_pos_right hfac).2 hcube
      _ ≤ 27 / 2 := ih

/-- The tail starts at degree three, so `f j` is the coefficient at degree `j + 3`. -/
private theorem hasSum_analytic_tail {f : ℕ → ℝ} {p K x : ℝ}
    (hx₀ : 0 ≤ x) (hx₁ : x < 1)
    (hterm : ∀ j, |f j| ≤
      192 * ((j + 3 : ℕ) : ℝ) ^ 4 * p ^ 2 * K ^ 2 * x ^ (j + 1) /
        ((j + 3).factorial : ℝ)) :
    HasSum f (∑' j, f j) ∧ |(∑' j, f j)| ≤ 2592 * p ^ 2 * K ^ 2 * x / (1 - x) := by
  have hgeom : HasSum (fun j : ℕ ↦ (2592 * p ^ 2 * K ^ 2 * x) * x ^ j)
      (2592 * p ^ 2 * K ^ 2 * x / (1 - x)) := by
    have hxabs : |x| < 1 := by simpa only [abs_of_nonneg hx₀] using hx₁
    simpa only [div_eq_mul_inv] using
      (hasSum_geometric_of_abs_lt_one hxabs).mul_left (2592 * p ^ 2 * K ^ 2 * x)
  have hmajorant (j : ℕ) : ‖f j‖ ≤ (2592 * p ^ 2 * K ^ 2 * x) * x ^ j := by
    rw [Real.norm_eq_abs]
    calc
      |f j| ≤ 192 * ((j + 3 : ℕ) : ℝ) ^ 4 * p ^ 2 * K ^ 2 * x ^ (j + 1) /
          ((j + 3).factorial : ℝ) := hterm j
      _ = (((j + 3 : ℕ) : ℝ) ^ 4 / ((j + 3).factorial : ℝ)) *
          (192 * p ^ 2 * K ^ 2 * x ^ (j + 1)) := by
            simp only [div_eq_mul_inv]
            ring
      _ ≤ (27 / 2) * (192 * p ^ 2 * K ^ 2 * x ^ (j + 1)) :=
        mul_le_mul_of_nonneg_right (pow_four_div_factorial_le (n := j + 3) (by omega))
          (by positivity)
      _ = (2592 * p ^ 2 * K ^ 2 * x) * x ^ j := by rw [pow_succ x j]; ring
  have habs : Summable (fun j ↦ ‖f j‖) :=
    hgeom.summable.of_norm_bounded (fun j ↦ by
      rw [Real.norm_eq_abs ‖f j‖, abs_of_nonneg (norm_nonneg (f j))]
      exact hmajorant j)
  have hsum := habs.of_norm.hasSum
  exact ⟨hsum, by
    simpa only [Real.norm_eq_abs] using hsum.norm_le_of_bounded hgeom hmajorant⟩

/-- After constant and linear cancellation, add the signed tail to the quadratic term. -/
theorem quadratic_add_tail_ge {f : ℕ → ℝ} {p K x quadratic : ℝ}
    (hx₀ : 0 ≤ x) (hx : x ≤ 1 / 100000)
    (hterm : ∀ j, |f j| ≤
      192 * ((j + 3 : ℕ) : ℝ) ^ 4 * p ^ 2 * K ^ 2 * x ^ (j + 1) /
        ((j + 3).factorial : ℝ))
    (hquad : (3 / 40) * (p ^ 2 * K ^ 2) ≤ quadratic) :
    HasSum f (∑' j, f j) ∧ p ^ 2 * K ^ 2 / 25 ≤ quadratic + (∑' j, f j) := by
  have hx₁ : x < 1 := by linarith only [hx]
  obtain ⟨hsum, htail⟩ := hasSum_analytic_tail hx₀ hx₁ hterm
  have hratio : 2592 * x / (1 - x) ≤ 2592 / 99999 := by
    apply (div_le_iff₀ (sub_pos.mpr hx₁)).2
    linarith only [hx]
  have hsmall : 2592 * p ^ 2 * K ^ 2 * x / (1 - x) ≤
      (7 / 200) * (p ^ 2 * K ^ 2) := by
    calc
      2592 * p ^ 2 * K ^ 2 * x / (1 - x) =
          (2592 * x / (1 - x)) * (p ^ 2 * K ^ 2) := by
            simp only [div_eq_mul_inv]
            ring
      _ ≤ (7 / 200) * (p ^ 2 * K ^ 2) :=
        mul_le_mul_of_nonneg_right (hratio.trans (by norm_num)) (by positivity)
  have hlower : -((7 / 200) * (p ^ 2 * K ^ 2)) ≤ ∑' j, f j :=
    (neg_le_neg hsmall).trans (abs_le.mp htail).1
  exact ⟨hsum, by nlinarith only [hquad, hlower]⟩

end D5.S3.Quantum.Analysis.RefinedBMVNearScalarAnalyticTail
