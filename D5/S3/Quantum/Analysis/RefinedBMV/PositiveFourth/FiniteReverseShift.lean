/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/FiniteReverseShift
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reversal and translation certify polynomial signs on the open unit square. -/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-! Exact binomial coefficients after reversal and translation of both variables. -/

open scoped BigOperators

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum

/-- The coefficient after reversal in each variable and translation by one. -/
def reverseShiftCoeff {ι : Type*} [Fintype ι] (c : ι → ℤ) (a b : ι → ℕ)
    (m n i j : ℕ) : ℤ :=
  ∑ k, c k * ((m - a k).choose i : ℤ) * ((n - b k).choose j : ℤ)

private theorem binomial_to_bound (x : ℝ) {d bound : ℕ} (h : d ≤ bound) :
    (x + 1)^d = ∑ i ∈ Finset.range (bound + 1), x^i * (d.choose i : ℝ) := by
  rw [add_pow]
  simp only [one_pow, mul_one]
  apply Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ h))
  intro i _ hi
  have hdi : d < i := by
    simp only [Finset.mem_range] at hi
    omega
  rw [Nat.choose_eq_zero_of_lt hdi, Nat.cast_zero, mul_zero]

private theorem pow_mul_reversed (x : ℝ) (hx : x ≠ 0) {i m : ℕ} (hi : i ≤ m) :
    x^m * (x⁻¹)^(m-i) = x^i := by
  rw [inv_pow, ← pow_sub₀ x hx (Nat.sub_le m i)]
  congr 1
  omega

/-- Each nonnegative reversed coefficient contributes a nonnegative term
at the two reciprocal gaps. -/
theorem nonneg_of_reverseShiftCoeffs {ι : Type*} [Fintype ι]
    (c : ι → ℤ) (a b : ι → ℕ) (m n : ℕ)
    (ha : ∀ k, a k ≤ m) (hb : ∀ k, b k ≤ n)
    (hcoeff : ∀ i ≤ m, ∀ j ≤ n, 0 ≤ reverseShiftCoeff c a b m n i j)
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (hr1 : r ≤ 1) (ht1 : t ≤ 1) :
    0 ≤ ∑ k, (c k : ℝ) * r^(a k) * t^(b k) := by
  let u := r⁻¹ - 1
  let v := t⁻¹ - 1
  have hu1 : u + 1 = r⁻¹ := sub_add_cancel _ _
  have hv1 : v + 1 = t⁻¹ := sub_add_cancel _ _
  have hu : 0 ≤ u := sub_nonneg.mpr ((one_le_inv₀ hr).2 hr1)
  have hv : 0 ≤ v := sub_nonneg.mpr ((one_le_inv₀ ht).2 ht1)
  have hrev (k : ι) :
      (c k : ℝ) * r^(a k) * t^(b k) =
        (r^m * t^n) * ((c k : ℝ) * (u+1)^(m-a k) * (v+1)^(n-b k)) := by
    rw [hu1, hv1, ← pow_mul_reversed r hr.ne' (ha k),
      ← pow_mul_reversed t ht.ne' (hb k)]
    ring
  have hbin (k : ι) :
      (c k : ℝ) * (u+1)^(m-a k) * (v+1)^(n-b k) =
        ∑ i ∈ Finset.range (m+1), ∑ j ∈ Finset.range (n+1),
          ((c k : ℝ) * ((m-a k).choose i : ℝ) * ((n-b k).choose j : ℝ)) * u^i * v^j := by
    rw [binomial_to_bound u (Nat.sub_le m (a k)),
      binomial_to_bound v (Nat.sub_le n (b k))]
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hrev, hbin]
  rw [← Finset.mul_sum]
  apply mul_nonneg (mul_nonneg (pow_nonneg hr.le _) (pow_nonneg ht.le _))
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun i hi => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun j hj => ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  apply mul_nonneg (mul_nonneg ?_ (pow_nonneg hu _)) (pow_nonneg hv _)
  have hc := hcoeff i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  unfold reverseShiftCoeff at hc
  exact_mod_cast hc

end RefinedBMV.ThreeBlockGram.PositiveSpectrum
