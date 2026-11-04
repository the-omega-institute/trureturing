/- GID: D5/S3/Arith/QuadraticPrefixEnergy
   generality: G
   mirror-B: D5/B/S3/Arith/QuadraticPrefixEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral prefix identities and the triangular reduction for reflected character sums. -/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace D5.S3.Arith.QuadraticPrefixEnergy

open scoped BigOperators

/-- Inclusive positive-index prefix; its value at zero is the empty sum. -/
def prefix (a : ℕ → ℤ) (r : ℕ) : ℤ := ∑ j ∈ Finset.range r, a (j + 1)

/-- The diagonal of the square accounts for the difference between the two triangles. -/
theorem twice_weighted_prefix (a : ℕ → ℤ) (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, a (i + 1) * prefix a (i + 1)) =
      prefix a n ^ 2 + ∑ i ∈ Finset.range n, a (i + 1) ^ 2 := by
  induction n with
  | zero => simp [prefix]
  | succ n ih =>
    have hS : prefix a (n + 1) = prefix a n + a (n + 1) := by
      exact Finset.sum_range_succ _ _
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hS]
    calc
      _ = 2 * (∑ i ∈ Finset.range n, a (i + 1) * prefix a (i + 1)) +
          2 * a (n + 1) * (prefix a n + a (n + 1)) := by ring
      _ = _ := by rw [ih]; ring

/-- Splitting a translated interval at its midpoint and reflecting its upper part.
There is no division in this integral identity. -/
theorem reflected_row_sum (a : ℕ → ℤ) (n i : ℕ) (hi : i ≤ n) (ε : ℤ)
    (hreflect : ∀ r, 1 ≤ r → r ≤ n → a (2 * n + 1 - r) = ε * a r) :
    (∑ k ∈ Finset.range n, a (i + k + 1)) =
      (1 + ε) * prefix a n - prefix a i - ε * prefix a (n - i) := by
  have hsplit₁ : prefix a (n + i) = prefix a n +
      ∑ k ∈ Finset.range i, a (n + k + 1) := by
    exact Finset.sum_range_add _ _ _
  have hsplit₂ : prefix a (n + i) = prefix a i +
      ∑ k ∈ Finset.range n, a (i + k + 1) := by
    rw [Nat.add_comm n i]
    exact Finset.sum_range_add _ _ _
  have hsplit₃ : prefix a n = prefix a (n - i) +
      ∑ k ∈ Finset.range i, a (n - i + k + 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hi]
    exact Finset.sum_range_add _ _ _
  have hu : (∑ k ∈ Finset.range i, a (n + k + 1)) =
      ε * (prefix a n - prefix a (n - i)) := by
    calc
      _ = ∑ k ∈ Finset.range i, ε * a (n - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        have harg : n + k + 1 = 2 * n + 1 - (n - k) := by omega
        rw [harg, hreflect _ (by omega) (by omega)]
      _ = ε * (∑ k ∈ Finset.range i, a (n - k)) := (Finset.mul_sum _ _ _).symm
      _ = ε * (∑ k ∈ Finset.range i, a (n - i + k + 1)) := by
        congr 1
        rw [← Finset.sum_range_reflect (fun k => a (n - i + k + 1)) i]
        apply Finset.sum_congr rfl
        intro k hk
        congr 1
        have := Finset.mem_range.mp hk
        omega
      _ = _ := by rw [hsplit₃]; ring
  rw [hu] at hsplit₁
  linarith

/-- Triangular reduction of the actual double product sum for any reflected sign sequence.
The square-one and cancellation hypotheses are supplied by the quadratic character. -/
theorem twice_triangle (a : ℕ → ℤ) (n : ℕ) (ε : ℤ)
    (hsq : ∀ r, 1 ≤ r → r ≤ n → a r ^ 2 = 1)
    (hreflect : ∀ r, 1 ≤ r → r ≤ n → a (2 * n + 1 - r) = ε * a r)
    (hcancel : (1 + ε) * prefix a n = 0) :
    2 * (∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n,
      a (i + 1) * a (i + 1 + k + 1)) =
        -(prefix a n ^ 2 + (n : ℤ)) -
          2 * ε * (∑ i ∈ Finset.range n, a (i + 1) * prefix a (n - (i + 1))) := by
  have hrows : (∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n,
      a (i + 1) * a (i + 1 + k + 1)) =
        -(∑ i ∈ Finset.range n, a (i + 1) * prefix a (i + 1)) -
          ε * (∑ i ∈ Finset.range n, a (i + 1) * prefix a (n - (i + 1))) := by
    calc
      _ = ∑ i ∈ Finset.range n,
          (-a (i + 1) * prefix a (i + 1) -
            ε * (a (i + 1) * prefix a (n - (i + 1)))) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.mul_sum, reflected_row_sum a n (i + 1)
          (by have := Finset.mem_range.mp hi; omega) ε hreflect, hcancel]
        ring
      _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        ← Finset.mul_sum, neg_mul]
  have hdiag : (∑ i ∈ Finset.range n, a (i + 1) ^ 2) = (n : ℤ) := by
    calc
      _ = ∑ _i ∈ Finset.range n, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hsq _ (by omega) (by have := Finset.mem_range.mp hi; omega)
      _ = _ := by simp
  have hpref := twice_weighted_prefix a n
  rw [hdiag] at hpref
  rw [hrows]
  linarith

end D5.S3.Arith.QuadraticPrefixEnergy
