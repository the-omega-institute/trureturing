/- GID: D5/S3/Factorization/A373561
   generality: G
   mirror-B: D5/B/S3/Factorization/A373561
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Granvik's gcd buckets sum to the square-sum polynomial of OEIS A373561. -/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators
open Finset

namespace D5.S3.Factorization.A373561

/-- The signed quadratic expression in Granvik's conjecture. -/
def f (x y z : ℕ) : ℤ := (x : ℤ) ^ 2 + (y : ℤ) ^ 2 - (z : ℤ) ^ 2

private lemma gcd_mem_bucket (m : ℤ) {n : ℕ} (hn : 0 < n) :
    Nat.gcd m.natAbs n ∈ Icc 1 n :=
  mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_right _ hn, Nat.gcd_le_right _ hn⟩

/-- Summing every gcd bucket recovers the unclassified sum, including signed and zero terms. -/
theorem gcd_buckets_eq_sum (n : ℕ) :
    (∑ k ∈ Icc 1 n, ∑ z ∈ Icc 1 n, ∑ y ∈ Icc 1 n, ∑ x ∈ Icc 1 n,
      if Nat.gcd (f x y z).natAbs n = k then f x y z else 0) =
      ∑ z ∈ Icc 1 n, ∑ y ∈ Icc 1 n, ∑ x ∈ Icc 1 n, f x y z := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  · have hmaps : ∀ p ∈ (Icc 1 n) ×ˢ ((Icc 1 n) ×ˢ (Icc 1 n)),
        Nat.gcd (f p.2.2 p.2.1 p.1).natAbs n ∈ Icc 1 n :=
      fun p _ => gcd_mem_bucket _ (Nat.pos_of_ne_zero hn)
    simpa only [sum_filter, sum_product] using
      (sum_fiberwise_of_maps_to hmaps (fun p => f p.2.2 p.2.1 p.1))

/-- The two positive square contributions and one negative contribution leave one square sum. -/
theorem triple_sum_eq (n : ℕ) :
    (∑ z ∈ Icc 1 n, ∑ y ∈ Icc 1 n, ∑ x ∈ Icc 1 n, f x y z) =
      (n : ℤ) ^ 2 * ∑ x ∈ Icc 1 n, (x : ℤ) ^ 2 := by
  simp only [f, sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul,
    Nat.card_Icc, Nat.add_sub_cancel, ← mul_sum]
  ring

/-- The conjectured sum reduces to a square sum before any division is introduced. -/
theorem a373561_core (n : ℕ) :
    (∑ k ∈ Icc 1 n, ∑ z ∈ Icc 1 n, ∑ y ∈ Icc 1 n, ∑ x ∈ Icc 1 n,
      if Nat.gcd (f x y z).natAbs n = k then f x y z else 0) =
      (n : ℤ) ^ 2 * ∑ x ∈ Icc 1 n, (x : ℤ) ^ 2 := by
  rw [gcd_buckets_eq_sum, triple_sum_eq]

private lemma six_mul_sum_sq (n : ℕ) :
    6 * (∑ x ∈ Icc 1 n, (x : ℤ) ^ 2) = (n : ℤ) * (n + 1) * (2 * n + 1) := by
  have hq : 6 * (∑ x ∈ Icc 1 n, (x : ℚ) ^ 2) =
      (n : ℚ) * (n + 1) * (2 * n + 1) := by
    have h := sum_Ico_pow n 2
    norm_num [sum_range_succ, Ico_add_one_right_eq_Icc] at h
    rw [h]
    ring
  exact_mod_cast hq

/-- Mats Granvik's June 10, 2024 conjecture for OEIS A373561, for every natural index. -/
theorem a373561 (n : ℕ) :
    (∑ k ∈ Icc 1 n, ∑ z ∈ Icc 1 n, ∑ y ∈ Icc 1 n, ∑ x ∈ Icc 1 n,
      if Nat.gcd (f x y z).natAbs n = k then f x y z else 0) =
      (n : ℤ) ^ 3 * (n + 1) * (2 * n + 1) / 6 := by
  rw [a373561_core]
  apply Int.eq_ediv_of_mul_eq_right (by norm_num : (6 : ℤ) ≠ 0)
  calc
    6 * ((n : ℤ) ^ 2 * ∑ x ∈ Icc 1 n, (x : ℤ) ^ 2) =
        (n : ℤ) ^ 2 * (6 * ∑ x ∈ Icc 1 n, (x : ℤ) ^ 2) := by ring
    _ = (n : ℤ) ^ 3 * (n + 1) * (2 * n + 1) := by
      rw [six_mul_sum_sq]
      ring

#print axioms gcd_buckets_eq_sum
#print axioms triple_sum_eq
#print axioms a373561_core
#print axioms a373561

end D5.S3.Factorization.A373561
