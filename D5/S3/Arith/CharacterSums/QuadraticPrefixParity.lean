/- GID: D5/S3/Arith/CharacterSums/QuadraticPrefixParity
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/QuadraticPrefixParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral interval parity and reflection norms of finite sign prefixes. -/

import D5.S3.Arith.CharacterSums.QuadraticPrefixEnergy
import D5.S3.Arith.CharacterSums.QuadraticSignProducts
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.ModEq

namespace D5.S3.Arith.CharacterSums.QuadraticPrefixParity

open scoped BigOperators
open D5.S3.Arith.CharacterSums.QuadraticPrefixEnergy D5.S3.Arith.CharacterSums.QuadraticSignProducts

/-- Applying the sign rule to a genuine disjoint union counts repeated signs with
multiplicity. Neither the total length nor its product is an extra hypothesis. -/
theorem sign_rows_mod_four (r : ℕ) (len : ℕ → ℕ) (f : ℕ → ℕ → ℤ)
    (hsq : ∀ i < r, ∀ j < len i, f i j ^ 2 = 1) :
    Int.ModEq 4 (∑ i ∈ Finset.range r, ∑ j ∈ Finset.range (len i), f i j)
      ((∑ i ∈ Finset.range r, (len i : ℤ)) - 1 +
        ∏ i ∈ Finset.range r, ∏ j ∈ Finset.range (len i), f i j) := by
  have h := sign_sum_mod_four ((Finset.range r).sigma (fun i => Finset.range (len i)))
    (fun q => f q.1 q.2) (by
      intro q hq
      simp only [Finset.mem_sigma, Finset.mem_range] at hq
      exact hsq q.1 hq.1 q.2 hq.2)
  simpa only [Finset.sum_sigma, Finset.prod_sigma, Finset.card_sigma,
    Nat.cast_sum, Finset.card_range] using h

/-- The lengths of the nested central intervals add to m(m+1). -/
theorem central_interval_length (m : ℕ) :
    (∑ i ∈ Finset.range m, ((2 * (m - i) : ℕ) : ℤ)) = (m : ℤ) * (m + 1) := by
  by_cases hm : m = 0
  · simp [hm]
  have hsum := Finset.sum_range_id_mul_two m
  have hz : (∑ i ∈ Finset.range m, (i : ℤ)) * 2 = (m : ℤ) * (m - 1) := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hsum
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_one] using h
  rw [← Finset.sum_range_reflect (fun i => ((2 * (m - i) : ℕ) : ℤ)) m]
  have heq : (∑ i ∈ Finset.range m, ((2 * (m - (m - 1 - i)) : ℕ) : ℤ)) =
      2 * (∑ i ∈ Finset.range m, (i : ℤ)) + 2 * m := by
    calc
      _ = ∑ i ∈ Finset.range m, (2 * (i : ℤ) + 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have he : m - (m - 1 - i) = i + 1 := by omega
        rw [he]
        push_cast
        ring
      _ = _ := by simp [Finset.sum_add_distrib, ← Finset.mul_sum] <;> ring
  rw [heq]
  nlinarith

/-- The sum of the central half-interval quotients modulo two, kept integrally
modulo four. This supplies the parity correction in both energy arguments. -/
theorem central_half_sum_mod_four (a : ℕ → ℤ) (m : ℕ)
    (hsq : ∀ j, 1 ≤ j → j ≤ 2 * m + 1 → a j ^ 2 = 1) :
    Int.ModEq 4
      (2 * (∑ i ∈ Finset.range m, oddB a (2 * m + 1) (i + 1)))
      ((m : ℤ) * (m + 1) - 1 + ∏ i ∈ Finset.range m, intervalProduct a m i) := by
  have h := sign_rows_mod_four m (fun i => 2 * (m - i))
    (fun i j => a (i + j + 1)) (by
      intro i hi j hj
      apply hsq _ (by omega) (by omega))
  have heq : (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range (2 * (m - i)), a (i + j + 1)) =
      2 * (∑ i ∈ Finset.range m, oddB a (2 * m + 1) (i + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hb := twice_oddB a m (i + 1) (by omega) (by omega) hsq
    have hs := Finset.sum_range_add (fun j => a (j + 1)) i (2 * (m - i))
    have harg : i + 2 * (m - i) = 2 * m + 1 - (i + 1) := by omega
    rw [harg] at hs
    simp only [Nat.add_sub_cancel] at hb
    change partialSum a (2 * m + 1 - (i + 1)) = partialSum a i + _ at hs
    linarith
  simpa only [heq, central_interval_length, intervalProduct] using h

/-- Symmetry of the even quotient vector, including both zero endpoints. -/
theorem evenB_square_sum (a : ℕ → ℤ) (m : ℕ) (hc : partialSum a (2 * m) = 0) :
    (∑ i ∈ Finset.range (2 * m), evenB a (2 * m) (i + 1) ^ 2) =
      2 * (∑ i ∈ Finset.range m, evenB a (2 * m) i ^ 2) + partialSum a m ^ 2 := by
  have hzero : evenB a (2 * m) 0 = 0 := by
    simp only [evenB, Nat.sub_zero, show partialSum a 0 = 0 by simp [partialSum],
      hc, add_zero, neg_zero, Int.zero_ediv]
  have h := sum_odd_reflection (fun i => evenB a (2 * m) i ^ 2) m
    (fun i hi => by rw [evenB_reflect a (2 * m) i (by omega)])
  rw [Finset.sum_range_succ', hzero, zero_pow two_ne_zero, add_zero,
    evenB_midpoint, neg_sq] at h
  exact h

/-- The even quotient differs from the central quotient by a negative prefix. -/
theorem evenB_add_central (a : ℕ → ℤ) (m i : ℕ) (hi : i ≤ m)
    (hsq : ∀ j, 1 ≤ j → j ≤ 2 * m + 1 → a j ^ 2 = 1) :
    evenB a (2 * m) i + oddB a (2 * m + 1) (i + 1) = -partialSum a i := by
  have he := twice_evenB a m i (by omega) (fun j hj hn => hsq j hj (by omega))
  have ho := twice_oddB a m (i + 1) (by omega) (by omega) hsq
  have harg : 2 * m + 1 - (i + 1) = 2 * m - i := by omega
  simp only [harg, Nat.add_sub_cancel] at ho
  linarith

/-- The sum of prefixes has the parity of the corresponding triangular number. -/
theorem twice_prefix_sum_mod_four (a : ℕ → ℤ) (m : ℕ)
    (hsq : ∀ j, 1 ≤ j → j ≤ m → a j ^ 2 = 1) :
    Int.ModEq 4 (2 * (∑ i ∈ Finset.range m, partialSum a i)) ((m : ℤ) * (m - 1)) := by
  by_cases hm : m = 0
  · simp [hm]
  have hp : ∀ i ∈ Finset.range m, Int.ModEq 2 (partialSum a i) (i : ℤ) := by
    intro i hi
    exact prefix_mod_two a i (fun j hj hn => hsq j hj (by have := Finset.mem_range.mp hi; omega))
  have h := Int.ModEq.sum hp
  have hz : (∑ i ∈ Finset.range m, (i : ℤ)) * 2 = (m : ℤ) * (m - 1) := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) (Finset.sum_range_id_mul_two m)
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_one] using h
  have hmul := h.mul_left' (c := 2)
  have hz' : 2 * (∑ i ∈ Finset.range m, (i : ℤ)) = (m : ℤ) * (m - 1) := by
    nlinarith [hz]
  simpa only [show (2 : ℤ) * 2 = 4 by norm_num, hz'] using hmul

/-- Squaring an integer preserves its parity, also under finite summation. -/
theorem square_sum_mod_two (b : ℕ → ℤ) (m : ℕ) :
    Int.ModEq 2 (∑ i ∈ Finset.range m, b i ^ 2) (∑ i ∈ Finset.range m, b i) := by
  apply Int.ModEq.sum
  intro i _
  have hi : b i % 2 = 0 ∨ b i % 2 = 1 := by omega
  rcases hi with hi | hi <;> simp [Int.ModEq, pow_two, Int.mul_emod, hi]

end D5.S3.Arith.CharacterSums.QuadraticPrefixParity
