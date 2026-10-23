/- GID: D5/S3/Factorization/TwoDenseDivisorBlocksPalindrome
   generality: G
   mirror-B: D5/B/S3/Factorization/TwoDenseDivisorBlocksPalindrome
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The maximal two-dense divisor blocks form a palindromic composition. -/

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.List.SplitBy
import D5.S1.Words.AssociatedMersenne.CircularWords
import Mathlib.Tactic.Linarith

namespace D5.S3.Factorization.TwoDenseDivisorBlocksPalindrome

/-- Block lengths of a list cut wherever the next entry exceeds twice the previous one. -/
def twoDenseBlockLengths (l : List ℕ) : List ℕ :=
  (l.splitBy (fun a b => decide (b ≤ 2 * a))).map List.length

/-- Row n of OEIS A384222, using the increasing first coordinates of the divisor pairs. -/
def row (n : ℕ) : List ℕ :=
  twoDenseBlockLengths (n.divisorsAntidiagonalList.map Prod.fst)

private theorem divisor_list_finset (n : ℕ) :
    (n.divisorsAntidiagonalList.map Prod.fst).toFinset = n.divisors := by
  rw [← Nat.image_fst_divisorsAntidiagonal, ← Nat.toFinset_divisorsAntidiagonalList]
  ext d
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]

/-- The block lengths sum to the number of positive divisors. -/
theorem row_sum (n : ℕ) (_hn : 0 < n) : (row n).sum = n.divisors.card := by
  rw [row, twoDenseBlockLengths, ← List.length_flatten, List.flatten_splitBy]
  rw [← divisor_list_finset n, List.toFinset_card_of_nodup]
  exact Nat.sortedLT_map_fst_divisorsAntidiagonalList.nodup

private theorem complement_reverse (n : ℕ) :
    (n.divisorsAntidiagonalList.map Prod.fst).reverse.map (n / ·) =
      n.divisorsAntidiagonalList.map Prod.fst := by
  rw [← List.map_reverse, Nat.reverse_divisorsAntidiagonalList, List.map_map, List.map_map]
  apply List.map_congr_left
  intro p hp
  obtain ⟨hp, hn⟩ := Nat.mem_divisorsAntidiagonalList.mp hp
  have hp0 : p.2 ≠ 0 := by
    intro h
    simp [h] at hp
    exact hn hp.symm
  dsimp
  exact Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hp0) hp.symm

private theorem complement_dense (n a b : ℕ) (hn : 0 < n)
    (ha : a ∈ n.divisors) (hb : b ∈ n.divisors) :
    (n / a ≤ 2 * (n / b)) ↔ b ≤ 2 * a := by
  have ha0 : 0 < a := Nat.pos_of_mem_divisors ha
  have hb0 : 0 < n / b := Nat.div_pos
    (Nat.le_of_dvd hn (Nat.mem_divisors.mp hb).1) (Nat.pos_of_mem_divisors hb)
  have haeq : a * (n / a) = n := Nat.mul_div_cancel' (Nat.mem_divisors.mp ha).1
  have hbeq : b * (n / b) = n := Nat.mul_div_cancel' (Nat.mem_divisors.mp hb).1
  constructor
  · intro h
    have := Nat.mul_le_mul_left a h
    nlinarith
  · intro h
    have := Nat.mul_le_mul_right (n / b) h
    nlinarith

/-- OEIS A384222 Conjecture 1: every positive-indexed row is palindromic.
Together with row_sum and the nonempty blocks of splitBy, it is a composition of tau(n). -/
theorem row_palindrome (n : ℕ) (hn : 0 < n) : (row n).reverse = row n := by
  have h := D5.S1.Words.AssociatedMersenne.CircularWords.split_reverse_map (fun a b : ℕ => decide (b ≤ 2 * a))
    (fun a b : ℕ => decide (b ≤ 2 * a)) (n / ·)
    (n.divisorsAntidiagonalList.map Prod.fst) (by
      intro a ha b hb
      apply Bool.decide_congr
      apply complement_dense n a b hn
      · rw [← divisor_list_finset n, List.mem_toFinset]; exact ha
      · rw [← divisor_list_finset n, List.mem_toFinset]; exact hb)
  rw [complement_reverse] at h
  have hm := congrArg (List.map List.length) h
  simpa [row, twoDenseBlockLengths, List.map_reverse, List.map_map, Function.comp_def]
    using hm.symm

#print axioms row_sum
#print axioms row_palindrome

end D5.S3.Factorization.TwoDenseDivisorBlocksPalindrome
