/- GID: D5/S3/Factorization/A380056
   generality: G
   mirror-B: D5/B/S3/Factorization/A380056
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Hanna's second A380056 conjecture follows from its finite sum and Euler residues. -/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

open scoped BigOperators
open Finset

namespace D5.S3.Factorization.A380056

/-- A fourth-root filter evaluates the entire residue-two binomial sum modulo five. -/
theorem binomial_residue_two (n : ℕ) (hn : 1 ≤ n) :
    (∑ j ∈ range (4 * n + 1),
      if j % 4 = 2 then ((4 * n).choose j : ZMod 5) else 0) = 1 := by
  have hfilter (j : ℕ) :
      (if j % 4 = 2 then (1 : ZMod 5) else 0) =
        4 * (1 ^ j + (-1) ^ j - 2 ^ j - 3 ^ j) := by
    rw [pow_eq_pow_mod j (by decide : (-1 : ZMod 5) ^ 4 = 1),
      pow_eq_pow_mod j (by decide : (2 : ZMod 5) ^ 4 = 1),
      pow_eq_pow_mod j (by decide : (3 : ZMod 5) ^ 4 = 1)]
    have hj : j % 4 < 4 := Nat.mod_lt _ (by decide)
    interval_cases h : j % 4 <;> norm_num <;> decide
  have hbinom (x : ZMod 5) :
      (∑ j ∈ range (4 * n + 1), x ^ j * ((4 * n).choose j : ZMod 5)) =
        (x + 1) ^ (4 * n) := by
    simpa only [one_pow, mul_one] using (add_pow x 1 (4 * n)).symm
  calc
    _ = ∑ j ∈ range (4 * n + 1),
        4 * (1 ^ j + (-1) ^ j - 2 ^ j - 3 ^ j) *
          ((4 * n).choose j : ZMod 5) := by
      apply sum_congr rfl
      intro j _
      rw [← hfilter]
      split_ifs <;> simp
    _ = 4 * ((1 + 1) ^ (4 * n) + (-1 + 1) ^ (4 * n) -
        (2 + 1) ^ (4 * n) - (3 + 1) ^ (4 * n)) := by
      simp only [mul_assoc, add_mul, sub_mul, ← mul_sum, sum_add_distrib,
        sum_sub_distrib, hbinom]
    _ = 1 := by
      have hpos : 4 * n ≠ 0 := by omega
      norm_num [hpos, pow_mul]
      rw [show (16 : ZMod 5) = 1 from by decide,
        show (81 : ZMod 5) = 1 from by decide,
        show (256 : ZMod 5) = 1 from by decide, zero_pow (by omega : n ≠ 0)]
      norm_num
      decide

/-- The endpoint and all odd Euler-index terms cancel collectively modulo five. -/
theorem surviving_sum (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Icc 1 (2 * n),
      if k = 2 * n ∨ (2 * n - k) % 2 = 1 then
        ((4 * n).choose (2 * k) : ZMod 5) * 4 ^ (2 * n - k) else 0) = 0 := by
  have hodd : (∑ k ∈ Icc 1 (2 * n),
      if k % 2 = 1 then ((4 * n).choose (2 * k) : ZMod 5) else 0) = 1 := by
    rw [← binomial_residue_two n hn]
    simp only [← sum_filter]
    apply sum_bij (fun k _ => 2 * k)
    · intro k hk
      simp only [mem_filter, mem_Icc, mem_range] at hk ⊢
      omega
    · intro k hk l hl heq
      omega
    · intro j hj
      simp only [mem_filter, mem_range] at hj
      refine ⟨j / 2, ?_, ?_⟩
      · simp only [mem_filter, mem_Icc]
        omega
      · omega
    · intro k _
      rfl
  have hterm (k : ℕ) (hk : k ∈ Icc 1 (2 * n)) :
      (if k = 2 * n ∨ (2 * n - k) % 2 = 1 then
        ((4 * n).choose (2 * k) : ZMod 5) * 4 ^ (2 * n - k) else 0) =
      (if k = 2 * n then 1 else 0) -
        (if k % 2 = 1 then ((4 * n).choose (2 * k) : ZMod 5) else 0) := by
    obtain ⟨hkpos, hkle⟩ := mem_Icc.mp hk
    by_cases heq : k = 2 * n
    · subst k
      simp [show 2 * (2 * n) = 4 * n by omega]
    · have hpar : (2 * n - k) % 2 = k % 2 := by omega
      by_cases hmod : k % 2 = 1
      · rw [if_pos (Or.inr (hpar.trans hmod)), if_neg heq, if_pos hmod,
          pow_eq_pow_mod _ (by decide : (4 : ZMod 5) ^ 2 = 1), hpar, hmod]
        simp [show (4 : ZMod 5) = -1 from by decide]
      · simp [heq, hpar, hmod]
  rw [sum_congr rfl hterm, sum_sub_distrib, hodd]
  simp [show 1 ≤ 2 * n by omega]

/-- Hanna's second conjecture, conditional only on the printed sum and Euler-number residues. -/
theorem a380056_div_five
    (a E : ℕ → ℕ)
    (hformula : ∀ m : ℕ, 1 ≤ m →
      a (2 * m) = ∑ k ∈ Icc 1 m,
        (2 * m).choose (2 * k) * E (m - k) * 4 ^ (m - k))
    (hE0 : E 0 = 1)
    (hE5 : ∀ r : ℕ, 0 < r → E r % 5 = if r % 2 = 1 then 1 else 0) :
    ∀ n : ℕ, 1 ≤ n → 5 ∣ a (4 * n) := by
  intro n hn
  apply (ZMod.natCast_eq_zero_iff (a (4 * n)) 5).mp
  have hf := hformula (2 * n) (by omega)
  rw [show 2 * (2 * n) = 4 * n by omega] at hf
  rw [hf]
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  rw [← surviving_sum n hn]
  apply sum_congr rfl
  intro k hk
  by_cases heq : k = 2 * n
  · subst k
    simp [hE0]
  · have hpos : 0 < 2 * n - k := by
      have := mem_Icc.mp hk
      omega
    have heuler : (E (2 * n - k) : ZMod 5) =
        if (2 * n - k) % 2 = 1 then 1 else 0 := by
      rw [← ZMod.natCast_mod (E (2 * n - k)) 5, hE5 _ hpos]
      split_ifs <;> rfl
    rw [heuler]
    by_cases hmod : (2 * n - k) % 2 = 1 <;> simp [heq, hmod]

#print axioms binomial_residue_two
#print axioms surviving_sum
#print axioms a380056_div_five

end D5.S3.Factorization.A380056
