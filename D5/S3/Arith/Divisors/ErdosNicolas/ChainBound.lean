/- GID: D5/S3/Arith/Divisors/ErdosNicolas/ChainBound
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/ErdosNicolas/ChainBound
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: Two- and three-term estimates summed over prime-power divisor chains. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Basic
import D5.S3.Arith.Divisors.ErdosNicolas.DivisorBlocks
import Mathlib.Data.Nat.Factorization.Basic

/-! Divisor averages from adjacent estimates on multiplicative chains. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

open Finset

/-- Every chain of length at least two is bounded using only adjacent pairs and triples. -/
private theorem chain_sum_le (u : ℕ → ℚ) (c : ℚ) {h : ℕ}
    (h₂ : ∀ i, i + 1 < h → u i + u (i + 1) ≤ 2 * c)
    (h₃ : ∀ i, i + 2 < h → u i + u (i + 1) + u (i + 2) ≤ 3 * c)
    (hh : 2 ≤ h) :
    ∑ i ∈ range h, u i ≤ (h : ℚ) * c := by
  induction h using Nat.strong_induction_on generalizing u with
  | h h ih =>
    by_cases he₂ : h = 2
    · subst h
      simpa [sum_range_succ] using h₂ 0 (by omega)
    by_cases he₃ : h = 3
    · subst h
      simpa [sum_range_succ, add_assoc] using h₃ 0 (by omega)
    have hh₄ : 4 ≤ h := by omega
    have hrec := ih (h - 2) (by omega) (fun i => u (2 + i))
      (fun i hi => by simpa [Nat.add_assoc] using h₂ (2 + i) (by omega))
      (fun i hi => by simpa [Nat.add_assoc] using h₃ (2 + i) (by omega)) (by omega)
    have heq : h = 2 + (h - 2) := by omega
    rw [heq, sum_range_add]
    have hcast : ((h - 2 : ℕ) : ℚ) = (h : ℚ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ h)]
      norm_num
    have hfirst : (∑ i ∈ range 2, u i) ≤ 2 * c := by
      simpa [sum_range_succ] using h₂ 0 (by omega)
    have hshift : (∑ i ∈ range (h - 2), u (2 + i)) ≤
        ((h : ℚ) - 2) * c := by simpa [hcast] using hrec
    simp only [Nat.cast_add, Nat.cast_ofNat]
    rw [hcast]
    linarith

/-- Explicit prime-power coordinates for the sum of an arbitrary divisor weight. -/
private theorem sum_divisors_prime_power_mul (q a m : ℕ) (hq : q.Prime) (hqm : ¬q ∣ m)
    (φ : ℕ → ℚ) :
    (∑ d ∈ (q ^ a * m).divisors, φ d) =
      ∑ d ∈ m.divisors, ∑ i ∈ range (a + 1), φ (q ^ i * d) := by
  induction a generalizing φ with
  | zero => simp
  | succ a ih =>
    rw [prime_power_divisors_partition hq (Nat.succ_pos a),
      sum_union (prime_power_divisor_blocks_disjoint hqm)]
    simp only [Nat.succ_sub_one, sum_image
      (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hq.pos h)]
    rw [ih (fun d => φ (q * d))]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro d _
    conv_rhs => rw [sum_range_succ']
    simp only [pow_zero, one_mul]
    rw [add_comm]
    congr 1
    apply sum_congr rfl
    intro i _
    rw [pow_succ']
    congr 1
    ring

/-- Pair and triple orbit bounds control the complete divisor average. -/
private theorem divisor_chain_average {q n : ℕ} (hq : q.Prime) (hqn : q ∣ n)
    (φ : ℕ → ℚ) (c : ℚ)
    (h₂ : ∀ r, q * r ∣ n → φ r + φ (q * r) ≤ 2 * c)
    (h₃ : ∀ r, q ^ 2 * r ∣ n → φ r + φ (q * r) + φ (q ^ 2 * r) ≤ 3 * c) :
    (∑ d ∈ n.divisors, φ d) ≤ c * (n.divisors.card : ℚ) := by
  by_cases hn : n = 0
  · simp [hn]
  obtain ⟨a, m, hqm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q hq.ne_one
  have ha : 0 < a := by
    by_contra h
    have heq : a = 0 := by omega
    simp only [heq, pow_zero, one_mul] at hqn
    exact hqm hqn
  rw [sum_divisors_prime_power_mul q a m hq hqm]
  calc
    _ ≤ ∑ d ∈ m.divisors, ((a + 1 : ℕ) : ℚ) * c := by
      apply sum_le_sum
      intro d hd
      have hdiv (i : ℕ) (hi : i ≤ a) : q ^ i * d ∣ q ^ a * m :=
        Nat.mul_dvd_mul (pow_dvd_pow q hi) (Nat.dvd_of_mem_divisors hd)
      apply chain_sum_le (fun i => φ (q ^ i * d)) c
      · intro i hi
        simpa [pow_succ', mul_assoc] using h₂ (q ^ i * d) (by
          simpa [pow_succ', mul_assoc] using hdiv (i + 1) (by omega))
      · intro i hi
        simpa [pow_add, pow_succ', mul_assoc] using h₃ (q ^ i * d) (by
          simpa [pow_add, mul_assoc, mul_left_comm] using hdiv (i + 2) (by omega))
      · omega
    _ = c * ((q ^ a * m).divisors.card : ℚ) := by
      simp only [sum_const, nsmul_eq_mul]
      rw [card_divisors_prime_power_mul hq hqm]
      push_cast
      ring

/-- Only residues prime to `p` need pair and triple tests for a `p`-free integer. -/
theorem divisor_chain_average_coprime {p q n : ℕ}
    (hq : n ≠ 0 → q = 1 ∨ q.Prime) (hqn : q ∣ n) (hpn : n ≠ 0 → ¬p ∣ n) (φ : ℕ → ℚ) (c : ℚ)
    (h₂ : ∀ r, q * r ∈ n.divisors → ¬p ∣ r → φ r + φ (q * r) ≤ 2 * c)
    (h₃ : ∀ r, q ^ 2 * r ∈ n.divisors → ¬p ∣ r → φ r + φ (q * r) + φ (q ^ 2 * r) ≤ 3 * c) :
    (∑ d ∈ n.divisors, φ d) ≤ c * (n.divisors.card : ℚ) := by
  by_cases hn : n = 0
  · simp [hn]
  have hpn' := hpn hn
  rcases hq hn with rfl | hq
  · calc
      _ ≤ ∑ _d ∈ n.divisors, c := by
        apply sum_le_sum
        intro d hd
        have he := h₂ d (by simpa using hd)
          (fun h => hpn' (h.trans (Nat.dvd_of_mem_divisors hd)))
        simp only [one_mul] at he
        linarith
      _ = _ := by simp [mul_comm]
  · apply divisor_chain_average hq hqn φ c
    · intro r hr
      exact h₂ r (Nat.mem_divisors.mpr ⟨hr, hn⟩)
        (fun h => hpn' (h.trans ((dvd_mul_left r q).trans hr)))
    · intro r hr
      exact h₃ r (Nat.mem_divisors.mpr ⟨hr, hn⟩)
        (fun h => hpn' (h.trans ((dvd_mul_left r (q ^ 2)).trans hr)))

/-- Every chain of length at least two is bounded using only adjacent pairs and triples. -/
private theorem chain_sum_lt (u : ℕ → ℚ) (c : ℚ) {h : ℕ}
    (h₂ : ∀ i, i + 1 < h → u i + u (i + 1) < 2 * c)
    (h₃ : ∀ i, i + 2 < h → u i + u (i + 1) + u (i + 2) < 3 * c)
    (hh : 2 ≤ h) :
    ∑ i ∈ range h, u i < (h : ℚ) * c := by
  induction h using Nat.strong_induction_on generalizing u with
  | h h ih =>
    by_cases he₂ : h = 2
    · subst h
      simpa [sum_range_succ] using h₂ 0 (by omega)
    by_cases he₃ : h = 3
    · subst h
      simpa [sum_range_succ, add_assoc] using h₃ 0 (by omega)
    have hh₄ : 4 ≤ h := by omega
    have hrec := ih (h - 2) (by omega) (fun i => u (2 + i))
      (fun i hi => by simpa [Nat.add_assoc] using h₂ (2 + i) (by omega))
      (fun i hi => by simpa [Nat.add_assoc] using h₃ (2 + i) (by omega)) (by omega)
    have heq : h = 2 + (h - 2) := by omega
    rw [heq, sum_range_add]
    have hcast : ((h - 2 : ℕ) : ℚ) = (h : ℚ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ h)]
      norm_num
    have hfirst : (∑ i ∈ range 2, u i) < 2 * c := by
      simpa [sum_range_succ] using h₂ 0 (by omega)
    have hshift : (∑ i ∈ range (h - 2), u (2 + i)) <
        ((h : ℚ) - 2) * c := by simpa [hcast] using hrec
    simp only [Nat.cast_add, Nat.cast_ofNat]
    rw [hcast]
    linarith

/-- Pair and triple orbit bounds control the complete divisor average. -/
theorem divisor_chain_average_lt {q n : ℕ} (hq : q = 1 ∨ q.Prime) (hqn : q ∣ n) (hn : n ≠ 0)
    (φ : ℕ → ℚ) (c : ℚ)
    (h₂ : ∀ r, q * r ∣ n → φ r + φ (q * r) < 2 * c)
    (h₃ : ∀ r, q ^ 2 * r ∣ n → φ r + φ (q * r) + φ (q ^ 2 * r) < 3 * c) :
    (∑ d ∈ n.divisors, φ d) < c * (n.divisors.card : ℚ) := by
  rcases hq with rfl | hq
  · calc
      _ < ∑ _d ∈ n.divisors, c := by
        apply sum_lt_sum_of_nonempty ⟨1, Nat.one_mem_divisors.mpr hn⟩
        intro d hd
        have he := h₂ d (by simpa using Nat.dvd_of_mem_divisors hd)
        simp only [one_mul] at he
        linarith
      _ = _ := by simp [mul_comm]
  ·
    obtain ⟨a, m, hqm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q hq.ne_one
    have ha : 0 < a := by
      by_contra h
      have heq : a = 0 := by omega
      simp only [heq, pow_zero, one_mul] at hqn
      exact hqm hqn
    rw [sum_divisors_prime_power_mul q a m hq hqm]
    calc
      _ < ∑ d ∈ m.divisors, ((a + 1 : ℕ) : ℚ) * c := by
        apply sum_lt_sum_of_nonempty
          ⟨1, Nat.one_mem_divisors.mpr (by
            intro hm
            simp [hm] at hn)⟩
        intro d hd
        have hdiv (i : ℕ) (hi : i ≤ a) : q ^ i * d ∣ q ^ a * m :=
          Nat.mul_dvd_mul (pow_dvd_pow q hi) (Nat.dvd_of_mem_divisors hd)
        apply chain_sum_lt (fun i => φ (q ^ i * d)) c
        · intro i hi
          simpa [pow_succ', mul_assoc] using h₂ (q ^ i * d) (by
            simpa [pow_succ', mul_assoc] using hdiv (i + 1) (by omega))
        · intro i hi
          simpa [pow_add, pow_succ', mul_assoc] using h₃ (q ^ i * d) (by
            simpa [pow_add, mul_assoc, mul_left_comm] using hdiv (i + 2) (by omega))
        · omega
      _ = c * ((q ^ a * m).divisors.card : ℚ) := by
        simp only [sum_const, nsmul_eq_mul]
        rw [card_divisors_prime_power_mul hq hqm]
        push_cast
        ring

#print axioms chain_sum_le
#print axioms sum_divisors_prime_power_mul
#print axioms divisor_chain_average
#print axioms divisor_chain_average_coprime

end D5.S3.Arith.ErdosNicolas
