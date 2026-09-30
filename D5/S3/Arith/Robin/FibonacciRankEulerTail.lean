/- GID: D5/S3/Arith/Robin/FibonacciRankEulerTail
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/FibonacciRankEulerTail
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Primes with one Fibonacci entry index have a harmonic Euler logarithm bound. -/

import D5.S3.Arith.FibonacciRank
import Mathlib.NumberTheory.Harmonic.Bounds

namespace D5.S3.Arith.Robin.FibonacciRankEulerTail

open Finset
open D5.S3.Arith.FibonacciRank

/-- All prime factors whose first positive Fibonacci zero occurs at `d`. -/
noncomputable def rankBucket (d : ℕ) : Finset ℕ := by
  classical
  exact (Nat.fib d).primeFactors.filter fun p =>
    ∀ k ∈ Finset.Ico 1 d, ¬ p ∣ Nat.fib k

/-- The complete bucket, without a bound on its primes, has a harmonic
Euler logarithm bound and hence an explicit logarithmic tail bound. -/
theorem result (d : ℕ) (hd : 5 < d) :
    (∑ p ∈ rankBucket d, Real.log ((p : ℝ) / ((p : ℝ) - 1))) ≤
        6 * (harmonic d : ℝ) / d ∧
      6 * (harmonic d : ℝ) / d ≤ 6 * (1 + Real.log d) / d := by
  classical
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by positivity
  have hfib0 : 0 < Nat.fib d := Nat.fib_pos.mpr hd0
  let s := rankBucket d
  let f : ℕ → ℝ := fun p => Real.log ((p : ℝ) / ((p : ℝ) - 1))
  have hs : s ⊆ (Nat.fib d).primeFactors := by
    intro p hp
    simp only [s, rankBucket, Finset.mem_filter] at hp
    exact hp.1
  have hprime (p : ℕ) (hp : p ∈ s) : p.Prime :=
    Nat.prime_of_mem_primeFactors (hs hp)
  have hzero (p : ℕ) (hp : p ∈ s) : p ∣ Nat.fib d :=
    Nat.dvd_of_mem_primeFactors (hs hp)
  have hmin (p : ℕ) (hp : p ∈ s) (k : ℕ) (hk : 0 < k)
      (hpk : p ∣ Nat.fib k) : d ≤ k := by
    by_contra h
    simp only [s, rankBucket, Finset.mem_filter] at hp
    have ht := hp.2 k (Finset.mem_Ico.mpr (by omega))
    exact ht hpk
  have hcong (p : ℕ) (hp : p ∈ s) : d ∣ p - 1 ∨ d ∣ p + 1 := by
    have hp5 : p ≠ 5 := by
      intro heq
      have ht := hmin p hp 5 (by decide)
      have hfive : p ∣ Nat.fib 5 := by norm_num [heq, Nat.fib_add_two]
      have := ht hfive
      omega
    have h := fibonacci_rank_dvd_prime_bound (hprime p hp) hp5 hd0
      (hzero p hp) (hmin p hp)
    split_ifs at h with hsign
    · exact Or.inl h
    · exact Or.inr h
  have hfib : ∀ n : ℕ, Nat.fib n < 2 ^ n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => norm_num
    | one => norm_num
    | more n ih ih' =>
      rw [Nat.fib_add_two, pow_add]
      norm_num
      have hh : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
      nlinarith
  have hcard : s.card < d := by
    have hlo : 2 ^ s.card ≤ ∏ p ∈ s, p :=
      Finset.pow_card_le_prod s id 2 (fun p hp => (hprime p hp).two_le)
    have hdiv : (∏ p ∈ s, p) ∣ Nat.fib d :=
      dvd_trans (Finset.prod_dvd_prod_of_subset _ _ id hs) (Nat.prod_primeFactors_dvd _)
    have hpow : 2 ^ s.card < 2 ^ d :=
      lt_of_le_of_lt (hlo.trans (Nat.le_of_dvd hfib0 hdiv)) (hfib d)
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hpow
  have flog (p : ℕ) (hp : 2 ≤ p) :
      0 ≤ f p ∧ f p ≤ 1 / ((p : ℝ) - 1) := by
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
    have hden : 0 < (p : ℝ) - 1 := by linarith
    have hratio : 0 < (p : ℝ) / ((p : ℝ) - 1) := div_pos (by linarith) hden
    constructor
    · apply Real.log_nonneg
      exact (le_div_iff₀ hden).mpr (by linarith)
    · calc
        f p ≤ (p : ℝ) / ((p : ℝ) - 1) - 1 := Real.log_le_sub_one_of_pos hratio
        _ = 1 / ((p : ℝ) - 1) := by field_simp; ring
  let ks := Finset.Icc 1 d
  let plus := ks.image fun k => k * d + 1
  let minus := ks.image fun k => k * d - 1
  let small := s.filter fun p => p ≤ d * d
  let large := s.filter fun p => ¬ p ≤ d * d
  have hsmall : small ⊆ plus ∪ minus := by
    intro p hp
    obtain ⟨hp, hpd⟩ := Finset.mem_filter.mp hp
    have hp2 := (hprime p hp).two_le
    rcases hcong p hp with h | h
    · obtain ⟨k, hk⟩ := h
      rw [Nat.mul_comm] at hk
      have heq : p = k * d + 1 := by omega
      have hk1 : 1 ≤ k := by nlinarith
      have hkd : k ≤ d := by nlinarith
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk1, hkd⟩, heq.symm⟩
    · obtain ⟨k, hk⟩ := h
      rw [Nat.mul_comm] at hk
      have heq : p = k * d - 1 := by omega
      have hk1 : 1 ≤ k := by nlinarith
      have hkd : k ≤ d := by nlinarith
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk1, hkd⟩, heq.symm⟩
  have htwop (p : ℕ) (hp : p ∈ plus ∪ minus) : 2 ≤ p := by
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
      have hk1 := (Finset.mem_Icc.mp hk).1
      nlinarith
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
      have hk1 := (Finset.mem_Icc.mp hk).1
      have : 3 ≤ k * d := by nlinarith
      omega
  have hchannel (k : ℕ) (hk : k ∈ ks) :
      f (k * d + 1) ≤ 2 / ((k : ℝ) * d) ∧
      f (k * d - 1) ≤ 2 / ((k : ℝ) * d) := by
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hkd : 4 ≤ k * d := by nlinarith
    have hkdR : (4 : ℝ) ≤ (k : ℝ) * d := by exact_mod_cast hkd
    have hkd0 : 0 < (k : ℝ) * d := by linarith
    constructor
    · have hp : 2 ≤ k * d + 1 := by omega
      calc
        f (k * d + 1) ≤ 1 / ((k * d + 1 : ℕ) - 1 : ℝ) := (flog _ hp).2
        _ ≤ 2 / ((k : ℝ) * d) := by
          push_cast
          rw [add_sub_cancel_right]
          exact div_le_div_of_nonneg_right (by norm_num) hkd0.le
    · have hp : 2 ≤ k * d - 1 := by omega
      calc
        f (k * d - 1) ≤ 1 / ((k * d - 1 : ℕ) - 1 : ℝ) := (flog _ hp).2
        _ ≤ 2 / ((k : ℝ) * d) := by
          rw [Nat.cast_sub (by omega : 1 ≤ k * d)]
          push_cast
          apply (div_le_div_iff₀ (by linarith : 0 < (k : ℝ) * d - 1 - 1) hkd0).mpr
          nlinarith
  have hsumplus : (∑ p ∈ plus, f p) ≤ ∑ k ∈ ks, 2 / ((k : ℝ) * d) := by
    rw [Finset.sum_image]
    · exact Finset.sum_le_sum fun k hk => (hchannel k hk).1
    · intro k hk l hl heq
      nlinarith
  have hsumminus : (∑ p ∈ minus, f p) ≤ ∑ k ∈ ks, 2 / ((k : ℝ) * d) := by
    rw [Finset.sum_image]
    · exact Finset.sum_le_sum fun k hk => (hchannel k hk).2
    · intro k hk l hl heq
      change k * d - 1 = l * d - 1 at heq
      have hk1 := (Finset.mem_Icc.mp hk).1
      have hl1 := (Finset.mem_Icc.mp hl).1
      have hka : 1 ≤ k * d := by nlinarith
      have hla : 1 ≤ l * d := by nlinarith
      have : k * d = l * d := by omega
      nlinarith
  have hharmonic : (∑ k ∈ ks, 2 / ((k : ℝ) * d)) = 2 * (harmonic d : ℝ) / d := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    dsimp [ks]
    simp_rw [div_mul_eq_div_div, div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hsmallbound : (∑ p ∈ small, f p) ≤ 4 * (harmonic d : ℝ) / d := by
    calc
      _ ≤ ∑ p ∈ plus ∪ minus, f p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsmall (fun p hp _ => (flog p (htwop p hp)).1)
      _ ≤ (∑ p ∈ plus, f p) + ∑ p ∈ minus, f p :=
        by
          have hh := Finset.sum_union_inter (s₁ := plus) (s₂ := minus) (f := f)
          have hh0 : 0 ≤ ∑ p ∈ plus ∩ minus, f p :=
            Finset.sum_nonneg fun p hp =>
              (flog p (htwop p (Finset.mem_union_left _ (Finset.mem_inter.mp hp).1))).1
          linarith
      _ ≤ 2 * (∑ k ∈ ks, 2 / ((k : ℝ) * d)) := by linarith
      _ = _ := by rw [hharmonic]; ring
  have hlarge : (∑ p ∈ large, f p) ≤ 1 / (d : ℝ) := by
    have hterm (p : ℕ) (hp : p ∈ large) : f p ≤ 1 / ((d : ℝ) * d) := by
      obtain ⟨hp, hpd⟩ := Finset.mem_filter.mp hp
      have hn : d * d ≤ p - 1 := by omega
      have hp1 := (hprime p hp).two_le
      apply (flog p hp1).2.trans
      apply one_div_le_one_div_of_le (by positivity : 0 < (d : ℝ) * d)
      have hh : (d : ℝ) * d + 1 ≤ p := by exact_mod_cast (show d * d + 1 ≤ p by omega)
      linarith
    calc
      _ ≤ ∑ _p ∈ large, 1 / ((d : ℝ) * d) := Finset.sum_le_sum hterm
      _ = (large.card : ℝ) / ((d : ℝ) * d) := by simp [div_eq_mul_inv]
      _ ≤ (d : ℝ) / ((d : ℝ) * d) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast (Finset.card_filter_le s _).trans hcard.le
      _ = 1 / (d : ℝ) := by field_simp
  have hH : (1 : ℝ) ≤ harmonic d := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    have h := Finset.single_le_sum (f := fun k : ℕ => ((k : ℚ)⁻¹ : ℝ))
      (fun k _ => by positivity) (Finset.mem_Icc.mpr (show 1 ≤ 1 ∧ 1 ≤ d by omega))
    simpa using h
  constructor
  · change (∑ p ∈ s, f p) ≤ _
    have hsplit : (∑ p ∈ small, f p) + (∑ p ∈ large, f p) = ∑ p ∈ s, f p :=
      Finset.sum_filter_add_sum_filter_not s (fun p => p ≤ d * d) f
    rw [← hsplit]
    have : 1 / (d : ℝ) ≤ 2 * (harmonic d : ℝ) / d := by
      apply div_le_div_of_nonneg_right _ hdR.le
      linarith
    calc
      _ ≤ 4 * (harmonic d : ℝ) / d + 1 / (d : ℝ) := add_le_add hsmallbound hlarge
      _ ≤ 4 * (harmonic d : ℝ) / d + 2 * (harmonic d : ℝ) / d := add_le_add_right this _
      _ = _ := by ring
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log d) (by norm_num)) hdR.le

#print axioms result

end D5.S3.Arith.Robin.FibonacciRankEulerTail
