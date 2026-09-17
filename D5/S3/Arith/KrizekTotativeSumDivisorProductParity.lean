/- GID: D5/S3/Arith/KrizekTotativeSumDivisorProductParity
   generality: I
   mirror-B: D5/B/S3/Arith/KrizekTotativeSumDivisorProductParity
   mirror-E: none(waiver:symbolic-number-theoretic-structure)
   anchors: []
   utility: none
   digest: The divisor product of totative sums is odd exactly when the totative sum is odd. -/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.PrimePow

/-
  This module is symbolic over arbitrary natural numbers, so utility is `none`.
  `totativeSum` and `divisorTotativeProduct` define general arithmetic functions,
  not bounded enumerations or certified instances. `odd_totativeSum_iff` and
  `result` are general theorems, not checkers or numeric reductions. Thus none
  of the four declarations belongs to any of the four computational-content
  classes.
-/

open scoped BigOperators

namespace D5.S3.Arith.KrizekTotativeSumDivisorProductParity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

def totativeSum (n : ℕ) : ℕ :=
  ∑ k ∈ (Finset.range (n + 1)).filter (n.Coprime ·), k

def divisorTotativeProduct (n : ℕ) : ℕ :=
  ∏ d ∈ n.divisors, totativeSum d

theorem odd_totativeSum_iff (n : ℕ) :
    Odd (totativeSum n) ↔
      n = 1 ∨ n = 2 ∨
        ∃ p k : ℕ, p.Prime ∧ p % 4 = 3 ∧ 1 ≤ k ∧ n = p ^ k := by
  have two_mul_totativeSum : ∀ {n : ℕ}, 1 < n → 2 * totativeSum n = n * n.totient := by
    intro n hn
    let A := (range n).filter (n.Coprime ·)
    have hpos {k : ℕ} (hk : k ∈ A) : 0 < k := by
      have hc : n.Coprime k := (mem_filter.mp hk).2
      exact Nat.pos_of_ne_zero fun hk0 => by
        subst k
        simp only [Nat.coprime_zero_right] at hc
        omega
    have hlt {k : ℕ} (hk : k ∈ A) : k < n :=
      mem_range.mp (mem_filter.mp hk).1
    have hmem {k : ℕ} (hk : k ∈ A) : n - k ∈ A := by
      rw [mem_filter, mem_range]
      exact ⟨Nat.sub_lt (by omega) (hpos hk),
        (Nat.coprime_self_sub_right (Nat.le_of_lt (hlt hk))).mpr (mem_filter.mp hk).2⟩
    have hsym : (∑ k ∈ A, k) = ∑ k ∈ A, (n - k) := by
      apply Finset.sum_bij' (fun k _ => n - k) (fun k _ => n - k)
      · exact fun k hk => hmem hk
      · exact fun k hk => hmem hk
      · intro k hk
        exact Nat.sub_sub_self (Nat.le_of_lt (hlt hk))
      · intro k hk
        exact Nat.sub_sub_self (Nat.le_of_lt (hlt hk))
      · intro k hk
        exact (Nat.sub_sub_self (Nat.le_of_lt (hlt hk))).symm
    have hrange : totativeSum n = ∑ k ∈ (range n).filter (n.Coprime ·), k := by
      rw [totativeSum, range_add_one, filter_insert]
      simp [show n ≠ 1 by omega]
    rw [hrange]
    change 2 * (∑ k ∈ A, k) = _
    rw [two_mul]
    nth_rw 2 [hsym]
    rw [← sum_add_distrib]
    calc
      (∑ k ∈ A, (k + (n - k))) = ∑ _k ∈ A, n :=
        sum_congr rfl fun k hk => Nat.add_sub_of_le (Nat.le_of_lt (hlt hk))
      _ = #A * n := by simp
      _ = n * n.totient := by simp [A, Nat.totient, mul_comm]
  by_cases hn0 : n = 0
  · subst n
    have hs : totativeSum 0 = 0 := by decide
    constructor
    · rw [hs]
      norm_num
    · rintro (h | h | ⟨p, k, hp, _hpmod, _hk, hpow⟩)
      · omega
      · omega
      · have : 0 < p ^ k := pow_pos hp.pos k
        omega
  by_cases hn1 : n = 1
  · subst n
    have hs : totativeSum 1 = 1 := by decide
    constructor
    · exact fun _ => Or.inl rfl
    · intro _
      rw [hs]
      norm_num
  by_cases hn2 : n = 2
  · subst n
    have hs : totativeSum 2 = 1 := by decide
    constructor
    · exact fun _ => Or.inr (Or.inl rfl)
    · intro _
      rw [hs]
      norm_num
  have hn : 2 < n := by omega
  constructor
  · intro hsumOdd
    have hnot4 : ¬4 ∣ n * n.totient := by
      intro h4
      rw [← two_mul_totativeSum (by omega)] at h4
      apply (Nat.not_even_iff_odd.mpr hsumOdd)
      obtain ⟨q, hq⟩ := h4
      exact ⟨q, by omega⟩
    have hnOdd : Odd n := by
      apply Nat.not_even_iff_odd.mp
      intro hnEven
      apply hnot4
      obtain ⟨a, ha⟩ := hnEven
      obtain ⟨b, hb⟩ := Nat.totient_even hn
      refine ⟨a * b, ?_⟩
      calc
        n * n.totient = (a + a) * (b + b) := congrArg₂ (· * ·) ha hb
        _ = 4 * (a * b) := by ring
    have hcard_le : n.primeFactors.card ≤ 1 := by
      by_contra hcard
      have htwo : 1 < n.primeFactors.card := by omega
      obtain ⟨p, hp_mem, q, hq_mem, hpq⟩ := Finset.one_lt_card.mp htwo
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have hq : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
      have hp_ne_two : p ≠ 2 :=
        hnOdd.ne_two_of_dvd_nat (Nat.dvd_of_mem_primeFactors hp_mem)
      have hq_ne_two : q ≠ 2 :=
        hnOdd.ne_two_of_dvd_nat (Nat.dvd_of_mem_primeFactors hq_mem)
      obtain ⟨a, ha⟩ := hp.even_sub_one hp_ne_two
      obtain ⟨b, hb⟩ := hq.even_sub_one hq_ne_two
      have hpair : ({p, q} : Finset ℕ) ⊆ n.primeFactors := by
        simpa only [insert_subset_iff, singleton_subset_iff] using ⟨hp_mem, hq_mem⟩
      have hpair_dvd :=
        Finset.prod_dvd_prod_of_subset ({p, q} : Finset ℕ) n.primeFactors
          (fun r : ℕ => r - 1) hpair
      have h4pair : 4 ∣ (p - 1) * (q - 1) := by
        refine ⟨a * b, ?_⟩
        rw [ha, hb]
        ring
      have h4prod : 4 ∣ ∏ r ∈ n.primeFactors, (r - 1) := by
        apply h4pair.trans
        simpa [hpq] using hpair_dvd
      have h4phi : 4 ∣ n.totient := by
        rw [Nat.totient_eq_div_primeFactors_mul]
        exact dvd_mul_of_dvd_right h4prod _
      exact hnot4 (dvd_mul_of_dvd_right h4phi n)
    have hcard_pos : 0 < n.primeFactors.card :=
      Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega))
    have hcard : n.primeFactors.card = 1 := by omega
    have hprimePow : IsPrimePow n :=
      isPrimePow_iff_card_primeFactors_eq_one.mpr hcard
    obtain ⟨p, k, hp, hk, hpow⟩ := (isPrimePow_nat_iff n).mp hprimePow
    have hp_dvd : p ∣ n := by
      rw [← hpow]
      exact dvd_pow_self p hk.ne'
    have hpOdd : Odd p := hnOdd.of_dvd_nat hp_dvd
    have hpmod : p % 4 = 1 ∨ p % 4 = 3 := by
      have := Nat.odd_iff.mp hpOdd
      omega
    have hpmod3 : p % 4 = 3 := by
      rcases hpmod with hpmod1 | hpmod3
      · exfalso
        have h4pred : 4 ∣ p - 1 := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h4phi : 4 ∣ n.totient := by
          rw [← hpow, Nat.totient_prime_pow hp hk]
          exact dvd_mul_of_dvd_right h4pred _
        exact hnot4 (dvd_mul_of_dvd_right h4phi n)
      · exact hpmod3
    exact Or.inr (Or.inr ⟨p, k, hp, hpmod3, hk, hpow.symm⟩)
  · rintro (hone | htwo | ⟨p, k, hp, hpmod, hk, rfl⟩)
    · exact (hn1 hone).elim
    · exact (hn2 htwo).elim
    · have hpOdd : Odd p := by
        rw [Nat.odd_iff]
        omega
      obtain ⟨a, ha⟩ : ∃ a : ℕ, p = 4 * a + 3 := by
        refine ⟨p / 4, ?_⟩
        omega
      have hlarge : 1 < p ^ k := by
        exact one_lt_pow₀ hp.one_lt (by omega)
      have hdouble := two_mul_totativeSum hlarge
      rw [Nat.totient_prime_pow hp hk] at hdouble
      have hsum : totativeSum (p ^ k) =
          p ^ k * p ^ (k - 1) * (2 * a + 1) := by
        have hpred : p - 1 = 2 * (2 * a + 1) := by omega
        apply Nat.mul_left_cancel (show 0 < 2 by omega)
        calc
          2 * totativeSum (p ^ k) = p ^ k * (p ^ (k - 1) * (p - 1)) := hdouble
          _ = 2 * (p ^ k * p ^ (k - 1) * (2 * a + 1)) := by
            rw [hpred]
            ring
      rw [hsum]
      exact (hpOdd.pow.mul hpOdd.pow).mul (odd_two_mul_add_one a)

theorem result (n : ℕ) (hn : 1 ≤ n) :
    Odd (divisorTotativeProduct n) ↔ Odd (totativeSum n) := by
  have odd_prod_iff (s : Finset ℕ) (f : ℕ → ℕ) :
      Odd (∏ x ∈ s, f x) ↔ ∀ x ∈ s, Odd (f x) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simp only [Finset.prod_insert ha, Nat.odd_mul, ih]
        aesop
  rw [divisorTotativeProduct, odd_prod_iff]
  constructor
  · intro hall
    exact hall n (Nat.mem_divisors_self n (by omega))
  · intro hnOdd d hd
    have hnclass := (odd_totativeSum_iff n).mp hnOdd
    apply (odd_totativeSum_iff d).mpr
    rcases hnclass with rfl | rfl | ⟨p, k, hp, hpmod, hk, rfl⟩
    · have hd1 : d = 1 := by
        exact Nat.dvd_one.mp (Nat.dvd_of_mem_divisors hd)
      exact Or.inl hd1
    · have hd12 : d = 1 ∨ d = 2 := by
        exact (Nat.dvd_prime Nat.prime_two).mp (Nat.dvd_of_mem_divisors hd)
      rcases hd12 with hd1 | hd2
      · exact Or.inl hd1
      · exact Or.inr (Or.inl hd2)
    · obtain ⟨j, hjk, hdj⟩ := (Nat.dvd_prime_pow hp).mp (Nat.dvd_of_mem_divisors hd)
      subst d
      by_cases hj : j = 0
      · subst j
        exact Or.inl (by simp)
      · exact Or.inr (Or.inr ⟨p, j, hp, hpmod, by omega, rfl⟩)

#print axioms odd_totativeSum_iff
#print axioms result

end D5.S3.Arith.KrizekTotativeSumDivisorProductParity
