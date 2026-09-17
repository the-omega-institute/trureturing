/- GID: D5/S3/Arith/KrizekPhitorialDivisorSumParity
   generality: I
   mirror-B: D5/B/S3/Arith/KrizekPhitorialDivisorSumParity
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Krizek's divisor sum of phitorials is odd exactly off twice a square. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Ring.Nat

open scoped BigOperators
open Finset

namespace D5.S3.Arith.KrizekPhitorialDivisorSumParity

set_option autoImplicit false
set_option relaxedAutoImplicit false

def phitorial (m : ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 1 m with Nat.Coprime k m, k

private def evenDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter Even

def a (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, phitorial d

def claim : Prop :=
  ∀ n : ℕ, 0 < n → (Odd (a n) ↔ ¬ ∃ k : ℕ, n = 2 * k ^ 2)

theorem result : claim := by
  intro n hn
  have odd_card_divisors_iff_square {m : ℕ} (hm : 0 < m) :
      Odd (#m.divisors) ↔ ∃ k : ℕ, m = k ^ 2 := by
    have odd_prod_iff (s : Finset ℕ) (f : ℕ → ℕ) :
        Odd (∏ x ∈ s, f x) ↔ ∀ x ∈ s, Odd (f x) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih => simp [ha, ih, Nat.odd_mul]
    rw [Nat.card_divisors hm.ne', odd_prod_iff]
    constructor
    · intro h
      let k := ∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2)
      refine ⟨k, ?_⟩
      rw [Nat.prod_primeFactors_pow_factorization hm.ne']
      dsimp only [k]
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_mul]
      congr 1
      have he : Even (m.factorization p) :=
        Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp (h p hp))
      rcases he with ⟨r, hr⟩
      omega
    · rintro ⟨k, rfl⟩ p hp
      rw [Nat.factorization_pow, Finsupp.smul_apply]
      simp
  have odd_phitorial_iff (m : ℕ) :
      Odd (phitorial m) ↔ m = 1 ∨ Even m := by
    constructor
    · intro hp
      by_cases h1 : m = 1
      · exact Or.inl h1
      right
      by_contra hne
      have hmOdd : Odd m := Nat.not_even_iff_odd.mp hne
      have hmTwo : 2 ≤ m := by
        rcases hmOdd with ⟨r, hr⟩
        omega
      have htwo : 2 ∈ (Finset.Icc 1 m).filter (fun k => Nat.Coprime k m) := by
        simpa [hmTwo] using hmOdd
      have hpEven : Even (phitorial m) := by
        rw [even_iff_two_dvd]
        exact Finset.dvd_prod_of_mem (fun k : ℕ => k) htwo
      exact (Nat.not_even_iff_odd.mpr hp) hpEven
    · rintro (rfl | hmEven)
      · simp [phitorial]
      have odd_prod_iff (s : Finset ℕ) (f : ℕ → ℕ) :
          Odd (∏ x ∈ s, f x) ↔ ∀ x ∈ s, Odd (f x) := by
        induction s using Finset.induction_on with
        | empty => simp
        | @insert a s ha ih => simp [ha, ih, Nat.odd_mul]
      rw [phitorial, odd_prod_iff]
      intro k hk
      have hcop : Nat.Coprime k m := by
        change k ∈ (Finset.Icc 1 m).filter (fun j => Nat.Coprime j m) at hk
        exact (Finset.mem_filter.mp hk).2
      exact (Nat.Coprime.of_dvd_right hmEven.two_dvd hcop).odd_of_right
  have card_evenDivisors_two_mul (m : ℕ) (hm : 0 < m) :
      #(evenDivisors (2 * m)) = #m.divisors := by
    classical
    refine Finset.card_bij'
        (fun d _ => d / 2)
        (fun e _ => 2 * e) ?_ ?_ ?_ ?_
    · intro d hd
      have hd' : d ∈ (2 * m).divisors ∧ Even d := by
        simpa [evenDivisors] using hd
      rcases hd'.2 with ⟨r, hr⟩
      have hdr : d = 2 * r := by omega
      have hdvd : d ∣ 2 * m := Nat.dvd_of_mem_divisors hd'.1
      rcases hdvd with ⟨c, hc⟩
      apply Nat.mem_divisors.mpr
      constructor
      · refine ⟨c, ?_⟩
        rw [hdr] at hc
        have hc' : 2 * m = 2 * (r * c) := by simpa [mul_assoc] using hc
        have : m = r * c := Nat.mul_left_cancel (by decide : 0 < 2) hc'
        simpa [hdr] using this
      · exact hm.ne'
    · intro e he
      have he' : e ∣ m ∧ m ≠ 0 := Nat.mem_divisors.mp he
      apply Finset.mem_filter.mpr
      constructor
      · apply Nat.mem_divisors.mpr
        constructor
        · exact Nat.mul_dvd_mul_left 2 he'.1
        · exact mul_ne_zero (by decide) hm.ne'
      · exact ⟨e, by omega⟩
    · intro d hd
      have hdEven : Even d := by
        have := (Finset.mem_filter.mp (show d ∈ (2 * m).divisors.filter Even by
          simpa [evenDivisors] using hd)).2
        exact this
      rcases hdEven with ⟨r, hr⟩
      have hdr : d = 2 * r := by omega
      simp [hdr]
    · intro e he
      simp
  have hoddA : Odd (a n) ↔ Even (#(evenDivisors n)) := by
    rw [a, Finset.odd_sum_iff_odd_card_odd]
    have hfilter :
        {d ∈ n.divisors | Odd (phitorial d)} = insert 1 (evenDivisors n) := by
      ext d
      simp only [Finset.mem_filter, odd_phitorial_iff, Finset.mem_insert]
      constructor
      · rintro ⟨hd, h1 | he⟩
        · exact Or.inl h1
        · exact Or.inr (Finset.mem_filter.mpr ⟨hd, he⟩)
      · rintro (rfl | hd)
        · exact ⟨Nat.one_mem_divisors.mpr hn.ne', Or.inl rfl⟩
        · exact ⟨(Finset.mem_filter.mp hd).1, Or.inr (Finset.mem_filter.mp hd).2⟩
    rw [hfilter]
    have hone : 1 ∉ evenDivisors n := by simp [evenDivisors]
    rw [Finset.card_insert_of_notMem hone, Nat.odd_add_one, Nat.not_odd_iff_even]
  rw [hoddA]
  by_cases hnEven : Even n
  · rcases hnEven with ⟨m, hm⟩
    have hnm : n = 2 * m := by omega
    have hmpos : 0 < m := by omega
    rw [hnm, card_evenDivisors_two_mul m hmpos]
    constructor
    · intro hcard
      rintro ⟨k, hk⟩
      have hodd : Odd (#m.divisors) :=
        (odd_card_divisors_iff_square hmpos).mpr ⟨k, by omega⟩
      exact (Nat.not_odd_iff_even.mpr hcard) hodd
    · intro hnot
      rw [← Nat.not_odd_iff_even]
      intro hodd
      obtain ⟨k, hk⟩ := (odd_card_divisors_iff_square hmpos).mp hodd
      apply hnot
      exact ⟨k, by omega⟩
  · have hempty : evenDivisors n = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro d hd
      have hd' : d ∈ n.divisors ∧ Even d := by
        simpa [evenDivisors] using hd
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd'.1
      rcases hdvd with ⟨c, hc⟩
      apply hnEven
      rw [hc]
      exact Nat.even_mul.mpr (Or.inl hd'.2)
    rw [hempty]
    simp only [Finset.card_empty, Even.zero, true_iff]
    rintro ⟨k, hk⟩
    apply hnEven
    rw [hk]
    exact Nat.even_mul.mpr (Or.inl (by simp))

#print axioms result

end D5.S3.Arith.KrizekPhitorialDivisorSumParity
