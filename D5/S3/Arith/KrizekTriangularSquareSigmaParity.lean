/- GID: D5/S3/Arith/KrizekTriangularSquareSigmaParity
   generality: I
   mirror-B: D5/B/S3/Arith/KrizekTriangularSquareSigmaParity
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Ring.Nat, mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc, mathlib/module/Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity, mathlib/module/Mathlib.Tactic.IntervalCases, mathlib/module/Mathlib.Tactic.Linarith, mathlib/module/Mathlib.Tactic.NormNum, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Krizek's triangular number is square exactly when both divisor sums are odd. -/

import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace D5.S3.Arith.KrizekTriangularSquareSigmaParity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction
open scoped ArithmeticFunction

private theorem sigma_odd_iff_square_or_twice_square (m : ℕ) (hm : 0 < m) :
    Odd (sigma 1 m) ↔ (IsSquare m ∨ ∃ t : ℕ, m = 2 * t ^ 2) := by
  classical
  have hm0 : m ≠ 0 := by omega
  constructor
  · intro hsigmaOdd
    have hsigmaProd :
        sigma 1 m =
          ∏ p ∈ m.primeFactors,
            ∑ i ∈ Finset.range (m.factorization p + 1), p ^ i := by
      simpa using
        (sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
          (k := 1) hm0)
    have hEvenExponent : ∀ p ∈ m.primeFactors, p ≠ 2 → Even (m.factorization p) := by
      intro p hpMem hpTwo
      have hgeomDvd :
          (∑ i ∈ Finset.range (m.factorization p + 1), p ^ i) ∣ sigma 1 m := by
        rw [hsigmaProd]
        exact Finset.dvd_prod_of_mem _ hpMem
      have hgeomOdd := hsigmaOdd.of_dvd_nat hgeomDvd
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
      have hpOdd : Odd p := hpPrime.odd_of_ne_two hpTwo
      rw [Finset.odd_sum_iff_odd_card_odd] at hgeomOdd
      simp only [hpOdd.pow, Finset.filter_true, Finset.card_range] at hgeomOdd
      exact Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hgeomOdd)
    obtain ⟨k, r, hrOdd, hmr⟩ := Nat.exists_eq_two_pow_mul_odd hm0
    have hr0 : r ≠ 0 := by
      intro h
      subst r
      exact Nat.not_odd_zero hrOdd
    have hrDivM : r ∣ m := ⟨2 ^ k, by simpa [mul_comm] using hmr⟩
    have hEvenR : ∀ p ∈ r.primeFactors, Even (r.factorization p) := by
      intro p hpMem
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
      have hpDivR : p ∣ r := Nat.dvd_of_mem_primeFactors hpMem
      have hpTwo : p ≠ 2 := by
        intro h
        subst p
        exact hrOdd.not_two_dvd_nat hpDivR
      have hpMemM : p ∈ m.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpPrime, hpDivR.trans hrDivM, hm0⟩
      have hpNotDvdTwo : ¬p ∣ 2 := by
        intro hpDivTwo
        exact hpTwo ((Nat.prime_dvd_prime_iff_eq hpPrime Nat.prime_two).mp hpDivTwo)
      have hfactorTwo : (Nat.factorization 2) p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hpNotDvdTwo
      have hmFactor : m.factorization p = r.factorization p := by
        rw [hmr, Nat.factorization_mul (pow_ne_zero _ (by decide)) hr0]
        simp [Nat.factorization_pow, hfactorTwo]
      rw [← hmFactor]
      exact hEvenExponent p hpMemM hpTwo
    let t := ∏ p ∈ r.primeFactors, p ^ (r.factorization p / 2)
    have hrSquare : r = t ^ 2 := by
      have hprod := Nat.prod_factorization_pow_eq_self hr0
      change (∏ p ∈ r.primeFactors, p ^ r.factorization p) = r at hprod
      rw [← hprod]
      rw [show t = ∏ p ∈ r.primeFactors, p ^ (r.factorization p / 2) by rfl]
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro p hpMem
      obtain ⟨q, hq⟩ := hEvenR p hpMem
      rw [hq]
      have hhalf : (q + q) / 2 = q := by omega
      rw [hhalf]
      simp [pow_add, pow_two]
    rcases Nat.even_or_odd k with hk | hk
    · obtain ⟨j, hj⟩ := hk
      left
      refine ⟨2 ^ j * t, ?_⟩
      rw [hmr, hrSquare, hj]
      simp [pow_add, pow_two]
      ring
    · obtain ⟨j, hj⟩ := hk
      right
      refine ⟨2 ^ j * t, ?_⟩
      rw [hmr, hrSquare, hj]
      simp [pow_succ]
      rw [show 2 ^ (2 * j) = (2 ^ j) ^ 2 by
        rw [show 2 * j = j * 2 by omega, pow_mul]]
      ring
  · intro hshape
    have odd_prod (s : Finset ℕ) (f : ℕ → ℕ)
        (h : ∀ p ∈ s, Odd (f p)) : Odd (∏ p ∈ s, f p) := by
      induction s using Finset.induction_on with
      | empty => norm_num
      | @insert p s hp ih =>
          rw [Finset.prod_insert hp]
          exact (h p (Finset.mem_insert_self p s)).mul
            (ih (fun q hq ↦ h q (Finset.mem_insert_of_mem hq)))
    have hsigmaProd :
        sigma 1 m =
          ∏ p ∈ m.primeFactors,
            ∑ i ∈ Finset.range (m.factorization p + 1), p ^ i := by
      simpa using
        (sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
          (k := 1) hm0)
    rw [hsigmaProd]
    apply odd_prod
    intro p hpMem
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    rw [Finset.odd_sum_iff_odd_card_odd]
    by_cases hpTwo : p = 2
    · subst p
      have hpow (i : ℕ) : Odd (2 ^ i) ↔ i = 0 := by
        rw [← Nat.not_even_iff_odd, Nat.even_pow]
        norm_num
      simp_rw [hpow]
      simp
    · have hpOdd : Odd p := hpPrime.odd_of_ne_two hpTwo
      have hEvenExponent : Even (m.factorization p) := by
        rcases hshape with hsquare | htwice
        · obtain ⟨t, rfl⟩ := hsquare
          rw [show t * t = t ^ 2 by simp [pow_two], Nat.factorization_pow]
          change Even (2 * t.factorization p)
          exact even_two_mul _
        · obtain ⟨t, rfl⟩ := htwice
          have ht0 : t ≠ 0 := by
            intro h
            subst t
            simp at hm
          have hpNotDvdTwo : ¬p ∣ 2 := by
            intro hpDivTwo
            exact hpTwo ((Nat.prime_dvd_prime_iff_eq hpPrime Nat.prime_two).mp hpDivTwo)
          have hfactorTwo : (Nat.factorization 2) p = 0 :=
            Nat.factorization_eq_zero_of_not_dvd hpNotDvdTwo
          rw [Nat.factorization_mul (by decide) (pow_ne_zero _ ht0)]
          simp [Nat.factorization_pow, hfactorTwo]
      simp only [hpOdd.pow, Finset.filter_true, Finset.card_range]
      obtain ⟨q, hq⟩ := hEvenExponent
      exact ⟨q, by omega⟩

end D5.S3.Arith.KrizekTriangularSquareSigmaParity
