/- GID: D5/S3/Arith/KrizekTriangularSquareSigmaParity
   generality: I
   mirror-B: D5/B/S3/Arith/KrizekTriangularSquareSigmaParity
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Ring.Nat, mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc]
   utility: none
   digest: Krizek's triangular number is square exactly when both divisor sums are odd. -/

import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.NumberTheory.ArithmeticFunction.Misc

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

private theorem consecutive_coprime_twice_square_split (n b : ℕ) (hn : 0 < n)
    (hprod : n * (n + 1) = 2 * b ^ 2) :
    (IsSquare n ∧ ∃ d : ℕ, n + 1 = 2 * d ^ 2) ∨
      ((∃ c : ℕ, n = 2 * c ^ 2) ∧ IsSquare (n + 1)) := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hn10 : n + 1 ≠ 0 := by omega
  have hb0 : b ≠ 0 := by
    intro h
    subst b
    simp at hprod
    exact hn0 hprod
  have hcop : n.Coprime (n + 1) := by simp
  have even_odd_prime_factorization_left (x y : ℕ) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
      (hxyCop : x.Coprime y) (hxy : x * y = 2 * b ^ 2) :
      ∀ p ∈ x.primeFactors, p ≠ 2 → Even (x.factorization p) := by
    intro p hpMem hpTwo
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    have hpDivX : p ∣ x := Nat.dvd_of_mem_primeFactors hpMem
    have hpNotDivY : ¬p ∣ y := by
      intro hpDivY
      have hpDivGcd : p ∣ Nat.gcd x y := Nat.dvd_gcd hpDivX hpDivY
      rw [hxyCop.gcd_eq_one] at hpDivGcd
      exact hpPrime.ne_one (Nat.dvd_one.mp hpDivGcd)
    have hyFactor : y.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hpNotDivY
    have hpNotDvdTwo : ¬p ∣ 2 := by
      intro hpDivTwo
      exact hpTwo ((Nat.prime_dvd_prime_iff_eq hpPrime Nat.prime_two).mp hpDivTwo)
    have htwoFactor : (Nat.factorization 2) p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hpNotDvdTwo
    have hfactor := congrArg (fun z : ℕ ↦ z.factorization p) hxy
    rw [Nat.factorization_mul hx0 hy0,
      Nat.factorization_mul (by decide) (pow_ne_zero _ hb0),
      Nat.factorization_pow] at hfactor
    change x.factorization p + y.factorization p =
      Nat.factorization 2 p + 2 * b.factorization p at hfactor
    rw [hyFactor, htwoFactor] at hfactor
    exact ⟨b.factorization p, by omega⟩
  have odd_sigma_of_even_odd_prime_factorization (x : ℕ) (hx0 : x ≠ 0)
      (heven : ∀ p ∈ x.primeFactors, p ≠ 2 → Even (x.factorization p)) :
      Odd (sigma 1 x) := by
    have odd_prod (s : Finset ℕ) (f : ℕ → ℕ)
        (h : ∀ p ∈ s, Odd (f p)) : Odd (∏ p ∈ s, f p) := by
      induction s using Finset.induction_on with
      | empty => norm_num
      | @insert p s hp ih =>
          rw [Finset.prod_insert hp]
          exact (h p (Finset.mem_insert_self p s)).mul
            (ih (fun q hq ↦ h q (Finset.mem_insert_of_mem hq)))
    have hsigmaProd :
        sigma 1 x =
          ∏ p ∈ x.primeFactors,
            ∑ i ∈ Finset.range (x.factorization p + 1), p ^ i := by
      simpa using
        (sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
          (k := 1) hx0)
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
      simp only [hpOdd.pow, Finset.filter_true, Finset.card_range]
      obtain ⟨q, hq⟩ := heven p hpMem hpTwo
      exact ⟨q, by omega⟩
  have hnEvenFactors :=
    even_odd_prime_factorization_left n (n + 1) hn0 hn10 hcop hprod
  have hn1EvenFactors :=
    even_odd_prime_factorization_left (n + 1) n hn10 hn0 hcop.symm (by
      simpa only [mul_comm] using hprod)
  have hnShape : IsSquare n ∨ ∃ c : ℕ, n = 2 * c ^ 2 :=
    (sigma_odd_iff_square_or_twice_square n hn).mp
      (odd_sigma_of_even_odd_prime_factorization n hn0 hnEvenFactors)
  have hn1Shape : IsSquare (n + 1) ∨ ∃ d : ℕ, n + 1 = 2 * d ^ 2 :=
    (sigma_odd_iff_square_or_twice_square (n + 1) (by omega)).mp
      (odd_sigma_of_even_odd_prime_factorization (n + 1) hn10 hn1EvenFactors)
  have no_nonzero_square_eq_twice_square (x y : ℕ) (hx0 : x ≠ 0)
      (heq : x ^ 2 = 2 * y ^ 2) : False := by
    have hy0 : y ≠ 0 := by
      intro h
      subst y
      simp at heq
      exact hx0 heq
    have hfactor := congrArg (fun z : ℕ ↦ z.factorization 2) heq
    rw [Nat.factorization_pow,
      Nat.factorization_mul (by decide) (pow_ne_zero _ hy0),
      Nat.factorization_pow] at hfactor
    change 2 * x.factorization 2 =
      Nat.factorization 2 2 + 2 * y.factorization 2 at hfactor
    have htwoFactor : Nat.factorization 2 2 = 1 :=
      Nat.Prime.factorization_self Nat.prime_two
    rw [htwoFactor] at hfactor
    omega
  rcases hnShape with hnSquare | hnTwice
  · rcases hn1Shape with hn1Square | hn1Twice
    · obtain ⟨x, hx⟩ := hnSquare.mul hn1Square
      have hx0 : x ≠ 0 := by
        intro h
        subst x
        simp at hx
        omega
      have heq : x ^ 2 = 2 * b ^ 2 := by
        simpa only [pow_two] using hx.symm.trans hprod
      exact (no_nonzero_square_eq_twice_square x b hx0 heq).elim
    · exact Or.inl ⟨hnSquare, hn1Twice⟩
  · rcases hn1Shape with hn1Square | hn1Twice
    · exact Or.inr ⟨hnTwice, hn1Square⟩
    · obtain ⟨c, hc⟩ := hnTwice
      obtain ⟨d, hd⟩ := hn1Twice
      have heq : b ^ 2 = 2 * (c * d) ^ 2 := by
        rw [hd, hc] at hprod
        nlinarith [hprod]
      exact (no_nonzero_square_eq_twice_square b (c * d) hb0 heq).elim

private theorem twice_square_triangular_exclusion (n f : ℕ) (hn : 0 < n)
    (hnShape : IsSquare n ∨ ∃ d : ℕ, n = 2 * d ^ 2)
    (htri : n * (n + 1) / 2 = 2 * f ^ 2) : False := by
  have htwoDvd : 2 ∣ n * (n + 1) :=
    even_iff_two_dvd.mp (Nat.even_mul_succ_self n)
  have hprod : n * (n + 1) = 4 * f ^ 2 := by
    calc
      n * (n + 1) = n * (n + 1) / 2 * 2 := (Nat.div_mul_cancel htwoDvd).symm
      _ = (2 * f ^ 2) * 2 := by rw [htri]
      _ = 4 * f ^ 2 := by ring
  rcases hnShape with hnSquare | hnTwice
  · obtain ⟨c, hc⟩ := hnSquare
    have hc0 : c ≠ 0 := by
      intro h
      subst c
      simp at hc
      omega
    have heq : c ^ 2 * (c ^ 2 + 1) = (2 * f) ^ 2 := by
      rw [hc] at hprod
      nlinarith [hprod]
    have hcSqDvd : c ^ 2 ∣ (2 * f) ^ 2 :=
      ⟨c ^ 2 + 1, heq.symm⟩
    have hcDvd : c ∣ 2 * f :=
      (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp hcSqDvd
    obtain ⟨g, hg⟩ := hcDvd
    have hcancel : c ^ 2 * (c ^ 2 + 1) = c ^ 2 * g ^ 2 := by
      calc
        c ^ 2 * (c ^ 2 + 1) = (2 * f) ^ 2 := heq
        _ = (c * g) ^ 2 := by rw [hg]
        _ = c ^ 2 * g ^ 2 := by ring
    have hnextSquare : c ^ 2 + 1 = g ^ 2 :=
      Nat.mul_left_cancel (pow_pos (by omega : 0 < c) 2) hcancel
    have hcLtG : c < g := by
      rw [← Nat.mul_self_lt_mul_self_iff]
      simpa only [pow_two] using (show c ^ 2 < g ^ 2 by omega)
    have hnextLe : (c + 1) * (c + 1) ≤ g * g :=
      Nat.mul_self_le_mul_self (by omega)
    nlinarith [hnextLe]
  · obtain ⟨d, hd⟩ := hnTwice
    have hd0 : d ≠ 0 := by
      intro h
      subst d
      simp at hd
      omega
    have heq : d ^ 2 * (2 * d ^ 2 + 1) = 2 * f ^ 2 := by
      rw [hd] at hprod
      nlinarith [hprod]
    have hf0 : f ≠ 0 := by
      intro h
      subst f
      simp at heq
      exact hd0 (by nlinarith [heq])
    have hoddNotDiv : ¬2 ∣ 2 * d ^ 2 + 1 := by omega
    have hoddFactor : (2 * d ^ 2 + 1).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hoddNotDiv
    have hfactor := congrArg (fun z : ℕ ↦ z.factorization 2) heq
    rw [Nat.factorization_mul (pow_ne_zero _ hd0) (by omega),
      Nat.factorization_pow,
      Nat.factorization_mul (by decide) (pow_ne_zero _ hf0),
      Nat.factorization_pow] at hfactor
    change 2 * d.factorization 2 + (2 * d ^ 2 + 1).factorization 2 =
      Nat.factorization 2 2 + 2 * f.factorization 2 at hfactor
    have htwoFactor : Nat.factorization 2 2 = 1 :=
      Nat.Prime.factorization_self Nat.prime_two
    rw [hoddFactor, htwoFactor] at hfactor
    omega

theorem result : ∀ n : ℕ, 0 < n →
    (IsSquare (n * (n + 1) / 2) ↔
      (Odd (sigma 1 n) ∧ Odd (sigma 1 (n * (n + 1) / 2)))) := by
  intro n hn
  have htriPos : 0 < n * (n + 1) / 2 := by
    apply Nat.div_pos
    · nlinarith
    · decide
  constructor
  · intro htriSquare
    have htwoDvd : 2 ∣ n * (n + 1) :=
      even_iff_two_dvd.mp (Nat.even_mul_succ_self n)
    obtain ⟨b, hb⟩ := htriSquare
    have hprod : n * (n + 1) = 2 * b ^ 2 := by
      calc
        n * (n + 1) = n * (n + 1) / 2 * 2 := (Nat.div_mul_cancel htwoDvd).symm
        _ = (b * b) * 2 := by rw [hb]
        _ = 2 * b ^ 2 := by ring
    have hnShape : IsSquare n ∨ ∃ c : ℕ, n = 2 * c ^ 2 := by
      rcases consecutive_coprime_twice_square_split n b hn hprod with hleft | hright
      · exact Or.inl hleft.1
      · exact Or.inr hright.1
    exact ⟨(sigma_odd_iff_square_or_twice_square n hn).mpr hnShape,
      (sigma_odd_iff_square_or_twice_square (n * (n + 1) / 2) htriPos).mpr
        (Or.inl ⟨b, hb⟩)⟩
  · rintro ⟨hnSigmaOdd, htriSigmaOdd⟩
    have hnShape : IsSquare n ∨ ∃ c : ℕ, n = 2 * c ^ 2 :=
      (sigma_odd_iff_square_or_twice_square n hn).mp hnSigmaOdd
    rcases (sigma_odd_iff_square_or_twice_square
        (n * (n + 1) / 2) htriPos).mp htriSigmaOdd with htriSquare | htriTwice
    · exact htriSquare
    · obtain ⟨f, hf⟩ := htriTwice
      exact (twice_square_triangular_exclusion n f hn hnShape hf).elim

#print axioms result

end D5.S3.Arith.KrizekTriangularSquareSigmaParity
