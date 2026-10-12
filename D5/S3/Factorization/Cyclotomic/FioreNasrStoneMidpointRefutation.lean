/- GID: D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation
   generality: I
   mirror-B: D5/B/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.claim; result=D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.result; claim=D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.claim
   digest: Odd primes three, five and eleven refute the midpoint assertion of Conjecture 6.8. -/

import D5.S3.Factorization.Cyclotomic.GeometricSpectrumFactorization
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Counterexamples.Cyclotomic105

noncomputable section

namespace D5.S3.Factorization.Cyclotomic.FioreNasrStoneMidpointRefutation

open Polynomial
open scoped BigOperators

/-- The first polynomial of Definition 6.1 at all four mixed exponents equal to one. -/
def midpointA (p q r : ℕ) : Polynomial ℤ :=
  Polynomial.X * (Polynomial.cyclotomic p ℤ)^2 *
    (Polynomial.cyclotomic q ℤ)^2 * Polynomial.cyclotomic (p*q) ℤ *
    Polynomial.cyclotomic (p*r) ℤ * Polynomial.cyclotomic (q*r) ℤ *
    Polynomial.cyclotomic (p*q*r) ℤ

/-- The second polynomial of Definition 6.1 at the complementary midpoint exponents. -/
def midpointB (p q r : ℕ) : Polynomial ℤ :=
  Polynomial.X * (Polynomial.cyclotomic r ℤ)^2 *
    Polynomial.cyclotomic (p*q) ℤ * Polynomial.cyclotomic (p*r) ℤ *
    Polynomial.cyclotomic (q*r) ℤ * Polynomial.cyclotomic (p*q*r) ℤ

/-- The universal midpoint assertion explicitly included in Conjecture 6.8. -/
def claim : Prop :=
  ∀ p q r : ℕ, Nat.Prime p → Nat.Prime q → Nat.Prime r →
    p ≠ q → p ≠ r → q ≠ r → p ≠ 2 →
    ((∃ n : ℕ, (midpointA p q r).coeff n < 0) ∨
     (∃ n : ℕ, (midpointB p q r).coeff n < 0))

/-- Both complete midpoint polynomials at `(3,5,11)` have nonnegative coefficients. -/
theorem result : Not claim := by
  classical
  have h3 : cyclotomic 3 ℤ = ∑ i ∈ Finset.range 3, (X : ℤ[X]) ^ i := by
    simpa [Nat.Prime.divisors (by norm_num : Nat.Prime 3)] using
      (GeometricSpectrumFactorization.geometric_sum_eq_cyclotomic_product
        ℤ (n := 3) (by norm_num)).symm
  have h5 : cyclotomic 5 ℤ = ∑ i ∈ Finset.range 5, (X : ℤ[X]) ^ i := by
    simpa [Nat.Prime.divisors (by norm_num : Nat.Prime 5)] using
      (GeometricSpectrumFactorization.geometric_sum_eq_cyclotomic_product
        ℤ (n := 5) (by norm_num)).symm
  have h11 : cyclotomic 11 ℤ = ∑ i ∈ Finset.range 11, (X : ℤ[X]) ^ i := by
    simpa [Nat.Prime.divisors (by norm_num : Nat.Prime 11)] using
      (GeometricSpectrumFactorization.geometric_sum_eq_cyclotomic_product
        ℤ (n := 11) (by norm_num)).symm
  have he3 := cyclotomic_expand_eq_cyclotomic_mul (by norm_num : Nat.Prime 3)
    (by norm_num : ¬ 3 ∣ 5) ℤ
  have he11_3 := cyclotomic_expand_eq_cyclotomic_mul (by norm_num : Nat.Prime 11)
    (by norm_num : ¬ 11 ∣ 3) ℤ
  have he11_5 := cyclotomic_expand_eq_cyclotomic_mul (by norm_num : Nat.Prime 11)
    (by norm_num : ¬ 11 ∣ 5) ℤ
  have he11_15 := cyclotomic_expand_eq_cyclotomic_mul (by norm_num : Nat.Prime 11)
    (by norm_num : ¬ 11 ∣ 15) ℤ
  have he5_11 := cyclotomic_expand_eq_cyclotomic_mul (by norm_num : Nat.Prime 5)
    (by norm_num : ¬ 5 ∣ 11) ℤ
  have he3_11 := cyclotomic_expand_eq_cyclotomic_mul (by norm_num : Nat.Prime 3)
    (by norm_num : ¬ 3 ∣ 11) ℤ
  have he3_55 := cyclotomic_expand_eq_cyclotomic_mul (by norm_num : Nat.Prime 3)
    (by norm_num : ¬ 3 ∣ 55) ℤ
  have hA : midpointA 3 5 11 = X * cyclotomic 3 ℤ * cyclotomic 5 ℤ *
      expand ℤ 11 (cyclotomic 3 ℤ) * expand ℤ 33 (cyclotomic 5 ℤ) := by
    rw [show 33 = 11 * 3 by norm_num, expand_mul, he3, map_mul,
      he11_3, he11_15, he11_5]
    norm_num [midpointA]
    ring
  have hB : midpointB 3 5 11 = X * (cyclotomic 11 ℤ * cyclotomic 15 ℤ) *
      expand ℤ 15 (cyclotomic 11 ℤ) := by
    rw [show 15 = 3 * 5 by norm_num, expand_mul, he5_11, map_mul,
      he3_55, he3_11]
    norm_num [midpointB]
    ring
  have hC : cyclotomic 11 ℤ * cyclotomic 15 ℤ =
      ∑ i ∈ ({0, 3, 5, 6, 8, 9, 10, 12, 13, 15, 18} : Finset ℕ), (X : ℤ[X]) ^ i := by
    rw [h11, Counterexample.cyclotomic_15]
    norm_num [Finset.sum_range_succ]
    ring
  have hsum (s : Finset ℕ) (n : ℕ) :
      0 ≤ (∑ i ∈ s, (X : ℤ[X]) ^ i).coeff n := by
    rw [finsetSum_coeff]
    apply Finset.sum_nonneg
    intro i _
    rw [coeff_X_pow]
    split <;> norm_num
  have hmul (f g : ℤ[X]) (hf : ∀ n, 0 ≤ f.coeff n) (hg : ∀ n, 0 ≤ g.coeff n)
      (n : ℕ) : 0 ≤ (f * g).coeff n := by
    rw [coeff_mul]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hf i.1) (hg i.2)
  have hexpand (k : ℕ) (hk : 0 < k) (f : ℤ[X]) (hf : ∀ n, 0 ≤ f.coeff n)
      (n : ℕ) : 0 ≤ (expand ℤ k f).coeff n := by
    rw [coeff_expand hk]
    split
    · exact hf _
    · norm_num
  have hx : ∀ n, 0 ≤ (X : ℤ[X]).coeff n := by
    intro n
    rw [coeff_X]
    split <;> norm_num
  have hn3 : ∀ n, 0 ≤ (cyclotomic 3 ℤ).coeff n := by
    rw [h3]
    exact hsum _
  have hn5 : ∀ n, 0 ≤ (cyclotomic 5 ℤ).coeff n := by
    rw [h5]
    exact hsum _
  have hn11 : ∀ n, 0 ≤ (cyclotomic 11 ℤ).coeff n := by
    rw [h11]
    exact hsum _
  have hnA : ∀ n, 0 ≤ (midpointA 3 5 11).coeff n := by
    rw [hA]
    exact hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ hx hn3) hn5)
      (hexpand 11 (by norm_num) _ hn3)) (hexpand 33 (by norm_num) _ hn5)
  have hnB : ∀ n, 0 ≤ (midpointB 3 5 11).coeff n := by
    rw [hB, hC]
    exact hmul _ _ (hmul _ _ hx (hsum _)) (hexpand 15 (by norm_num) _ hn11)
  intro h
  rcases h 3 5 11 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) with ⟨n, hn⟩ | ⟨n, hn⟩
  · exact (not_lt_of_ge (hnA n)) hn
  · exact (not_lt_of_ge (hnB n)) hn

#print axioms result

end D5.S3.Factorization.Cyclotomic.FioreNasrStoneMidpointRefutation
