/- GID: D5/S3/Factorization/CollinearTripleCountDivisibility
   generality: G
   mirror-B: D5/B/S3/Factorization/CollinearTripleCountDivisibility
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Cyclic composition symmetry proves the A146557 square-divisibility conjecture. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

/-!
# Square divisibility for OEIS A146557

The sequence is defined here by Max Alekseyev's integer-valued formula. Its
identification with the geometric count is the OEIS author's formula and is
not re-proved here. In particular, the ordered matrix count is six times the
unordered geometric count; this module makes no formal claim about either count.

The new cyclic reindexing of positive three-part compositions gives
`3 * a n = n^2 * T n`. When three does not divide `n`, Euclid's lemma gives
`3 ∣ T n`; cancelling three proves Peter Bala's conjecture of July 24, 2025.
No totient decomposition or bounded enumeration is needed for this proof.
-/

namespace D5.S3.Factorization.CollinearTripleCountDivisibility

open Finset

/-- Compositions of `n` into three positive parts, represented by triples. -/
def triples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (n + 1)) ×ˢ ((range (n + 1)) ×ˢ (range (n + 1)))).filter
    (fun triple => 0 < triple.1 ∧ 0 < triple.2.1 ∧ 0 < triple.2.2 ∧
      triple.1 + triple.2.1 + triple.2.2 = n)

/-- Alekseyev's symmetric summand, with subtraction performed in the integers. -/
def summand (n : ℕ) (triple : ℕ × ℕ × ℕ) : ℤ :=
  (n : ℤ) * Nat.gcd (Nat.gcd triple.1 triple.2.1) triple.2.2 -
    Nat.gcd triple.1 n - Nat.gcd triple.2.1 n - Nat.gcd triple.2.2 n + 2

/-- OEIS A146557 defined by Alekseyev's formula, not by the geometric count. -/
def a (n : ℕ) : ℤ :=
  (n : ℤ) * ∑ triple ∈ triples n, summand n triple * triple.2.2

private theorem mem_triples {n : ℕ} {triple : ℕ × ℕ × ℕ} :
    triple ∈ triples n ↔ 0 < triple.1 ∧ 0 < triple.2.1 ∧ 0 < triple.2.2 ∧
      triple.1 + triple.2.1 + triple.2.2 = n := by
  simp only [triples, mem_filter, mem_product, mem_range]
  omega

private def rotate (triple : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (triple.2.1, triple.2.2, triple.1)

private theorem rotate_mem {n : ℕ} {triple : ℕ × ℕ × ℕ}
    (member : triple ∈ triples n) : rotate triple ∈ triples n := by
  rw [mem_triples] at member ⊢
  dsimp [rotate]
  omega

private theorem summand_rotate (n : ℕ) (triple : ℕ × ℕ × ℕ) :
    summand n (rotate triple) = summand n triple := by
  simp only [summand, rotate, Nat.gcd_comm, Nat.gcd_left_comm]
  ring

private theorem sum_rotate (n : ℕ) (weight : (ℕ × ℕ × ℕ) → ℤ) :
    ∑ triple ∈ triples n, weight (rotate triple) =
      ∑ triple ∈ triples n, weight triple := by
  apply sum_nbij' rotate (fun triple => rotate (rotate triple))
  · exact fun _ member => rotate_mem member
  · exact fun _ member => rotate_mem (rotate_mem member)
  · exact fun _ _ => rfl
  · exact fun _ _ => rfl
  · exact fun _ _ => rfl

/-- Cyclic symmetry turns the weighted sum into one third of the total moment. -/
theorem three_mul_a_eq (n : ℕ) :
    3 * a n = (n : ℤ) ^ 2 * ∑ triple ∈ triples n, summand n triple := by
  have first := sum_rotate n (fun triple => summand n triple * triple.2.2)
  have second := sum_rotate n (fun triple => summand n triple * triple.1)
  change (∑ triple ∈ triples n, summand n (rotate triple) * triple.1) = _ at first
  change (∑ triple ∈ triples n, summand n (rotate triple) * triple.2.1) = _ at second
  simp only [summand_rotate] at first second
  have moment :
      (∑ triple ∈ triples n, summand n triple * triple.1) +
        (∑ triple ∈ triples n, summand n triple * triple.2.1) +
        (∑ triple ∈ triples n, summand n triple * triple.2.2) =
          (n : ℤ) * ∑ triple ∈ triples n, summand n triple := by
    rw [← sum_add_distrib, ← sum_add_distrib, mul_sum]
    apply sum_congr rfl
    intro triple member
    have total : (triple.1 : ℤ) + triple.2.1 + triple.2.2 = n := by
      exact_mod_cast (mem_triples.mp member).2.2.2
    calc
      _ = summand n triple * ((triple.1 : ℤ) + triple.2.1 + triple.2.2) := by ring
      _ = (n : ℤ) * summand n triple := by rw [total, mul_comm]
  rw [second, first] at moment
  dsimp [a]
  calc
    _ = (n : ℤ) *
        ((∑ triple ∈ triples n, summand n triple * triple.2.2) +
          (∑ triple ∈ triples n, summand n triple * triple.2.2) +
          (∑ triple ∈ triples n, summand n triple * triple.2.2)) := by ring
    _ = _ := by rw [moment]; ring

/-- If three does not divide the index, it divides the total symmetric summand. -/
theorem three_dvd_summand_sum {n : ℕ} (h3 : ¬ 3 ∣ n) :
    (3 : ℤ) ∣ ∑ triple ∈ triples n, summand n triple := by
  have coprime : Nat.Coprime 3 (n ^ 2) :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr h3).pow_right 2
  have gcd_one : Int.gcd 3 ((n : ℤ) ^ 2) = 1 := by
    exact_mod_cast coprime.gcd_eq_one
  apply Int.dvd_of_dvd_mul_right_of_gcd_one _ gcd_one
  rw [← three_mul_a_eq]
  exact dvd_mul_right _ _

/-- Bala's A146557 conjecture for the sequence defined by Alekseyev's formula. -/
theorem sq_dvd_a {n : ℕ} (h3 : ¬ 3 ∣ n) : (n : ℤ) ^ 2 ∣ a n := by
  obtain ⟨quotient, total⟩ := three_dvd_summand_sum h3
  refine ⟨quotient, ?_⟩
  have identity := three_mul_a_eq n
  rw [total] at identity
  apply mul_left_cancel₀ (show (3 : ℤ) ≠ 0 by decide)
  calc
    3 * a n = (n : ℤ) ^ 2 * (3 * quotient) := identity
    _ = 3 * ((n : ℤ) ^ 2 * quotient) := by ring

#print axioms three_mul_a_eq
#print axioms three_dvd_summand_sum
#print axioms sq_dvd_a

end D5.S3.Factorization.CollinearTripleCountDivisibility
