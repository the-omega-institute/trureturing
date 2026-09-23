/- GID: D5/S3/Factorization/DivisorDoublingMultipleDividesSquare
   generality: G
   mirror-B: D5/B/S3/Factorization/DivisorDoublingMultipleDividesSquare
   mirror-E: none(waiver:factorisation-exponent-argument)
   anchors: [mathlib/module/Mathlib.NumberTheory.Divisors]
   utility: none
   digest: A multiple with fewer than twice as many divisors divides the square. -/

import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Factorization.DivisorDoublingMultipleDividesSquare

/-- Every positive multiple with fewer than twice as many divisors divides the square. -/
def claim : Prop :=
  ∀ n m : ℕ, 0 < n → 0 < m → n ∣ m →
    m.divisors.card < 2 * n.divisors.card → m ∣ n ^ 2

/-- The divisor-count bound forces every prime exponent of the multiple below twice the original. -/
theorem result : claim := by
  intro n m hn hm hnm hcard
  have hfac : n.factorization ≤ m.factorization :=
    (Nat.factorization_le_iff_dvd hn.ne' hm.ne').mpr hnm
  have hsupp : n.factorization.support ⊆ m.factorization.support :=
    Finsupp.support_mono hfac
  have hcardn :
      n.divisors.card =
        ∏ p ∈ n.factorization.support, (n.factorization p + 1) := by
    simpa only [Nat.support_factorization] using Nat.card_divisors hn.ne'
  have hcardm :
      m.divisors.card =
        ∏ p ∈ m.factorization.support, (m.factorization p + 1) := by
    simpa only [Nat.support_factorization] using Nat.card_divisors hm.ne'
  have hprod_mono (s : Finset ℕ) :
      (∏ p ∈ s, (n.factorization p + 1)) ≤
        ∏ p ∈ s, (m.factorization p + 1) := by
    exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
      (fun p _ ↦ Nat.add_le_add_right (hfac p) 1)
  have hprod_extend (s : Finset ℕ) (hs : s ⊆ m.factorization.support) :
      (∏ p ∈ s, (m.factorization p + 1)) ≤
        ∏ p ∈ m.factorization.support, (m.factorization p + 1) := by
    exact Finset.prod_le_prod_of_subset_of_one_le hs
      (fun _ _ ↦ Nat.zero_le _) (fun p _ _ ↦ by omega)
  apply (Nat.factorization_le_iff_dvd hm.ne' (pow_ne_zero 2 hn.ne')).mp
  rw [Nat.factorization_pow]
  intro q
  simp only [Finsupp.smul_apply, smul_eq_mul]
  by_contra hq
  have hbad : 2 * n.factorization q < m.factorization q := Nat.lt_of_not_ge hq
  by_cases hqn : q ∈ n.factorization.support
  · have hqfactor :
        2 * (n.factorization q + 1) ≤ m.factorization q + 1 := by
      omega
    have hrest :
        (∏ p ∈ n.factorization.support.erase q, (n.factorization p + 1)) ≤
          ∏ p ∈ n.factorization.support.erase q, (m.factorization p + 1) :=
      hprod_mono _
    have hdouble :
        2 * (∏ p ∈ n.factorization.support, (n.factorization p + 1)) ≤
          ∏ p ∈ n.factorization.support, (m.factorization p + 1) := by
      rw [← Finset.mul_prod_erase n.factorization.support
        (fun p ↦ n.factorization p + 1) hqn,
        ← Finset.mul_prod_erase n.factorization.support
          (fun p ↦ m.factorization p + 1) hqn]
      simpa only [mul_assoc] using Nat.mul_le_mul hqfactor hrest
    have hcount : 2 * n.divisors.card ≤ m.divisors.card := by
      rw [hcardn, hcardm]
      exact hdouble.trans (hprod_extend _ hsupp)
    omega
  · have hnq : n.factorization q = 0 := Finsupp.notMem_support_iff.mp hqn
    have hmq : 0 < m.factorization q := by
      omega
    have hqm : q ∈ m.factorization.support := Finsupp.mem_support_iff.mpr hmq.ne'
    have hinsert :
        insert q n.factorization.support ⊆ m.factorization.support :=
      Finset.insert_subset hqm hsupp
    have hqfactor : 2 ≤ m.factorization q + 1 := by
      omega
    have hdouble :
        2 * (∏ p ∈ n.factorization.support, (n.factorization p + 1)) ≤
          ∏ p ∈ insert q n.factorization.support, (m.factorization p + 1) := by
      rw [Finset.prod_insert hqn]
      exact Nat.mul_le_mul hqfactor (hprod_mono _)
    have hcount : 2 * n.divisors.card ≤ m.divisors.card := by
      rw [hcardn, hcardm]
      exact hdouble.trans (hprod_extend _ hinsert)
    omega
end D5.S3.Factorization.DivisorDoublingMultipleDividesSquare
