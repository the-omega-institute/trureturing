/- GID: D5/S3/Arith/DivisorCountRadicalCoincidence
   generality: G
   mirror-B: D5/B/S3/Arith/DivisorCountRadicalCoincidence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A divisor count dividing the natural radical must equal that radical. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.Radical.NatInt

/- The public result is a general symbolic theorem; the `k = 12` example is non-public. -/

/-!
Library-search audit trail (pinned Mathlib v4.33.0):

* `Mathlib/NumberTheory/ArithmeticFunction/Misc.lean` supplies
  `Nat.card_divisors`, `ArithmeticFunction.sigma_zero_apply`,
  `ArithmeticFunction.cardFactors_multiset_prod`, and
  `ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree`.
* `Mathlib/RingTheory/Radical/NatInt.lean` supplies the natural-number radical,
  `Nat.radical_eq_prod_primeFactors`, and `Nat.primeFactors_radical`.
* `Mathlib/RingTheory/Radical/Basic.lean` supplies
  `UniqueFactorizationMonoid.squarefree_radical`; `Mathlib/Algebra/Squarefree/Basic.lean`
  supplies `Squarefree.squarefree_of_dvd`.
* `Mathlib/Data/Nat/PrimeFin.lean` and `Mathlib/Data/Nat/Squarefree.lean` supply
  `Nat.primeFactors_mono`, `Nat.prod_primeFactors_of_squarefree`, and the
  prime-factor-list characterizations used below.

The first search was attempted before the pinned dependency cache existed and found
no Mathlib source tree. After `make lean-cache-ensure` seeded that cache, the named
declarations above were found and reused rather than reproved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ArithmeticFunction.Omega

namespace D5.S3.Arith.DivisorCountRadicalCoincidence

private theorem primeFactors_card_le_cardFactors_card_divisors {k : ℕ} (hk : k ≠ 0) :
    k.primeFactors.card ≤ ArithmeticFunction.cardFactors k.divisors.card := by
  classical
  rw [Nat.card_divisors hk]
  have hproduct_ne : ∏ p ∈ k.primeFactors, (k.factorization p + 1) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (by intro p hp; omega)
  rw [show ArithmeticFunction.cardFactors
      (∏ p ∈ k.primeFactors, (k.factorization p + 1)) =
        ∑ p ∈ k.primeFactors,
          ArithmeticFunction.cardFactors (k.factorization p + 1) by
    have hmultiset_ne :
        (k.primeFactors.1.map fun p ↦ k.factorization p + 1).prod ≠ 0 := by
      exact hproduct_ne
    simpa only [Finset.prod_map_val, Finset.sum_map_val, Multiset.map_map,
      Function.comp_apply] using
      ArithmeticFunction.cardFactors_multiset_prod hmultiset_ne]
  simpa only [Finset.card_eq_sum_ones] using Finset.sum_le_sum fun p hp ↦ by
    obtain ⟨hpprime, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
    have hexponent : 0 < k.factorization p :=
      hpprime.factorization_pos_of_dvd hk hpdvd
    exact ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (by omega)

/-- Ctibor O. Zizka's conjecture in OEIS A070226/A120737: if the divisor count of a
positive natural number divides its squarefree kernel, then the two are equal. -/
theorem radical_eq_card_divisors_of_dvd {k : ℕ} (hk : 1 ≤ k)
    (hdiv : k.divisors.card ∣ UniqueFactorizationMonoid.radical k) :
    UniqueFactorizationMonoid.radical k = k.divisors.card := by
  have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
  have hradical_squarefree : Squarefree (UniqueFactorizationMonoid.radical k) :=
    UniqueFactorizationMonoid.squarefree_radical
  have hdivisors_squarefree : Squarefree k.divisors.card :=
    hradical_squarefree.squarefree_of_dvd hdiv
  have hprimeFactors_subset :
      k.divisors.card.primeFactors ⊆ k.primeFactors := by
    rw [← Nat.primeFactors_radical k]
    exact Nat.primeFactors_mono hdiv (Nat.radical_pos k).ne'
  have hcardFactors_eq :
      ArithmeticFunction.cardFactors k.divisors.card =
        k.divisors.card.primeFactors.card := by
    rw [ArithmeticFunction.cardFactors_apply, ← Nat.toFinset_factors]
    exact
      (List.toFinset_card_of_nodup hdivisors_squarefree.nodup_primeFactorsList).symm
  have hreverse_card : k.primeFactors.card ≤ k.divisors.card.primeFactors.card := by
    rw [← hcardFactors_eq]
    exact primeFactors_card_le_cardFactors_card_divisors hk_ne
  have hprimeFactors_eq : k.divisors.card.primeFactors = k.primeFactors :=
    Finset.eq_of_subset_of_card_le hprimeFactors_subset hreverse_card
  calc
    UniqueFactorizationMonoid.radical k = ∏ p ∈ k.primeFactors, p :=
      Nat.radical_eq_prod_primeFactors
    _ = ∏ p ∈ k.divisors.card.primeFactors, p := by rw [hprimeFactors_eq]
    _ = k.divisors.card := Nat.prod_primeFactors_of_squarefree hdivisors_squarefree

example :
    (12 : ℕ).divisors.card ∣ UniqueFactorizationMonoid.radical 12 ∧
      UniqueFactorizationMonoid.radical 12 = (12 : ℕ).divisors.card := by
  have hcard : (12 : ℕ).divisors.card = 6 := by decide
  have hprimeFactors : (12 : ℕ).primeFactors = {2, 3} := by
    have : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
    rw [this]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
      Nat.Prime.primeFactors Nat.prime_three]
    rfl
  rw [hcard, Nat.radical_eq_prod_primeFactors, hprimeFactors]
  norm_num

#print axioms radical_eq_card_divisors_of_dvd

end D5.S3.Arith.DivisorCountRadicalCoincidence
