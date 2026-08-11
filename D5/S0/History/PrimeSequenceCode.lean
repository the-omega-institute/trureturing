/- GID: D5/S0/History/PrimeSequenceCode
   generality: G
   mirror-B: D5/B/S0/History/PrimeSequenceCode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Shifted prime-power products injectively encode finite natural sequences. -/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.PrimeCounting

open scoped BigOperators

/- Provenance: pinned Mathlib supplies primality and injectivity of the
   increasing enumeration of primes (`Nat.prime_nth_prime`,
   `Nat.nth_injective`) and factorization of finite products and prime powers
   (`Nat.factorization_prod_apply`, `Nat.Prime.factorization_pow`). No direct
   theorem packages the shifted-exponent finite-sequence injection. -/

namespace D5.S0.History.PrimeSequenceCode

/-- Encode a finite sequence by assigning its `i`th entry, shifted by one, to
the exponent of the `i`th prime. The shift makes sequence length visible in
the prime support even when the final entries are zero. -/
noncomputable def primeSequenceCode (xs : List Nat) : Nat :=
  (Finset.range xs.length).prod fun i =>
    Nat.nth Nat.Prime i ^ (xs.getD i 0 + 1)

private theorem factorization_primeSequenceCode_apply (xs : List Nat) (i : Nat) :
    (primeSequenceCode xs).factorization (Nat.nth Nat.Prime i) =
      if i < xs.length then xs.getD i 0 + 1 else 0 := by
  rw [primeSequenceCode, Nat.factorization_prod_apply]
  · have hnth : Function.Injective (Nat.nth Nat.Prime) :=
      Nat.nth_injective Nat.infinite_setOf_prime
    by_cases hi : i < xs.length
    · rw [if_pos hi, Finset.sum_eq_single i]
      · simp [Nat.prime_nth_prime]
      · intro j hj hji
        simp [Nat.prime_nth_prime, hnth.ne hji]
      · simp [hi]
    · rw [if_neg hi]
      apply Finset.sum_eq_zero
      intro j hj
      have hji : Ne j i := by
        intro equality
        subst j
        exact hi (Finset.mem_range.mp hj)
      simp [Nat.prime_nth_prime, hnth.ne hji]
  · intro j hj
    exact pow_ne_zero _ (Nat.prime_nth_prime j).ne_zero

/-- Shifted prime-power coding is injective on finite natural sequences. Equal
codes have equal prime exponents; the first missing prime forces equal lengths,
and the remaining exponents recover every sequence entry. -/
theorem prime_sequence_code_injective : Function.Injective primeSequenceCode := by
  intro xs ys hcode
  have hfactorization : (primeSequenceCode xs).factorization =
      (primeSequenceCode ys).factorization := congrArg Nat.factorization hcode
  have hlength : xs.length = ys.length := by
    apply le_antisymm
    · by_contra hnot
      have hy := congrArg
        (fun f : Finsupp Nat Nat => f (Nat.nth Nat.Prime ys.length)) hfactorization
      rw [factorization_primeSequenceCode_apply,
        factorization_primeSequenceCode_apply] at hy
      simp only [lt_self_iff_false, reduceIte, not_le.mp hnot] at hy
      omega
    · by_contra hnot
      have hx := congrArg
        (fun f : Finsupp Nat Nat => f (Nat.nth Nat.Prime xs.length)) hfactorization
      rw [factorization_primeSequenceCode_apply,
        factorization_primeSequenceCode_apply] at hx
      simp only [lt_self_iff_false, reduceIte, not_le.mp hnot] at hx
      omega
  apply List.ext_get
  · exact hlength
  · intro n hnx hny
    have hentry := congrArg
      (fun f : Finsupp Nat Nat => f (Nat.nth Nat.Prime n)) hfactorization
    rw [factorization_primeSequenceCode_apply,
      factorization_primeSequenceCode_apply] at hentry
    simp only [hnx, hny, reduceIte] at hentry
    simpa [List.getD_eq_getElem?_getD, hnx, hny] using Nat.add_right_cancel hentry

end D5.S0.History.PrimeSequenceCode
