/- GID: D5/S3/Factorization/IanakievPrimeExponentSumIterationReachesFive
   generality: G
   mirror-B: D5/B/S3/Factorization/IanakievPrimeExponentSumIterationReachesFive
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Factorization.Induction, mathlib/module/Mathlib.Data.Nat.Factorization.Basic, mathlib/module/Mathlib.Tactic.Linarith, mathlib/module/Mathlib.Tactic.NormNum]
   utility: none
   digest: Ianakiev's prime-exponent sum iteration reaches five from every integer above four. -/

import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Factorization.IanakievPrimeExponentSumIterationReachesFive

/-- OEIS A008474, the sum of each prime divisor and its exponent. -/
def F (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, (p + n.factorization p)

private theorem F_upper : ∀ n : ℕ, 2 ≤ n → F n ≤ n + 1 := by
  apply Nat.recOnPosPrimePosCoprime
  · intro p e hp he _
    have hvalue : F (p ^ e) = p + e := by
      rw [F, Nat.primeFactors_pow p he.ne', hp.primeFactors, hp.factorization_pow]
      simp
    rw [hvalue]
    have hpow : ∀ k : ℕ, 0 < k → p + k ≤ p ^ k + 1 := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
          by_cases hk0 : k = 0
          · subst k
            simp
          · have ih' := ih (by omega)
            have hpk : p ≤ p ^ k := Nat.le_self_pow (by omega) p
            have hq2 : 2 ≤ p ^ k := hp.two_le.trans hpk
            have hmul : 2 * p ^ k ≤ p ^ k * p := by
              simpa [mul_comm] using Nat.mul_le_mul_right (p ^ k) hp.two_le
            rw [pow_succ]
            omega
    exact hpow e he
  · omega
  · omega
  · intro a b ha hb hab hA hB _
    have hvalue : F (a * b) = F a + F b := by
      rw [F, F, F, hab.primeFactors_mul,
        Nat.factorization_mul (by omega) (by omega)]
      rw [Finset.sum_union hab.disjoint_primeFactors]
      apply congrArg₂ (fun x y => x + y)
      · apply Finset.sum_congr rfl
        intro p hp
        simp only [Finsupp.add_apply]
        have hnot : ¬p ∣ b := fun hpb =>
          (Nat.prime_of_mem_primeFactors hp).ne_one
            (Nat.eq_one_of_dvd_coprimes hab (Nat.dvd_of_mem_primeFactors hp) hpb)
        rw [Nat.factorization_eq_zero_of_not_dvd hnot, add_zero]
      · apply Finset.sum_congr rfl
        intro p hp
        simp only [Finsupp.add_apply]
        have hnot : ¬p ∣ a := fun hpa =>
          (Nat.prime_of_mem_primeFactors hp).ne_one
            (Nat.eq_one_of_dvd_coprimes hab hpa (Nat.dvd_of_mem_primeFactors hp))
        rw [Nat.factorization_eq_zero_of_not_dvd hnot, zero_add]
    rw [hvalue]
    have hsum : a + 1 + (b + 1) ≤ a * b + 1 := by
      by_cases ha2 : a = 2
      · subst a
        have hb2 : b ≠ 2 := by
          intro h
          subst b
          norm_num at hab
        omega
      · have ha3 : 3 ≤ a := by omega
        have haeq : a = (a - 3) + 3 := by omega
        have hbeq : b = (b - 2) + 2 := by omega
        rw [haeq, hbeq]
        nlinarith [Nat.zero_le ((a - 3) * (b - 2))]
    exact (Nat.add_le_add (hA (by omega)) (hB (by omega))).trans hsum

/-- Ianakiev's A008474 iteration conjecture. -/
theorem ianakiev_a008474 : ∀ m : ℕ, 4 < m → ∃ t : ℕ, F^[t] m = 5 := by
  sorry

#print axioms ianakiev_a008474

end D5.S3.Factorization.IanakievPrimeExponentSumIterationReachesFive
