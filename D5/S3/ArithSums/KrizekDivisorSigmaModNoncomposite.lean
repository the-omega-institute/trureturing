/- GID: D5/S3/ArithSums/KrizekDivisorSigmaModNoncomposite
   generality: G
   mirror-B: D5/B/S3/ArithSums/KrizekDivisorSigmaModNoncomposite
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc]
   utility: none
   digest: OEIS A300657 equality holds exactly at one and the primes. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (issue #8386; Proved)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.NumberTheory.ArithmeticFunction.Misc

open scoped BigOperators

namespace D5.S3.ArithSums.KrizekDivisorSigmaModNoncomposite

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- OEIS A300657: the sum of the divisor-sum residues over the divisors of `n`. -/
def a300657 (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, ArithmeticFunction.sigma 1 d % d

/-- OEIS A300657: its value equals `sigma(n) mod n` exactly at one and the primes. -/
theorem result (n : ℕ) (hn : 1 ≤ n) :
    a300657 n = ArithmeticFunction.sigma 1 n % n ↔ n = 1 ∨ n.Prime := by
  constructor
  · intro heq
    by_cases h1 : n = 1
    · exact Or.inl h1
    · right
      by_contra hnp
      have hn2 : 2 ≤ n := by omega
      let p := n.minFac
      have hp : p.Prime := Nat.minFac_prime h1
      have hσ : ArithmeticFunction.sigma 1 p % p = 1 := by
        rw [ArithmeticFunction.sigma_one_apply, hp.divisors,
          Finset.sum_insert (by simpa using hp.ne_one.symm)]
        simp [Nat.mod_eq_of_lt hp.one_lt]
      have hpdvd : p ∣ n := Nat.minFac_dvd n
      have hplt : p < n := (Nat.not_prime_iff_minFac_lt hn2).mp hnp
      have hn0 : n ≠ 0 := by omega
      have hnmem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hn0⟩
      have hpmem : p ∈ n.divisors.erase n := Finset.mem_erase.mpr ⟨hplt.ne, by
        exact Nat.mem_divisors.mpr ⟨hpdvd, hn0⟩⟩
      have hsplit :
          (∑ d ∈ n.divisors.erase n, ArithmeticFunction.sigma 1 d % d) +
              ArithmeticFunction.sigma 1 n % n = a300657 n := by
        simpa [a300657] using Finset.sum_erase_add n.divisors
          (fun d => ArithmeticFunction.sigma 1 d % d) hnmem
      have htail0 :
          (∑ d ∈ n.divisors.erase n, ArithmeticFunction.sigma 1 d % d) = 0 := by
        omega
      have hpzero : ArithmeticFunction.sigma 1 p % p = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp htail0 p hpmem
      rw [hσ] at hpzero
      omega
  · rintro (rfl | hp)
    · simp [a300657]
    · have hσ : ArithmeticFunction.sigma 1 n % n = 1 := by
        rw [ArithmeticFunction.sigma_one_apply, hp.divisors,
          Finset.sum_insert (by simpa using hp.ne_one.symm)]
        simp [Nat.mod_eq_of_lt hp.one_lt]
      simp [a300657, hp.divisors, hσ]

#print axioms result

end D5.S3.ArithSums.KrizekDivisorSigmaModNoncomposite
