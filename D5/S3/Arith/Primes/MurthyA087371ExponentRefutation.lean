/- GID: D5/S3/Arith/Primes/MurthyA087371ExponentRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/MurthyA087371ExponentRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Primes/MurthyA087371ExponentRefutation.claim; result=D5/S3/Arith/Primes/MurthyA087371ExponentRefutation.result; claim=D5/S3/Arith/Primes/MurthyA087371ExponentRefutation.claim
   digest: Arbitrarily large prime gaps refute boundedness of the least positive prime-producing exponent in A087371. -/

import D5.S3.Arith.Primes.PrimeGap
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Find

/-! The boundedness assertion for the least positive exponent producing a prime above ten. -/

set_option autoImplicit false

namespace D5.S3.Arith.Primes.MurthyA087371ExponentRefutation

/-- The least positive exponent producing a prime strictly greater than ten,
or zero if no such exponent exists. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, 1 ≤ k ∧ Nat.Prime (10 ^ k + 2 * n - 1) ∧
      10 < 10 ^ k + 2 * n - 1 then Nat.find h else 0

/-- OEIS A087371, COMMENTS: "There exists a finite M such that a(n) < M for all n."
The entry has offset one; successful values must be primes strictly greater than ten. -/
def claim : Prop := ∃ M : ℕ, ∀ n : ℕ, 1 ≤ n → a n < M

/-- Every positive exponent occurs as the first successful exponent, so no bound exists. -/
theorem result : ¬ claim := by
  classical
  have hsurj : ∀ K : ℕ, 1 ≤ K → ∃ n : ℕ, 1 ≤ n ∧ a n = K := by
    intro K hK
    obtain ⟨i, hi⟩ := PrimeGap.exists_primeGap_ge (10 ^ K)
    let q := Nat.nth Nat.Prime i
    let p := Nat.nth Nat.Prime (i + 1)
    have hgap : 10 ^ K ≤ p - q := hi
    have hq : Nat.Prime q := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i
    have hp : Nat.Prime p := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (i + 1)
    have hqge : 2 ≤ q := hq.two_le
    have htge : 10 ≤ 10 ^ K := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (10 : ℕ)) hK
    have hple : 10 ^ K ≤ p := by omega
    have hpthreshold : 10 < p := by omega
    have hpne : p ≠ 2 := by omega
    have hteven : Even (10 ^ K) :=
      (by decide : Even (10 : ℕ)).pow_of_ne_zero (by omega : K ≠ 0)
    obtain ⟨m, hm⟩ := Nat.Odd.sub_even hple (hp.odd_of_ne_two hpne) hteven
    let n := m + 1
    have hsum : 10 ^ K + 2 * n - 1 = p := by dsimp [n]; omega
    have hnpos : 1 ≤ n := by dsimp [n]; omega
    have hearlier : ∀ j : ℕ, j < K → ¬ Nat.Prime (10 ^ j + 2 * n - 1) := by
      intro j hjK hr
      have hjpos : 0 < (10 : ℕ) ^ j := Nat.pow_pos (by decide)
      have hjlt : (10 : ℕ) ^ j < 10 ^ K := Nat.pow_lt_pow_of_lt (by decide) hjK
      have hleft : q < 10 ^ j + 2 * n - 1 := by omega
      have hright : 10 ^ j + 2 * n - 1 < p := by omega
      have hnext := (Nat.nth_add_one_le_iff Nat.infinite_setOfPred_prime hr).2 hleft
      change p ≤ 10 ^ j + 2 * n - 1 at hnext
      omega
    have hex : ∃ k : ℕ, 1 ≤ k ∧ Nat.Prime (10 ^ k + 2 * n - 1) ∧
        10 < 10 ^ k + 2 * n - 1 :=
      ⟨K, hK, hsum ▸ hp, hsum ▸ hpthreshold⟩
    refine ⟨n, hnpos, ?_⟩
    rw [a, dite_eq_left hex]
    apply (Nat.find_eq_iff hex).2
    refine ⟨⟨hK, hsum ▸ hp, hsum ▸ hpthreshold⟩, ?_⟩
    intro j hj hjprime
    exact hearlier j hj hjprime.2.1
  rintro ⟨M, hM⟩
  obtain ⟨n, hn, ha⟩ := hsurj (M + 1) (by omega)
  have hbound := hM n hn
  omega

end D5.S3.Arith.Primes.MurthyA087371ExponentRefutation
