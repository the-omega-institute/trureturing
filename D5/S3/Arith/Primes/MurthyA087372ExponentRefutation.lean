/- GID: D5/S3/Arith/Primes/MurthyA087372ExponentRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/MurthyA087372ExponentRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Primes/MurthyA087372ExponentRefutation.claim; result=D5/S3/Arith/Primes/MurthyA087372ExponentRefutation.result; claim=D5/S3/Arith/Primes/MurthyA087372ExponentRefutation.claim
   digest: Arbitrarily large prime gaps refute boundedness of the least positive prime-producing exponent in A087372. -/

import D5.S3.Arith.Primes.PrimeGap
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Find

/-! The boundedness assertion for the least positive prime-producing exponent. -/

set_option autoImplicit false

namespace D5.S3.Arith.Primes.MurthyA087372ExponentRefutation

/-- The least positive exponent producing a prime, or zero if no such exponent exists. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, 1 ≤ k ∧ Nat.Prime (3 ^ k + 2 * n) then Nat.find h else 0

/-- OEIS A087372, COMMENTS: "There exists a finite M such that a(n) < M for all n."
The entry has offset one; its example a(23) = 3 specifies positive exponents. -/
def claim : Prop := ∃ M : ℕ, ∀ n : ℕ, 1 ≤ n → a n < M

/-- Every positive exponent occurs as the first successful exponent, so no bound exists. -/
theorem result : ¬ claim := by
  classical
  have hsurj : ∀ K : ℕ, 1 ≤ K → ∃ n : ℕ, 1 ≤ n ∧ a n = K := by
    intro K hK
    obtain ⟨i, hi⟩ := PrimeGap.exists_primeGap_ge (3 ^ K)
    let q := Nat.nth Nat.Prime i
    let p := Nat.nth Nat.Prime (i + 1)
    have hgap : 3 ^ K ≤ p - q := hi
    have hq : Nat.Prime q := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i
    have hp : Nat.Prime p := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (i + 1)
    have hqge : 2 ≤ q := hq.two_le
    have htge : 3 ≤ 3 ^ K := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3 : ℕ)) hK
    have hple : 3 ^ K ≤ p := by omega
    have hpne : p ≠ 2 := by omega
    have htodd : Odd (3 ^ K) := (by decide : Odd (3 : ℕ)).pow
    obtain ⟨n, hn⟩ := Nat.Odd.sub_odd (hp.odd_of_ne_two hpne) htodd
    have hsum : 3 ^ K + 2 * n = p := by omega
    have hnpos : 1 ≤ n := by omega
    have hearlier : ∀ j : ℕ, 1 ≤ j → j < K → ¬ Nat.Prime (3 ^ j + 2 * n) := by
      intro j hj hjK hr
      have hjpos : 0 < (3 : ℕ) ^ j := Nat.pow_pos (by decide)
      have hjlt : (3 : ℕ) ^ j < 3 ^ K := Nat.pow_lt_pow_of_lt (by decide) hjK
      have hleft : q < 3 ^ j + 2 * n := by omega
      have hright : 3 ^ j + 2 * n < p := by omega
      have hnext := (Nat.nth_add_one_le_iff Nat.infinite_setOfPred_prime hr).2 hleft
      change p ≤ 3 ^ j + 2 * n at hnext
      omega
    have hex : ∃ k : ℕ, 1 ≤ k ∧ Nat.Prime (3 ^ k + 2 * n) :=
      ⟨K, hK, hsum ▸ hp⟩
    refine ⟨n, hnpos, ?_⟩
    rw [a, dite_eq_left hex]
    apply (Nat.find_eq_iff hex).2
    refine ⟨⟨hK, hsum ▸ hp⟩, ?_⟩
    intro j hj hjprime
    exact hearlier j hjprime.1 hj hjprime.2
  rintro ⟨M, hM⟩
  obtain ⟨n, hn, ha⟩ := hsurj (M + 1) (by omega)
  have hbound := hM n hn
  omega

end D5.S3.Arith.Primes.MurthyA087372ExponentRefutation
