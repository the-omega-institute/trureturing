/- GID: D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo
   generality: G
   mirror-B: D5/B/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.NumberTheory.Divisors, mathlib/module/Mathlib.Data.Nat.Prime.Basic, mathlib/module/Mathlib.Tactic]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.claim; result=D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.result; claim=D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.claim
   digest: The literal offset-zero power-of-two comment is refuted at zero, while its positive-index form is studied. -/

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace D5.S3.Factorization.GerasimovLeastEvenDivisorCountPowerOfTwo

def E (m : ℕ) : ℕ := (m.divisors.filter Even).card

noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | 0 < m ∧ E m = n}

def claim : Prop := ∀ n : ℕ, a n = 2 ^ n → Nat.Prime n ∨ n = 1

private theorem a_zero_eq_one : a 0 = 1 := by
  have hmem : 1 ∈ {m : ℕ | 0 < m ∧ E m = 0} := by
    simp [E]
  have hle : a 0 ≤ 1 := by
    exact Nat.sInf_le hmem
  have hs : a 0 ∈ {m : ℕ | 0 < m ∧ E m = 0} := by
    exact Nat.sInf_mem ⟨1, hmem⟩
  have hpos : 0 < a 0 := hs.1
  omega

theorem result : ¬ claim := by
  intro h
  have hbad : Nat.Prime 0 ∨ (0 : ℕ) = 1 := h 0 (by simp [a_zero_eq_one])
  cases hbad with
  | inl hp => exact Nat.not_prime_zero hp
  | inr h01 => omega

end D5.S3.Factorization.GerasimovLeastEvenDivisorCountPowerOfTwo
