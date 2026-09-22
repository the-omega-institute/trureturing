/- GID: D5/S3/Arith/Primes/PrimeGap
   generality: G
   mirror-B: D5/B/S3/Arith/Primes/PrimeGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Prime.Nth, mathlib/module/Mathlib.Data.Nat.PrimeFin]
   utility: none
   digest: The gap after the n-th prime is positive and takes arbitrarily large values. -/

import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
set_option autoImplicit false
namespace D5.S3.Arith.Primes.PrimeGap

/-- The gap after the zero-indexed `n`-th prime. -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- Every gap between consecutive primes is positive. -/
theorem primeGap_pos (n : ℕ) : 0 < primeGap n := by
  exact Nat.sub_pos_of_lt
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self n))

/-- Factorial intervals without primes yield arbitrarily large consecutive prime gaps. -/
theorem exists_primeGap_ge (N : ℕ) : ∃ n : ℕ, N ≤ primeGap n := by
  let m := N + 2
  have hfac : 0 < m.factorial := Nat.factorial_pos m
  have hcomposite : ∀ k : ℕ, 2 ≤ k → k ≤ m → ¬Nat.Prime (m.factorial + k) := by
    intro k hk hkm
    have hdvd : k ∣ m.factorial + k :=
      dvd_add (Nat.dvd_factorial (by omega) hkm) (dvd_refl k)
    exact Nat.not_prime_of_dvd_of_lt hdvd hk (by omega)
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hex : ∃ j : ℕ, m.factorial + 1 < Nat.nth Nat.Prime j := by
    refine ⟨m.factorial + 2, ?_⟩
    have hle : m.factorial + 2 ≤ Nat.nth Nat.Prime (m.factorial + 2) :=
      hmono.id_le (m.factorial + 2)
    omega
  let j := Nat.find hex
  have hj : m.factorial + 1 < Nat.nth Nat.Prime j := Nat.find_spec hex
  have hjpos : 0 < j := by
    by_contra h
    have hjzero : j = 0 := by omega
    rw [hjzero, Nat.nth_prime_zero_eq_two] at hj
    omega
  have hprev : Nat.nth Nat.Prime (j - 1) ≤ m.factorial + 1 := by
    have hmin := Nat.find_min hex (show j - 1 < j by omega)
    omega
  have hnext : m.factorial + m < Nat.nth Nat.Prime j := by
    by_contra h
    have hklo : 2 ≤ Nat.nth Nat.Prime j - m.factorial := by omega
    have hkhi : Nat.nth Nat.Prime j - m.factorial ≤ m := by omega
    have hnot := hcomposite (Nat.nth Nat.Prime j - m.factorial) hklo hkhi
    have heq : m.factorial + (Nat.nth Nat.Prime j - m.factorial) =
        Nat.nth Nat.Prime j := by omega
    rw [heq] at hnot
    exact hnot (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime j)
  refine ⟨j - 1, ?_⟩
  unfold primeGap
  have hsucc : j - 1 + 1 = j := by omega
  rw [hsucc]
  dsimp [m] at hnext hprev
  omega

end D5.S3.Arith.Primes.PrimeGap
