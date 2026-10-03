/- GID: D5/S3/Arith/Primes/FibonacciPrimePowerMod31Nonsquare
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciPrimePowerMod31Nonsquare
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: A modulus-thirty-one orbit obstructs square Fibonacci quotients in two prime classes. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare

/-- In the two residue classes, successive prime-power Fibonacci quotients
alternate between two nonsquare residues modulo thirty-one. -/
theorem fibonacci_prime_power_mod31_nonsquare (q k : ℕ) (hq : q.Prime)
    (hqge : 7 ≤ q) (hclass : q % 120 = 49 ∨ q % 120 = 71) :
    0 < Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k) ∧
      (Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k)) % 31 =
        (if k % 2 = 0 then 27 else 23) ∧
      ¬ IsSquare (Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k)) := by
  have hperiod : ∀ a : ℕ, (Nat.fib (a + 30) : ZMod 31) = Nat.fib a := by
    intro a
    induction a using Nat.twoStepInduction with
    | zero => decide
    | one => simpa [Nat.add_comm] using
        (show (Nat.fib 31 : ZMod 31) = 1 by decide)
    | more a ha ha1 =>
        have hrec : (Nat.fib (a + 2 + 30) : ZMod 31) =
            (Nat.fib (a + 30) : ZMod 31) +
              (Nat.fib (a + 1 + 30) : ZMod 31) := by
          rw [show a + 2 + 30 = (a + 30) + 2 by omega,
            Nat.fib_add_two, Nat.cast_add]
        rw [hrec, ha, ha1, Nat.fib_add_two, Nat.cast_add]
  have hreduce (n : ℕ) :
      (Nat.fib n : ZMod 31) = (Nat.fib (n % 30) : ZMod 31) := by
    have hsplit : n % 30 + 30 * (n / 30) = n := Nat.mod_add_div n 30
    have hmul : ∀ j : ℕ,
        (Nat.fib (n % 30 + 30 * j) : ZMod 31) = Nat.fib (n % 30) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
          have hs := hperiod (n % 30 + 30 * j)
          have heq : n % 30 + 30 * (j + 1) =
              (n % 30 + 30 * j) + 30 := by omega
          rw [heq, hs]
          exact ih
    exact (congrArg (fun a : ℕ => (Nat.fib a : ZMod 31)) hsplit.symm).trans
      (hmul (n / 30))
  have hqmod : q % 30 = 11 ∨ q % 30 = 19 := by
    rcases hclass with h | h <;> omega
  have hqtwo : (q : ZMod 30) ^ 2 = 1 := by
    rw [← ZMod.natCast_mod q 30]
    rcases hqmod with h | h <;> rw [h] <;> decide
  have hindex (j : ℕ) :
      q ^ j % 30 = if j % 2 = 0 then 1 else q % 30 := by
    have heq : ((q ^ j : ℕ) : ZMod 30) =
        ((if j % 2 = 0 then 1 else q % 30 : ℕ) : ZMod 30) := by
      simp only [Nat.cast_pow]
      rw [pow_eq_pow_mod j hqtwo]
      by_cases hj : j % 2 = 0
      · simp [hj]
      · have hjone : j % 2 = 1 := by omega
        simp [hjone, ZMod.natCast_mod]
    have hmod := (ZMod.natCast_eq_natCast_iff' (q ^ j)
      (if j % 2 = 0 then 1 else q % 30) 30).mp heq
    have hrange : (if j % 2 = 0 then 1 else q % 30) < 30 := by
      split_ifs <;> omega
    rwa [Nat.mod_eq_of_lt hrange] at hmod
  have hphase (j : ℕ) :
      (Nat.fib (q ^ j) : ZMod 31) = if j % 2 = 0 then 1 else 27 := by
    rw [hreduce (q ^ j), hindex j]
    by_cases hj : j % 2 = 0
    · simp [hj]
    · simp only [if_neg hj]
      rcases hqmod with h | h <;> rw [h] <;> decide
  have hdenpos : 0 < Nat.fib (q ^ k) :=
    Nat.fib_pos.mpr (pow_pos hq.pos k)
  have hnumpos : 0 < Nat.fib (q ^ (k + 1)) :=
    Nat.fib_pos.mpr (pow_pos hq.pos (k + 1))
  have hdiv : Nat.fib (q ^ k) ∣ Nat.fib (q ^ (k + 1)) := by
    apply Nat.fib_dvd
    refine ⟨q, ?_⟩
    simp [pow_succ, mul_comm]
  let Q := Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k)
  have hmul : Nat.fib (q ^ k) * Q = Nat.fib (q ^ (k + 1)) :=
    Nat.mul_div_cancel' hdiv
  have hproduct :
      (Nat.fib (q ^ k) : ZMod 31) * (Q : ZMod 31) =
        (Nat.fib (q ^ (k + 1)) : ZMod 31) := by
    simpa only [Nat.cast_mul] using
      congrArg (fun n : ℕ => (n : ZMod 31)) hmul
  have hQcast : (Q : ZMod 31) =
      (if k % 2 = 0 then 27 else 23 : ℕ) := by
    by_cases hk : k % 2 = 0
    · have hnext : (k + 1) % 2 ≠ 0 := by omega
      have hprev : (Nat.fib (q ^ k) : ZMod 31) = 1 := by
        simpa [hk] using hphase k
      have hnew : (Nat.fib (q ^ (k + 1)) : ZMod 31) = 27 := by
        simpa [hnext] using hphase (k + 1)
      rw [hprev, hnew] at hproduct
      simpa [hk] using hproduct
    · have hnext : (k + 1) % 2 = 0 := by omega
      have hprev : (Nat.fib (q ^ k) : ZMod 31) = 27 := by
        simpa [hk] using hphase k
      have hnew : (Nat.fib (q ^ (k + 1)) : ZMod 31) = 1 := by
        simpa [hnext] using hphase (k + 1)
      rw [hprev, hnew] at hproduct
      have h27nz : (27 : ZMod 31) ≠ 0 := by decide
      have h27inv : (27 : ZMod 31) * 23 = 1 := by decide
      letI : Fact (Nat.Prime 31) := ⟨by decide⟩
      have h23 : (Q : ZMod 31) = 23 :=
        mul_left_cancel₀ h27nz (hproduct.trans h27inv.symm)
      simpa [hk] using h23
  have hQmod : Q % 31 = if k % 2 = 0 then 27 else 23 := by
    by_cases hk : k % 2 = 0
    · have hc : (Q : ZMod 31) = 27 := by simpa [hk] using hQcast
      have hr := (ZMod.natCast_eq_natCast_iff' Q 27 31).mp hc
      simpa [hk] using hr
    · have hc : (Q : ZMod 31) = 23 := by simpa [hk] using hQcast
      have hr := (ZMod.natCast_eq_natCast_iff' Q 23 31).mp hc
      simpa [hk] using hr
  have hQnonsquare : ¬ IsSquare Q := by
    intro hsq
    have hsq31 : IsSquare (Q : ZMod 31) :=
      hsq.map (Nat.castRingHom (ZMod 31))
    by_cases hk : k % 2 = 0
    · rw [hQcast, if_pos hk] at hsq31
      exact (by decide : ¬ IsSquare (27 : ZMod 31)) hsq31
    · rw [hQcast, if_neg hk] at hsq31
      exact (by decide : ¬ IsSquare (23 : ZMod 31)) hsq31
  exact ⟨Nat.div_pos (Nat.le_of_dvd hnumpos hdiv) hdenpos, hQmod,
    hQnonsquare⟩

#print axioms fibonacci_prime_power_mod31_nonsquare

end D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare
