/- GID: D5/S3/Arith/Primes/FibonacciPrimePowerModularNonsquare
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciPrimePowerModularNonsquare
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Modular periods obstruct squares in twenty-eight Fibonacci quotient classes. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare

/-- A prime in any of twenty-eight residue classes modulo 120 has no square
Fibonacci quotient between successive powers. -/
theorem fibonacci_prime_power_modular_nonsquare (q k : ℕ) (hq : q.Prime)
    (hqge : 7 ≤ q) (h1 : q % 120 ≠ 1) (h49 : q % 120 ≠ 49)
    (h71 : q % 120 ≠ 71) (h119 : q % 120 ≠ 119) :
    0 < Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k) ∧
      ¬ IsSquare (Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k)) := by
  have hreduce (m : ℕ) (hzero : (Nat.fib 120 : ZMod m) = 0)
      (hone : (Nat.fib 121 : ZMod m) = 1) (n : ℕ) :
      (Nat.fib n : ZMod m) = (Nat.fib (n % 120) : ZMod m) := by
    have hstep : ∀ a : ℕ, (Nat.fib (a + 120) : ZMod m) = Nat.fib a := by
      intro a
      induction a using Nat.twoStepInduction with
      | zero => simpa using hzero
      | one => simpa [Nat.add_comm] using hone
      | more a ha ha1 =>
          have hrec : (Nat.fib (a + 2 + 120) : ZMod m) =
              (Nat.fib (a + 120) : ZMod m) +
                (Nat.fib (a + 1 + 120) : ZMod m) := by
            rw [show a + 2 + 120 = (a + 120) + 2 by omega,
              Nat.fib_add_two, Nat.cast_add]
          rw [hrec, ha, ha1, Nat.fib_add_two, Nat.cast_add]
    have hsplit : n % 120 + 120 * (n / 120) = n := Nat.mod_add_div n 120
    have hmul : ∀ j : ℕ,
        (Nat.fib (n % 120 + 120 * j) : ZMod m) = Nat.fib (n % 120) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
          have hs := hstep (n % 120 + 120 * j)
          have heq : n % 120 + 120 * (j + 1) =
              (n % 120 + 120 * j) + 120 := by omega
          rw [heq, hs]
          exact ih
    exact (congrArg (fun a : ℕ => (Nat.fib a : ZMod m)) hsplit.symm).trans
      (hmul (n / 120))
  have hred8 (n : ℕ) :
      (Nat.fib n : ZMod 8) = (Nat.fib (n % 120) : ZMod 8) :=
    hreduce 8 (by decide) (by decide) n
  have hred3 (n : ℕ) :
      (Nat.fib n : ZMod 3) = (Nat.fib (n % 120) : ZMod 3) :=
    hreduce 3 (by decide) (by decide) n
  have hred5 (n : ℕ) :
      (Nat.fib n : ZMod 5) = (Nat.fib (n % 120) : ZMod 5) :=
    hreduce 5 (by decide) (by decide) n
  let r := q % 120
  have hrlt : r < 120 := Nat.mod_lt q (by decide)
  have hprimeResidue (p : ℕ) (hp : p.Prime) (hpSmall : p < q)
      (hp120 : p ∣ 120) : r % p ≠ 0 := by
    intro hz
    have hmod : q % p = 0 := by
      simpa only [r, Nat.mod_mod_of_dvd q hp120] using hz
    have hdvd : p ∣ q := Nat.dvd_of_mod_eq_zero hmod
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd
    omega
  have hr2 : r % 2 ≠ 0 :=
    hprimeResidue 2 Nat.prime_two (by omega) (by decide)
  have hr3 : r % 3 ≠ 0 :=
    hprimeResidue 3 (by decide) (by omega) (by decide)
  have hr5 : r % 5 ≠ 0 :=
    hprimeResidue 5 Nat.prime_five (by omega) (by decide)
  have hfourFinite : ∀ a : Fin 120, a.val % 2 ≠ 0 → a.val % 3 ≠ 0 →
      a.val % 5 ≠ 0 → (a.val : ZMod 120) ^ 4 = 1 := by
    decide
  have hqfour : (q : ZMod 120) ^ 4 = 1 := by
    rw [← ZMod.natCast_mod q 120]
    exact hfourFinite ⟨r, hrlt⟩ hr2 hr3 hr5
  have hindex : q ^ k % 120 = r ^ (k % 4) % 120 := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ 120).mp
    simp only [Nat.cast_pow]
    calc
      (q : ZMod 120) ^ k = (q : ZMod 120) ^ (k % 4) := pow_eq_pow_mod k hqfour
      _ = (r : ZMod 120) ^ (k % 4) := by rw [← ZMod.natCast_mod q 120]
  have hnext : q ^ (k + 1) % 120 = r ^ (k % 4 + 1) % 120 := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ 120).mp
    simp only [Nat.cast_pow]
    calc
      (q : ZMod 120) ^ (k + 1) = (q : ZMod 120) ^ (k % 4 + 1) := by
        rw [pow_succ, pow_succ, pow_eq_pow_mod k hqfour]
      _ = (r : ZMod 120) ^ (k % 4 + 1) := by rw [← ZMod.natCast_mod q 120]
  have hcertificate : ∀ a : Fin 120,
      a.val % 2 ≠ 0 → a.val % 3 ≠ 0 → a.val % 5 ≠ 0 →
      a.val ≠ 1 → a.val ≠ 49 → a.val ≠ 71 → a.val ≠ 119 →
      ∀ j : Fin 4,
        let u := a.val ^ j.val % 120
        let v := a.val ^ (j.val + 1) % 120
        (∀ x : ZMod 8, IsSquare x →
            (Nat.fib u : ZMod 8) * x ≠ Nat.fib v) ∨
        (∀ x : ZMod 3, IsSquare x →
            (Nat.fib u : ZMod 3) * x ≠ Nat.fib v) ∨
        (∀ x : ZMod 5, IsSquare x →
            (Nat.fib u : ZMod 5) * x ≠ Nat.fib v) := by
    set_option maxRecDepth 10000 in
      decide
  have hjlt : k % 4 < 4 := Nat.mod_lt _ (by decide)
  have hcert := hcertificate ⟨r, hrlt⟩ hr2 hr3 hr5 h1 h49 h71 h119
    ⟨k % 4, hjlt⟩
  dsimp only at hcert
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
  have hproduct (m : ℕ)
      (hred : ∀ n : ℕ,
        (Nat.fib n : ZMod m) = (Nat.fib (n % 120) : ZMod m)) :
      (Nat.fib (r ^ (k % 4) % 120) : ZMod m) * (Q : ZMod m) =
        (Nat.fib (r ^ (k % 4 + 1) % 120) : ZMod m) := by
    have hc := congrArg (fun n : ℕ => (n : ZMod m)) hmul
    simp only [Nat.cast_mul] at hc
    rw [hred (q ^ k), hred (q ^ (k + 1)), hindex, hnext] at hc
    exact hc
  refine ⟨Nat.div_pos (Nat.le_of_dvd hnumpos hdiv) hdenpos, ?_⟩
  intro hsq
  rcases hcert with hbad8 | hbad3 | hbad5
  · exact hbad8 _ (hsq.map (Nat.castRingHom (ZMod 8))) (hproduct 8 hred8)
  · exact hbad3 _ (hsq.map (Nat.castRingHom (ZMod 3))) (hproduct 3 hred3)
  · exact hbad5 _ (hsq.map (Nat.castRingHom (ZMod 5))) (hproduct 5 hred5)

#print axioms fibonacci_prime_power_modular_nonsquare

end D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare
