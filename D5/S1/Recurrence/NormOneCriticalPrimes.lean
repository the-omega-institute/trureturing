/- GID: D5/S1/Recurrence/NormOneCriticalPrimes
   generality: I
   mirror-B: none(waiver:source-anchored-universal-refutation)
   mirror-E: none(waiver:all-parameters-and-primes)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Recurrence/NormOneCriticalPrimes.conjecture65vNecessary; result=D5/S1/Recurrence/NormOneCriticalPrimes.refutes_conjecture65v; claim=D5/S1/Recurrence/NormOneCriticalPrimes.conjecture65vNecessary
   digest: Prime fixed points of the actual norm-one Lucas recurrence are exactly the prime divisors of a-2; golden even iterates have an exact parity split, and a mixed-modulus family refutes Conjecture 6.5(v). -/

import D5.S1.Recurrence.LucasCompanion
import D5.S1.Scale.LucasDoubling
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S1.Recurrence.NormOneCriticalPrimes

open Matrix LucasEvenDescent LucasCompanion
open scoped Matrix

/-- The paper's (a,-1)-sequence, with the initial values 0 and 1. -/
def sequence (a : ℤ) (m : ℕ) (n : ℤ) : ZMod m :=
  lucasU (a : ZMod m) (1 : (ZMod m)ˣ) n

/-- The existing invertible companion order, not a new period oracle. -/
noncomputable def period (a : ℤ) (m : ℕ) : ℕ :=
  matrixPeriod (a : ZMod m) (1 : (ZMod m)ˣ)

/-- A return of the companion is precisely a translation period of the entire sequence. -/
theorem period_dvd_iff_sequence (a : ℤ) (m t : ℕ) :
    period a m ∣ t ↔ Function.Periodic (sequence a m) (t : ℤ) := by
  constructor
  · intro h n
    have hu : companion (a : ZMod m) (1 : (ZMod m)ˣ) ^ t = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp h
    simp only [sequence, lucasU, zpow_add, zpow_natCast, hu, mul_one]
  · intro h
    have h0 := h 0
    have h1 := h 1
    have hinit := lucas_recurrence (a : ZMod m) (1 : (ZMod m)ˣ)
    change lucasU (a : ZMod m) 1 (0 + (t : ℤ)) = lucasU (a : ZMod m) 1 0 at h0
    change lucasU (a : ZMod m) 1 (1 + (t : ℤ)) = lucasU (a : ZMod m) 1 1 at h1
    rw [zero_add, hinit.1] at h0
    rw [add_comm 1, hinit.2.1] at h1
    apply orderOf_dvd_iff_pow_eq_one.mpr
    apply Units.ext
    have hs := companion_power_shape (a : ZMod m) (1 : (ZMod m)ˣ) (t : ℤ)
    change (↑(companion (a : ZMod m) (1 : (ZMod m)ˣ) ^ (t : ℤ)) :
      Matrix (Fin 2) (Fin 2) (ZMod m)) = _ at hs
    rw [zpow_natCast, h0, h1] at hs
    rw [hs]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- At parameter two the actual companion is a nontrivial square-zero shear. -/
theorem parameter_two_power (R : Type*) [CommRing R] (t : ℕ) :
    (↑(companion (2 : R) (1 : Rˣ) ^ t) : Matrix (Fin 2) (Fin 2) R) =
      !![(t : R) + 1, -(t : R); (t : R), 1 - (t : R)] := by
  induction t with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  | succ t ih =>
      rw [pow_succ, Units.val_mul, ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [companion, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Every positive modulus is its own least period when the parameter is two modulo it. -/
theorem period_eq_modulus_of_parameter_two (a : ℤ) (m : ℕ)
    (ha : (a : ZMod m) = 2) : period a m = m := by
  unfold period matrixPeriod
  rw [ha]
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_iff_pow_eq_one.mpr
    apply Units.ext
    rw [parameter_two_power]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · have h := congrArg Units.val
      (pow_orderOf_eq_one (companion (2 : ZMod m) (1 : (ZMod m)ˣ)))
    rw [parameter_two_power] at h
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod m) => M 1 0) h
    apply (ZMod.natCast_eq_zero_iff _ m).mp
    simpa using h10

/-- Complete prime-level classification, including the prime two. -/
theorem prime_fixed_iff_parameter_two (a : ℤ) (p : ℕ) (hp : p.Prime) :
    period a p = p ↔ (a : ZMod p) = 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro h
    have hu := pow_orderOf_eq_one (companion (a : ZMod p) (1 : (ZMod p)ˣ))
    change companion (a : ZMod p) (1 : (ZMod p)ˣ) ^ period a p = 1 at hu
    rw [h] at hu
    have ht := ZMod.trace_pow_card
      (↑(companion (a : ZMod p) (1 : (ZMod p)ˣ)) : Matrix (Fin 2) (Fin 2) (ZMod p))
    rw [← Units.val_pow_eq_pow_val, hu] at ht
    simpa [companion, Matrix.trace_fin_two] using ht.symm
  · exact period_eq_modulus_of_parameter_two a p

/-- This is the exact divisibility condition behind the paper's critical-prime question. -/
theorem prime_fixed_iff_dvd_parameter_sub_two (a : ℤ) (p : ℕ) (hp : p.Prime) :
    period a p = p ↔ (p : ℤ) ∣ a - 2 := by
  rw [prime_fixed_iff_parameter_two a p hp,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd (a - 2) p]
  simp only [Int.cast_sub, Int.cast_ofNat, sub_eq_zero]

/-- Parity in the original golden power decides the factorization of the critical-prime target. -/
theorem golden_even_trace_excess (k : ℕ) :
    D5.S1.Scale.goldenLucas (2 * k) - 2 =
      if Even k then 5 * (Nat.fib k : ℤ) ^ 2 else D5.S1.Scale.goldenLucas k ^ 2 := by
  have ht := D5.S1.Scale.golden_lucas_two_mul k
  have hd := D5.S1.Scale.golden_lucas_discriminant k
  by_cases hk : Even k
  · rw [hk.neg_one_pow] at ht hd
    rw [if_pos hk]
    linarith
  · have ho : Odd k := Nat.not_even_iff_odd.mp hk
    rw [ho.neg_one_pow] at ht hd
    rw [if_neg hk]
    linarith

/-- The entire prime-level critical set for every even iterate of the original golden unit. -/
theorem prime_fixed_golden_even_iterate (k p : ℕ) (hp : p.Prime) :
    period (D5.S1.Scale.goldenLucas (2 * k)) p = p ↔
      if Even k then p = 5 ∨ p ∣ Nat.fib k else (p : ℤ) ∣ D5.S1.Scale.goldenLucas k := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [prime_fixed_iff_parameter_two _ p hp, ← sub_eq_zero]
  have h := congrArg (fun z : ℤ => (z : ZMod p)) (golden_even_trace_excess k)
  by_cases hk : Even k
  · rw [if_pos hk] at h ⊢
    push_cast at h
    rw [h, mul_eq_zero, sq_eq_zero_iff]
    change ((5 : ℕ) : ZMod p) = 0 ∨ (Nat.fib k : ZMod p) = 0 ↔ _
    rw [ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff,
      Nat.prime_dvd_prime_iff_eq hp Nat.prime_five]
  · rw [if_neg hk] at h ⊢
    push_cast at h
    rw [h, sq_eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- A single mixed modulus is fixed for an unbounded family in the paper's a=-1 mod 6 case. -/
theorem mixed_fixed_family (t : ℕ) : period (47 + 30 * (t : ℤ)) 15 = 15 := by
  apply period_eq_modulus_of_parameter_two
  push_cast
  rw [show (47 : ZMod 15) = 2 from rfl, show (30 : ZMod 15) = 0 from rfl,
    zero_mul, add_zero]

lemma fifteen_not_prime_power : ¬ ∃ p e : ℕ, p.Prime ∧ 15 = p ^ e := by
  rintro ⟨p, e, hp, he⟩
  have h3 : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow
    (show 3 ∣ p ^ e by rw [← he]; decide)
  have h5 : 5 ∣ p := Nat.prime_five.dvd_of_dvd_pow
    (show 5 ∣ p ^ e by rw [← he]; decide)
  have he3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
  have he5 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp h5
  omega

/-- A necessary consequence of the literal positive-parameter clause (v) in
Benfield-Lippard, arXiv:2404.08194v2, Conjecture 6.5. Allowing ALL primes here
only weakens their restriction to prime factors of the discriminant. -/
def conjecture65vNecessary : Prop :=
  ∀ a : ℤ, 2 < a → a % 6 = 5 → ∀ m : ℕ, 1 < m → period a m = m →
    (∃ p e : ℕ, p.Prime ∧ m = p ^ e) ∨ 6 ∣ m

/-- One fixed golden-trace parameter already contradicts that necessary consequence. -/
theorem refutes_conjecture65v : ¬ conjecture65vNecessary := by
  intro h
  have hf : period 47 15 = 15 := by simpa using mixed_fixed_family 0
  rcases h 47 (by decide) (by decide) 15 (by decide) hf with hp | hd
  · exact fifteen_not_prime_power hp
  · norm_num at hd

/-- The witness stays inside the original golden quadratic field: a=L_8=47. -/
theorem witness_is_golden_trace : D5.S1.Scale.goldenLucas 8 = 47 := by
  have h := D5.S1.Scale.golden_lucas_succ_eq_fib_add_fib 7
  norm_num [Nat.fib] at h
  exact h

#print axioms period_dvd_iff_sequence
#print axioms parameter_two_power
#print axioms period_eq_modulus_of_parameter_two
#print axioms prime_fixed_iff_parameter_two
#print axioms prime_fixed_iff_dvd_parameter_sub_two
#print axioms golden_even_trace_excess
#print axioms prime_fixed_golden_even_iterate
#print axioms mixed_fixed_family
#print axioms fifteen_not_prime_power
#print axioms refutes_conjecture65v
#print axioms witness_is_golden_trace

end D5.S1.Recurrence.NormOneCriticalPrimes
