/- GID: D5/S1/Recurrence/FibonacciReturnSpectrum
   generality: G
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:universal-return-spectrum)
   anchors: []
   digest: The existing Lucas matrix period is exactly the Fibonacci sequence period and is divisibility-dual to an executable return content. -/

import D5.S1.Recurrence.LucasCompanion
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S1.Recurrence.FibonacciReturnSpectrum

open Matrix LucasEvenDescent LucasCompanion
open scoped Matrix

/-- Use the existing invertible Lucas companion, with Fibonacci parameters. -/
abbrev fibUnit (R : Type*) [CommRing R] : (Matrix (Fin 2) (Fin 2) R)ˣ :=
  companion (1 : R) (-1 : Rˣ)

/-- This is the existing matrix-period definition, specialized without a new order oracle. -/
noncomputable def period (q : ℕ) : ℕ :=
  matrixPeriod (1 : ZMod q) (-1 : (ZMod q)ˣ)

/-- An executable integer made from the two actual return defects.
At time zero it is zero, so every positive modulus is correctly admitted. -/
def returnContent (t : ℕ) : ℕ :=
  Nat.gcd (Nat.fib t) (Nat.fib (t + 1) - 1)

/-- Natural Fibonacci powers of the existing unit, over any commutative coefficient ring.
The lower-right entry uses ring subtraction, with no truncated-index convention. -/
theorem fibUnit_power (R : Type*) [CommRing R] (t : ℕ) :
    (↑(fibUnit R ^ t) : Matrix (Fin 2) (Fin 2) R) =
      !![(Nat.fib (t + 1) : R), (Nat.fib t : R);
         (Nat.fib t : R), (Nat.fib (t + 1) : R) - (Nat.fib t : R)] := by
  induction t with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  | succ t ih =>
      rw [pow_succ, Units.val_mul, ih]
      have hunit : (↑(fibUnit R) : Matrix (Fin 2) (Fin 2) R) = !![1, 1; 1, 0] := by
        simp [fibUnit, companion]
      rw [hunit]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Nat.fib_add_two,
          Nat.add_assoc, Nat.cast_add] <;> ring

/-- Equality to the matrix identity is exactly the two scalar return conditions. -/
theorem fibUnit_pow_eq_one_iff (q t : ℕ) :
    fibUnit (ZMod q) ^ t = 1 ↔
      (Nat.fib t : ZMod q) = 0 ∧ (Nat.fib (t + 1) : ZMod q) = 1 := by
  constructor
  · intro h
    have hm := congrArg Units.val h
    rw [fibUnit_power] at hm
    constructor
    · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 1 0) hm
    · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 0 0) hm
  · rintro ⟨h0, h1⟩
    apply Units.ext
    rw [fibUnit_power, h0, h1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem period_dvd_iff_pair (q t : ℕ) :
    period q ∣ t ↔
      (Nat.fib t : ZMod q) = 0 ∧ (Nat.fib (t + 1) : ZMod q) = 1 := by
  change orderOf (fibUnit (ZMod q)) ∣ t ↔ _
  rw [orderOf_dvd_iff_pow_eq_one, fibUnit_pow_eq_one_iff]

/-- The matrix order is the period of the actual entire Fibonacci sequence.
This theorem removes a possible matrix/sequence factor-of-two ambiguity. -/
theorem period_dvd_iff_sequence (q t : ℕ) :
    period q ∣ t ↔ ∀ n : ℕ, (Nat.fib (n + t) : ZMod q) = (Nat.fib n : ZMod q) := by
  constructor
  · intro h n
    have hu : fibUnit (ZMod q) ^ t = 1 := orderOf_dvd_iff_pow_eq_one.mp h
    have he : fibUnit (ZMod q) ^ (n + t) = fibUnit (ZMod q) ^ n := by
      rw [pow_add, hu, mul_one]
    have hm := congrArg Units.val he
    rw [fibUnit_power, fibUnit_power] at hm
    simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 1 0) hm
  · intro h
    apply (period_dvd_iff_pair q t).mpr
    constructor
    · simpa using h 0
    · simpa [Nat.add_comm] using h 1

/-- All return moduli are represented by the divisors of one computable integer. -/
theorem period_dvd_iff_dvd_returnContent (q t : ℕ) :
    period q ∣ t ↔ q ∣ returnContent t := by
  have hf : 1 ≤ Nat.fib (t + 1) := Nat.fib_pos.mpr (by omega)
  have hcast : ((Nat.fib (t + 1) - 1 : ℕ) : ZMod q) =
      (Nat.fib (t + 1) : ZMod q) - 1 := by
    rw [Nat.cast_sub hf, Nat.cast_one]
  rw [period_dvd_iff_pair, returnContent, Nat.dvd_gcd_iff]
  rw [← ZMod.natCast_eq_zero_iff (Nat.fib t) q,
      ← ZMod.natCast_eq_zero_iff (Nat.fib (t + 1) - 1) q, hcast, sub_eq_zero]

/-- Positive finite moduli have an actual positive least period, including q=1. -/
theorem period_pos (q : ℕ) (hq : 0 < q) : 0 < period q :=
  matrixPeriod_zmod_pos q hq 1 (-1)

/-- Refining a modular observation cannot shorten its least period. -/
theorem period_dvd_of_dvd {a b : ℕ} (hab : a ∣ b) : period a ∣ period b := by
  apply (period_dvd_iff_dvd_returnContent a (period b)).mpr
  exact hab.trans ((period_dvd_iff_dvd_returnContent b (period b)).mp (dvd_refl _))

/-- Joint modular observation synchronizes by lcm, without a coprimality assumption. -/
theorem period_lcm (a b : ℕ) :
    period (Nat.lcm a b) = Nat.lcm (period a) (period b) := by
  apply Nat.dvd_antisymm
  · apply (period_dvd_iff_dvd_returnContent _ _).mpr
    apply Nat.lcm_dvd
    · exact (period_dvd_iff_dvd_returnContent a _).mp (Nat.dvd_lcm_left _ _)
    · exact (period_dvd_iff_dvd_returnContent b _).mp (Nat.dvd_lcm_right _ _)
  · exact Nat.lcm_dvd (period_dvd_of_dvd (Nat.dvd_lcm_left a b))
      (period_dvd_of_dvd (Nat.dvd_lcm_right a b))

/-- A strong divisibility law for the RETURN CONTENT, not just for Fibonacci numbers. -/
theorem returnContent_gcd (s t : ℕ) :
    returnContent (Nat.gcd s t) = Nat.gcd (returnContent s) (returnContent t) := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact (period_dvd_iff_dvd_returnContent _ s).mp
        (((period_dvd_iff_dvd_returnContent _ (Nat.gcd s t)).mpr (dvd_refl _)).trans
          (Nat.gcd_dvd_left s t))
    · exact (period_dvd_iff_dvd_returnContent _ t).mp
        (((period_dvd_iff_dvd_returnContent _ (Nat.gcd s t)).mpr (dvd_refl _)).trans
          (Nat.gcd_dvd_right s t))
  · apply (period_dvd_iff_dvd_returnContent _ _).mp
    exact Nat.dvd_gcd
      ((period_dvd_iff_dvd_returnContent _ s).mpr (Nat.gcd_dvd_left _ _))
      ((period_dvd_iff_dvd_returnContent _ t).mpr (Nat.gcd_dvd_right _ _))

/-- Any positive return content is itself a modulus whose period divides its time. -/
theorem period_returnContent_dvd (t : ℕ) : period (returnContent t) ∣ t :=
  (period_dvd_iff_dvd_returnContent _ _).mpr (dvd_refl _)

/-- A first prime-power plateau is exactly a divisibility condition at the OLD least period. -/
theorem square_period_eq_iff (p : ℕ) :
    period (p ^ 2) = period p ↔ p ^ 2 ∣ returnContent (period p) := by
  constructor
  · intro h
    apply (period_dvd_iff_dvd_returnContent _ _).mp
    simpa only [h] using (dvd_refl (period p))
  · intro h
    apply Nat.dvd_antisymm
    · exact (period_dvd_iff_dvd_returnContent _ _).mpr h
    · apply period_dvd_of_dvd
      exact ⟨p, by simp [pow_two]⟩

end D5.S1.Recurrence.FibonacciReturnSpectrum
