/- GID: D5/S1/Recurrence/GoldenModReturnBridge
   generality: G
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:exact-existing-carrier-bridge)
   anchors: []
   digest: The existing golden algebra modulo any modulus has a faithful regular matrix representation, identifying its golden-unit order with the actual Fibonacci period. -/

import D5.S1.Recurrence.FibonacciReturnSpectrum
import D5.S3.Arith.GoldenApparition

set_option autoImplicit false

namespace D5.S1.Recurrence.GoldenModReturnBridge

open Matrix FibonacciReturnSpectrum
open D5.S3.Arith.GoldenApparition
open scoped Matrix

/-- Multiplication in the existing GoldenMod carrier, in coordinate order (b,a).
The formula is valid for every modulus, including prime powers and composites. -/
def regularRepresentation (q : ℕ) : GoldenMod q →+* Matrix (Fin 2) (Fin 2) (ZMod q) where
  toFun z := !![z.a + z.b, z.b; z.b, z.a]
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_mul' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem regularRepresentation_injective (q : ℕ) :
    Function.Injective (regularRepresentation q) := by
  intro x y h
  apply GoldenMod.ext
  · simpa [regularRepresentation] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 1 1) h
  · simpa [regularRepresentation] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 0 1) h

/-- The representation is the actual action of multiplication on both residue coordinates. -/
theorem regularRepresentation_mulVec (q : ℕ) (x y : GoldenMod q) :
    regularRepresentation q x *ᵥ ![y.b, y.a] = ![(x * y).b, (x * y).a] := by
  ext i
  fin_cases i <;>
    simp [regularRepresentation, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

lemma regularRepresentation_phi (q : ℕ) :
    regularRepresentation q (GoldenMod.phi : GoldenMod q) =
      (↑(fibUnit (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [regularRepresentation, GoldenMod.phi, fibUnit, LucasEvenDescent.companion]

/-- Both sides use existing definitions: GoldenMod.phi and LucasCompanion's invertible companion. -/
theorem golden_power_matrix (q t : ℕ) :
    regularRepresentation q ((GoldenMod.phi : GoldenMod q) ^ t) =
      (↑(fibUnit (ZMod q) ^ t) : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
  rw [map_pow, regularRepresentation_phi, Units.val_pow]

theorem period_dvd_iff_golden_power (q t : ℕ) :
    period q ∣ t ↔ (GoldenMod.phi : GoldenMod q) ^ t = 1 := by
  constructor
  · intro h
    apply regularRepresentation_injective q
    rw [golden_power_matrix, map_one]
    have hu : fibUnit (ZMod q) ^ t = 1 := orderOf_dvd_iff_pow_eq_one.mp h
    exact congrArg Units.val hu
  · intro h
    apply orderOf_dvd_iff_pow_eq_one.mpr
    apply Units.ext
    have he := congrArg (regularRepresentation q) h
    simpa only [golden_power_matrix, map_one, Units.val_one] using he

/-- No factor-of-two or exceptional-modulus assumption is hidden in the order identification. -/
theorem period_eq_golden_order (q : ℕ) :
    period q = orderOf (GoldenMod.phi : GoldenMod q) := by
  apply Nat.dvd_antisymm
  · exact (period_dvd_iff_golden_power q _).mpr (pow_orderOf_eq_one _)
  · exact orderOf_dvd_iff_pow_eq_one.mpr
      ((period_dvd_iff_golden_power q _).mp (dvd_refl _))

/-- The order condition is also a statement about reduction of the ORIGINAL golden integers. -/
theorem period_dvd_iff_reduced_phi (q t : ℕ) :
    period q ∣ t ↔ GoldenMod.reduce q (D5.S0.Carrier.phi ^ t) = 1 := by
  rw [period_dvd_iff_golden_power, map_pow]
  rfl

end D5.S1.Recurrence.GoldenModReturnBridge
