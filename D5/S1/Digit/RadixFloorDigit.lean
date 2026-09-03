/- GID: D5/S1/Digit/RadixFloorDigit
   generality: G
   mirror-B: D5/B/S1/Digit/RadixFloorDigit
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.Algebra.Order.Floor.Ring]
   digest: Successive floors define an exact bounded radix digit. -/

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.RadixFloorDigit

/-- The integral carry remainder between `floor (b*x)` and `b * floor x`. -/
noncomputable def digitInt (base : Nat) (x : Real) : Int :=
  ⌊(base : Real) * x⌋ - (base : Int) * ⌊x⌋

/-- A floor carry remainder is nonnegative. -/
theorem digitInt_nonneg (base : Nat) (x : Real) :
    0 ≤ digitInt base x := by
  rw [digitInt, sub_nonneg, Int.le_floor]
  push_cast
  exact mul_le_mul_of_nonneg_left (Int.floor_le x) (by positivity)

/-- For positive radix, a floor carry remainder is strictly smaller than the radix. -/
theorem digitInt_lt (base : Nat) (positive : 0 < base) (x : Real) :
    digitInt base x < (base : Int) := by
  have basePositive : (0 : Real) < base := by exact_mod_cast positive
  have h : (base : Real) * x < (base : Real) * (⌊x⌋ + 1) :=
    mul_lt_mul_of_pos_left (Int.lt_floor_add_one x) basePositive
  rw [digitInt, sub_lt_iff_lt_add, Int.floor_lt]
  push_cast
  push_cast at h
  linarith

/-- The exact radix digit as an element of `Fin base`. -/
noncomputable def digit (base : Nat) (positive : 0 < base) (x : Real) : Fin base where
  val := (digitInt base x).toNat
  isLt := by
    have nonnegative := digitInt_nonneg base x
    have bounded := digitInt_lt base positive x
    rw [Int.toNat_lt nonnegative]
    exact bounded

@[simp] theorem digit_val (base : Nat) (positive : 0 < base) (x : Real) :
    (digit base positive x).val = (digitInt base x).toNat := rfl

/-- Successive floors decompose into the previous floor and one bounded digit. -/
theorem floor_mul_decomposition (base : Nat) (x : Real) :
    ⌊(base : Real) * x⌋ = (base : Int) * ⌊x⌋ + digitInt base x := by
  simp [digitInt]

/-- The floor carry is simultaneously bounded and gives the exact radix decomposition. -/
theorem radix_floor_digit_bounds_and_decomposition
    (base : Nat) (positive : 0 < base) (x : Real) :
    0 ≤ digitInt base x ∧ digitInt base x < (base : Int) ∧
      ⌊(base : Real) * x⌋ = (base : Int) * ⌊x⌋ + digitInt base x := by
  exact ⟨digitInt_nonneg base x, digitInt_lt base positive x,
    floor_mul_decomposition base x⟩

#print axioms radix_floor_digit_bounds_and_decomposition

end D5.S1.Digit.RadixFloorDigit
