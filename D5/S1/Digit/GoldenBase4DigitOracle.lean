/- GID: D5/S1/Digit/GoldenBase4DigitOracle
   generality: I
   mirror-B: D5/B/S1/Digit/GoldenBase4DigitOracle
   mirror-E: none(waiver:exact-arithmetic-definition)
   anchors: []
   digest: Exact floor arithmetic supplies the base-four golden digit oracle and canonical power samples. -/

import D5.S0.Conventions.WDigits
import Mathlib.NumberTheory.Real.GoldenRatio

/- Library-search audit trail (2026-09-01):
   * `D5.S0.Conventions.WDigits` already exposes Mathlib's canonical Zeckendorf
     representation and reconstruction theorem; this node reuses that carrier.
   * Pinned Mathlib supplies the natural floor, finite remainders, and the
     golden ratio. No repository node paired the exact base-four digit oracle
     with the canonical W-coordinate sample of `4 ^ i`.
   * The occupied-index word below is an exact arithmetic sample carrier. A
     later node must add the bit-stream serialization and prove its MSD/LSD
     convention before importing the published Walnut transition table. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.GoldenBase4DigitOracle

open D5.S0.Conventions

/-- The exact integer prefix numerator `floor (4^(i+1) * phi)`. -/
noncomputable def prefixNumerator (i : Nat) : Nat :=
  ⌊(4 : Real) ^ (i + 1) * Real.goldenRatio⌋₊

/-- The `i`th base-four digit of the golden ratio, read as the final radix-four
remainder of the exact prefix numerator. -/
noncomputable def digit (i : Nat) : Fin 4 :=
  ⟨prefixNumerator i % 4, Nat.mod_lt _ (by norm_num)⟩

/-- The canonical Zeckendorf occupied-index representation of `4 ^ i`. -/
def powerOccupiedIndices (i : Nat) : List Nat :=
  wdigits (4 ^ i)

/-- Every power sample is a canonical Zeckendorf representation. -/
theorem powerOccupiedIndices_isCanonical (i : Nat) :
    (powerOccupiedIndices i).IsZeckendorfRep := by
  exact wdigits_isCanonical (4 ^ i)

/-- Decoding the canonical occupied indices recovers the sampled power exactly. -/
@[simp]
theorem decode_powerOccupiedIndices (i : Nat) :
    ((powerOccupiedIndices i).map Nat.fib).sum = 4 ^ i := by
  exact decode_wdigits (4 ^ i)

/-- The finite output carrier enforces the radix-four digit bound. -/
theorem digit_lt_four (i : Nat) : (digit i).val < 4 :=
  (digit i).isLt

/-- The oracle is definitionally the final radix-four remainder of the exact
floor prefix. -/
@[simp]
theorem digit_val (i : Nat) :
    (digit i).val = prefixNumerator i % 4 :=
  rfl

#print axioms powerOccupiedIndices_isCanonical
#print axioms decode_powerOccupiedIndices
#print axioms digit_lt_four

end D5.S1.Digit.GoldenBase4DigitOracle
