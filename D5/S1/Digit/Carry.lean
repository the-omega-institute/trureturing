/- GID: D5/S1/Digit/Carry
   generality: I
   mirror-B: D5/B/S1/Digit/Carry
   mirror-E: none(waiver:algebraically-proved)
   anchors: [GICT-v3.6-I.2-definition-1.4, mathlib-data-nat-fib-zeckendorf]
   digest: Four local Fibonacci carry rules preserve the value of finite raw W digits. -/

import D5.S1.Digit.Raw

namespace D5.S1.Digit

open D5.S0.Conventions

/--
One local value-preserving rewrite of raw W digits. The untouched `rest` may
contain further mass at any index, so the constructors also apply to coefficients
larger than the displayed redex.
-/
inductive CarryStep : RawDigits → RawDigits → Prop where
  /-- `1@i + 1@(i+1) → 1@(i+2)`. -/
  | adjacent (rest : RawDigits) (i : ℕ) :
      CarryStep
        (rest + Finsupp.single i 1 + Finsupp.single (i + 1) 1)
        (rest + Finsupp.single (i + 2) 1)
  /-- `2@0 → 1@1`. -/
  | double_zero (rest : RawDigits) :
      CarryStep
        (rest + Finsupp.single 0 2)
        (rest + Finsupp.single 1 1)
  /-- `2@1 → 1@0 + 1@2`. -/
  | double_one (rest : RawDigits) :
      CarryStep
        (rest + Finsupp.single 1 2)
        (rest + Finsupp.single 0 1 + Finsupp.single 2 1)
  /-- `2@(i+2) → 1@i + 1@(i+3)`. -/
  | double_succ (rest : RawDigits) (i : ℕ) :
      CarryStep
        (rest + Finsupp.single (i + 2) 2)
        (rest + Finsupp.single i 1 + Finsupp.single (i + 3) 1)

/-- The general repeated-digit identity `2 W_(i+2) = W_i + W_(i+3)`. -/
theorem two_mul_wValue_add_two (i : ℕ) :
    2 * wValue (i + 2) = wValue i + wValue (i + 3) := by
  rw [show i + 3 = (i + 1) + 2 by omega, wValue_add_two,
    wValue_add_two]
  rw [show i + 1 + 1 = i + 2 by omega, wValue_add_two]
  omega

/-- The adjacent-pair carry preserves raw value. -/
theorem rawValue_carry_adjacent (rest : RawDigits) (i : ℕ) :
    rawValue (rest + Finsupp.single i 1 + Finsupp.single (i + 1) 1) =
      rawValue (rest + Finsupp.single (i + 2) 1) := by
  simp only [rawValue_add, rawValue_single, one_mul]
  rw [wValue_add_two]
  omega

/-- The exceptional lowest repeated digit `2 W_0 = W_1` preserves raw value. -/
theorem rawValue_carry_double_zero (rest : RawDigits) :
    rawValue (rest + Finsupp.single 0 2) =
      rawValue (rest + Finsupp.single 1 1) := by
  simp [rawValue_add]

/-- The exceptional second repeated digit `2 W_1 = W_0 + W_2` preserves raw value. -/
theorem rawValue_carry_double_one (rest : RawDigits) :
    rawValue (rest + Finsupp.single 1 2) =
      rawValue (rest + Finsupp.single 0 1 + Finsupp.single 2 1) := by
  simp [rawValue_add]

/-- The general repeated-digit carry preserves raw value. -/
theorem rawValue_carry_double_succ (rest : RawDigits) (i : ℕ) :
    rawValue (rest + Finsupp.single (i + 2) 2) =
      rawValue (rest + Finsupp.single i 1 + Finsupp.single (i + 3) 1) := by
  simp only [rawValue_add, rawValue_single, one_mul]
  rw [two_mul_wValue_add_two]
  omega

/-- Every local carry step preserves the represented natural number. -/
theorem rawValue_carryStep {before after : RawDigits}
    (step : CarryStep before after) : rawValue before = rawValue after := by
  cases step with
  | adjacent rest i => exact rawValue_carry_adjacent rest i
  | double_zero rest => exact rawValue_carry_double_zero rest
  | double_one rest => exact rawValue_carry_double_one rest
  | double_succ rest i => exact rawValue_carry_double_succ rest i

end D5.S1.Digit
