/- GID: D5/S1/Digit/Addition
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   digest: Local normalization proves Zeckendorf digit addition is closed and canonical. -/

import D5.S1.Digit.Normalize

namespace D5.S1.Digit

open D5.S0.Conventions

/-- The canonical Zeckendorf W string of a natural number. -/
def Z (n : ℕ) : WDigitString :=
  wEncoding n

/-- Shift a canonical mathlib Fibonacci-index string into zero-based raw W digits. -/
noncomputable def toRaw (digits : WDigitString) : RawDigits :=
  rawOfZeckendorf digits.1

/-- `toRaw` preserves the canonicality carried by its subtype input. -/
theorem canonicalRaw_toRaw (digits : WDigitString) : CanonicalRaw (toRaw digits) :=
  canonicalRaw_rawOfZeckendorf digits.2

/-- `toRaw` preserves the Fibonacci sum represented by a canonical string. -/
theorem rawValue_toRaw (digits : WDigitString) :
    rawValue (toRaw digits) = (digits.1.map Nat.fib).sum :=
  rawValue_rawOfZeckendorf digits.2

/-- Decoding the canonical digits `Z n` recovers `n`. -/
@[simp] theorem rawValue_toRaw_Z (n : ℕ) : rawValue (toRaw (Z n)) = n := by
  rw [rawValue_toRaw]
  exact Nat.sum_zeckendorf_fib n

/--
Zeckendorf addition closure: adding two canonical raw strings and then performing
the deterministic local normalization gives the canonical string for the sum.
-/
theorem zeck_add (m n : ℕ) :
    toRaw (Z (m + n)) = normalize (toRaw (Z m) + toRaw (Z n)) := by
  apply canonicalRaw_unique (canonicalRaw_toRaw _)
    (normalize_canonical _)
  rw [rawValue_toRaw_Z, rawValue_normalize, rawValue_add,
    rawValue_toRaw_Z, rawValue_toRaw_Z]

end D5.S1.Digit
