/- GID: D5/S1/Digit/PrimeAxisTable
   generality: I
   mirror-B: D5/B/S1/Digit/PrimeAxisTable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime-indexed canonical W digits decode finite exponent tables. -/

import D5.S1.Digit.Raw
import Mathlib.Data.Nat.Prime.Basic

namespace D5.S1.Digit

open D5.S0.Conventions

/-- A prime coordinate in a factorization table. -/
abbrev PrimeAxis := {p : ℕ // Nat.Prime p}

/-- Canonical W digits on finitely many prime axes. -/
structure PrimeAxisTable where
  digits : PrimeAxis →₀ RawDigits
  canonical : ∀ p, CanonicalRaw (digits p)

/-- The exponent encoded on one prime axis. -/
def axisExponent (z : PrimeAxisTable) (p : PrimeAxis) : ℕ :=
  rawValue (z.digits p)

/-- Decode the finite prime-axis table as a natural number. -/
def decodePrimeAxisTable (z : PrimeAxisTable) : ℕ :=
  z.digits.prod fun p row ↦ (p : ℕ) ^ rawValue row

/--
The table has canonical digits on every axis and finite global support; its axis
exponents are W-weighted sums, and decoding is the corresponding finite prime product.
-/
theorem prime_axis_table_spec (z : PrimeAxisTable) :
    (∀ p, CanonicalRaw (z.digits p)) ∧
      (z.digits.support : Set PrimeAxis).Finite ∧
      (∀ p, axisExponent z p =
        ∑ k ∈ (z.digits p).support, z.digits p k * wValue k) ∧
      decodePrimeAxisTable z =
        ∏ p ∈ z.digits.support, (p : ℕ) ^ axisExponent z p := by
  refine ⟨z.canonical, z.digits.support.finite_toSet, ?_, ?_⟩
  · intro p
    rfl
  · rfl

end D5.S1.Digit
