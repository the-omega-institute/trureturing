/- GID: D5/S0/Conventions/WDigits
   generality: I
   mirror-B: D5/B/S0/Conventions/WDigits
   mirror-E: none(waiver:mathlib-zeckendorf-theorem)
   anchors: [GICT-v3.6-I.2-definition-1.4]
   digest: W digits use Fibonacci weights and the unique nonadjacent Zeckendorf representation. -/

import Mathlib.Data.Nat.Fib.Zeckendorf

namespace D5.S0.Conventions

/-- The zero-based W weight sequence `1, 2, 3, 5, ...`. -/
def wValue (index : ℕ) : ℕ := Nat.fib (index + 2)

@[simp] theorem wValue_zero : wValue 0 = 1 := rfl
@[simp] theorem wValue_one : wValue 1 = 2 := rfl
@[simp] theorem wValue_two : wValue 2 = 3 := rfl

theorem wValue_add_two (index : ℕ) :
    wValue (index + 2) = wValue index + wValue (index + 1) := by
  simpa [wValue, Nat.add_assoc] using (Nat.fib_add_two (n := index + 2))

/-- Canonical W digits, stored as the occupied Fibonacci indices used by mathlib. -/
def wdigits (n : ℕ) : List ℕ := Nat.zeckendorf n

/-- W1/W2: occupied indices are at least two and no two are adjacent. -/
theorem wdigits_isCanonical (n : ℕ) : (wdigits n).IsZeckendorfRep :=
  Nat.isZeckendorfRep_zeckendorf n

/-- W3: decoding canonical occupied indices recovers the natural number. -/
@[simp] theorem decode_wdigits (n : ℕ) : ((wdigits n).map Nat.fib).sum = n :=
  Nat.sum_zeckendorf_fib n

/-- Canonicality is unique among nonadjacent Fibonacci representations. -/
theorem wdigits_unique {n : ℕ} {digits : List ℕ}
    (canonical : digits.IsZeckendorfRep)
    (value : (digits.map Nat.fib).sum = n) : digits = wdigits n := by
  have identified := Nat.zeckendorf_sum_fib canonical
  rw [value] at identified
  exact identified.symm

/-- The machine type of canonical W strings. -/
abbrev WDigitString := {digits : List ℕ // digits.IsZeckendorfRep}

/-- Zeckendorf's theorem as the canonical W-coordinate equivalence. -/
def wEncoding : ℕ ≃ WDigitString := Nat.zeckendorfEquiv

end D5.S0.Conventions
