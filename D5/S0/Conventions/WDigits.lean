/- GID: D5/S0/Conventions/WDigits
   generality: I
   mirror-B: D5/B/S0/Conventions/WDigits
   mirror-E: none(waiver:mathlib-zeckendorf-theorem)
   anchors: []
   digest: W digits use Fibonacci weights and the unique nonadjacent Zeckendorf representation. -/

import Mathlib.Data.Nat.Fib.Zeckendorf
import OmegaBuild.Commands
import OmegaMath.Arithmetic.WDigits

compile_only_with_mathlib

namespace D5.S0.Conventions

/-- The zero-based W weight sequence `1, 2, 3, 5, ...`. -/
def wValue (index : ℕ) : ℕ := Nat.fib (index + 2)

@[simp] theorem wValue_zero_nat : wValue 0 = 1 := rfl
@[simp] theorem wValue_one_nat : wValue 1 = 2 := rfl
@[simp] theorem wValue_two_nat : wValue 2 = 3 := rfl

theorem wValue_add_two_nat (index : ℕ) :
    wValue (index + 2) = wValue index + wValue (index + 1) := by
  let step (pair : Nat × Nat) := (pair.2, pair.1 + pair.2)
  have commute (n : Nat) (pair : Nat × Nat) :
      (step^[n]) (step pair) = step ((step^[n]) pair) := by
    induction n generalizing pair with
    | zero => rfl
    | succ n ih => exact ih (step pair)
  have advance (n : Nat) : (step^[n + 1]) (0, 1) = step ((step^[n]) (0, 1)) :=
    commute n (0, 1)
  change ((step^[index + 2 + 1 + 1]) (0, 1)).1 =
    ((step^[index + 2]) (0, 1)).1 + ((step^[index + 2 + 1]) (0, 1)).1
  rw [advance (index + 2 + 1), advance (index + 2)]

section OmegaWeights

open Omega.Arithmetic.WDigits renaming wValue → omegaWeight

-- On the Mathlib backend both weight functions reduce to the same Fibonacci iterator.
theorem wValue_zero : Omega.Eq (omegaWeight .zero) Omega.Nat.one :=
  wValue_zero_nat

theorem wValue_one : Omega.Eq (omegaWeight Omega.Nat.one) Omega.Nat.one.succ :=
  wValue_one_nat

theorem wValue_two : Omega.Eq (omegaWeight Omega.Nat.one.succ) Omega.Nat.one.succ.succ :=
  wValue_two_nat

theorem wValue_add_two (index : Omega.Nat) :
    Omega.Eq (omegaWeight index.succ.succ) ((omegaWeight index).add (omegaWeight index.succ)) :=
  wValue_add_two_nat index

end OmegaWeights

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
