/- GID: D5/S1/Digit/Admissibility/GrayCodeBinaryRecurrenceClosedForm
   generality: G
   mirror-B: D5/B/S1/Digit/Admissibility/GrayCodeBinaryRecurrenceClosedForm
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.Int.Parity, mathlib/module/Mathlib.Data.Nat.Bitwise, mathlib/module/Mathlib.Data.Nat.EvenOddRec]
   utility: none
   digest: Yanev's Gray-code closed form for the nonnegative half of OEIS A163617. -/
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.EvenOddRec

/-!
# Gray-code closed form for OEIS A163617

OEIS A163617 defines `a(2*n) = 2*a(n)` and
`a(2*n+1) = 2*a(n) + 2 + (-1)^n` for integer indices. This module proves
the nonnegative-index part, initialized by `a 0 = 0`; the negative-index
sequence A163618 is not claimed.

The correction below is `3*n/2` for even `n` and `(3*n+1)/2` for odd `n`.
Over the integers these two branches equal `(6*n + 1 - (-1)^n)/4`, the
form in Velin Yanev's conjecture of Dec 17 2016. The Gray-code component is
OEIS A003188, `n XOR floor(n/2)`.
-/

namespace D5.S1.Digit.Admissibility.GrayCodeBinaryRecurrenceClosedForm

/-- The nonnegative half of Somos's binary recurrence in OEIS A163617. -/
def a (n : ℕ) : ℕ :=
  n.evenOddRec 0
    (fun _ x => 2 * x)
    (fun m x => 2 * x + if m % 2 = 0 then 3 else 1)

/-- Binary reflected Gray code, OEIS A003188. -/
def gray (n : ℕ) : ℕ := n ^^^ (n / 2)

/-- The integral parity split of Yanev's correction term. -/
def corr (n : ℕ) : ℕ :=
  if n % 2 = 0 then 3 * n / 2 else (3 * n + 1) / 2

/-- Yanev's correction term: `corr n` is the integer `(6 n + 1 − (−1)^n) / 4`. -/
example (n : ℕ) : (corr n : ℤ) = (6 * n + 1 - (-1) ^ n) / 4 := by
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨m, rfl⟩ := hn
    rw [Even.neg_one_pow (α := ℤ) ⟨m, rfl⟩]
    push_cast
    simp [corr]
    omega
  · obtain ⟨m, rfl⟩ := hn
    rw [Odd.neg_one_pow (α := ℤ) ⟨m, rfl⟩]
    push_cast
    simp [corr]
    omega

/-- Velin Yanev's 2016 conjectured closed form for every nonnegative index. -/
theorem yanev_a163617 : ∀ n, a n = gray n + corr n := by
  intro n
  induction n using Nat.evenOddRec with
  | h0 => rfl
  | h_even m ih =>
      have hgray : gray (2 * m) = 2 * gray m + m % 2 := by
        calc
          gray (2 * m) = (2 * m) ^^^ m := by simp [gray]
          _ = Nat.bit false m ^^^ Nat.bit (Nat.bodd m) (Nat.div2 m) := by
            rw [Nat.bit_bodd_div2]
            rfl
          _ = Nat.bit (bne false (Nat.bodd m))
                (m ^^^ Nat.div2 m) := Nat.xor_bit _ _ _ _
          _ = 2 * gray m + m % 2 := by
            simp [gray, Nat.bit_val, Nat.div2_val, Nat.mod_two_of_bodd]
      rw [a, Nat.evenOddRec_even (H := by rfl)]
      change 2 * a m = gray (2 * m) + corr (2 * m)
      rw [ih, hgray]
      unfold corr
      by_cases h : m % 2 = 0 <;> simp [h] <;> omega
  | h_odd m ih =>
      have hgray :
          gray (2 * m + 1) = 2 * gray m + if m % 2 = 0 then 1 else 0 := by
        calc
          gray (2 * m + 1) = (2 * m + 1) ^^^ m := by
            unfold gray
            congr 1
            omega
          _ = Nat.bit true m ^^^ Nat.bit (Nat.bodd m) (Nat.div2 m) := by
            rw [Nat.bit_bodd_div2]
            rfl
          _ = Nat.bit (bne true (Nat.bodd m))
                (m ^^^ Nat.div2 m) := Nat.xor_bit _ _ _ _
          _ = 2 * gray m + if m % 2 = 0 then 1 else 0 := by
            cases h : Nat.bodd m <;>
              simp [gray, Nat.bit_val, Nat.div2_val, Nat.mod_two_of_bodd, h]
      rw [a, Nat.evenOddRec_odd (H := by rfl)]
      change 2 * a m + (if m % 2 = 0 then 3 else 1) =
        gray (2 * m + 1) + corr (2 * m + 1)
      rw [ih, hgray]
      unfold corr
      by_cases h : m % 2 = 0 <;> simp [h] <;> omega

#print axioms yanev_a163617

end D5.S1.Digit.Admissibility.GrayCodeBinaryRecurrenceClosedForm
