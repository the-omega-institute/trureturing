/- GID: D5/S1/Recurrence/Parity/DyadicPowerRowClosedForm
   generality: I
   mirror-B: D5/B/S1/Recurrence/Parity/DyadicPowerRowClosedForm
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The rows at powers of two have a closed form contradicting a printed A329369 sum. -/

import D5.S1.Digit.DyadicRowPolynomialRecurrence
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace D5.S1.Recurrence.Parity.DyadicPowerRowClosedForm

open Polynomial
open D5.S1.Digit.DyadicRowPolynomialRecurrence

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- The row polynomial evaluated at one. -/
def b (n : Nat) : Int := (R n).eval 1

/-- The sum on the right of the printed row recurrence. -/
def kurkovSum (n m q : Nat) : Int :=
  ∑ i ∈ Finset.Icc (1 + padicValNat 2 (n + 1)) (wt n + 1),
    T n i * b (2 ^ m * (2 ^ (i - 1) - 1) + q)

/-- The sum identity as printed, with the index q left unbounded. -/
def KurkovRowRecurrence : Prop :=
  ∀ n m q : Nat, b (2 ^ m * n + q) = kurkovSum n m q

theorem b_zero : b 0 = 1 := by simp [b, R_zero]

theorem b_odd_index (r : Nat) : b (2 * r + 1) = b r := by
  simp [b, R_odd]

theorem b_even_index (r : Nat) (hr : 0 < r) :
    b (2 * r) = b r + b (r - 2 ^ padicValNat 2 r) + b (2 * r - 2 ^ padicValNat 2 r) := by
  simp [b, conjecture1 r hr]

private theorem R_one : R 1 = X ^ 2 := by
  simpa [R_zero, pow_two] using R_odd 0

/-- Closed form for the rows indexed by a positive power of two.
The induction turns one row into the next through the difference operator, so the two
coefficients evolve by `a` becoming `a + c` and `c` becoming `2 * c`. -/
theorem R_two_pow (k : Nat) (hk : 0 < k) :
    R (2 ^ k) = C ((2 : Int) ^ k - 1) * X + C ((2 : Int) ^ k) * X ^ 2 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have h : R (2 * 1) = X * ((R 1).comp (X + 1) - R 1) := R_even 1 (by decide)
      rw [show (2 : Nat) ^ 1 = 2 * 1 by decide, h, R_one]
      simp only [pow_comp, X_comp]
      rw [show ((2 : Int) ^ 1 - 1) = 1 by decide, show ((2 : Int) ^ 1) = 2 by decide]
      simp only [map_one, one_mul]
      rw [show C (2 : Int) = 2 by simp]
      ring
    · have h := ih hkpos
      have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
      rw [show (2 : Nat) ^ (k + 1) = 2 * 2 ^ k by ring, R_even (2 ^ k) hpos, h]
      simp only [add_comp, mul_comp, C_comp, X_comp, pow_comp]
      rw [show ((2 : Int) ^ (k + 1) - 1) = ((2 : Int) ^ k - 1) + (2 : Int) ^ k by ring,
        show ((2 : Int) ^ (k + 1)) = 2 * (2 : Int) ^ k by ring]
      rw [C_add, C_mul, show C (2 : Int) = 2 by simp]
      ring

private theorem wt_double (n : Nat) (hn : 0 < n) : wt (2 * n) = wt n := by
  unfold wt
  rw [Nat.digits_def' (by decide : (1 : Nat) < 2) (by omega)]
  simp

private theorem wt_two_pow (k : Nat) : wt (2 ^ k) = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show (2 : Nat) ^ (k + 1) = 2 * 2 ^ k by ring,
      wt_double _ (Nat.two_pow_pos k)]
    exact ih

private theorem padicValNat_two_pow_add_one (k : Nat) (hk : 0 < k) :
    padicValNat 2 (2 ^ k + 1) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show (2 : Nat) ^ (j + 1) = 2 * 2 ^ j by ring]
  omega

/-- The value at a power of two. -/
theorem b_two_pow (k : Nat) : b (2 ^ k) = 2 ^ (k + 1) - 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [b, R_one]
  · rw [b, R_two_pow k hk]
    simp
    ring

/-- The value just after a positive power of two. -/
theorem b_two_pow_add_one (k : Nat) (hk : 0 < k) : b (2 ^ k + 1) = 2 ^ k - 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show (2 : Nat) ^ (j + 1) + 1 = 2 * 2 ^ j + 1 by ring, b_odd_index, b_two_pow j]

private theorem b_one : b 1 = 1 := by simpa using b_two_pow 0

private theorem b_two : b 2 = 3 := by
  have h := b_two_pow 1
  norm_num at h
  simpa using h

private theorem T_two_pow_one (k : Nat) (hk : 0 < k) : T (2 ^ k) 1 = 2 ^ k - 1 := by
  rw [T, R_two_pow k hk]
  simp only [coeff_add, coeff_C_mul, coeff_X, coeff_X_pow]
  norm_num

private theorem T_two_pow_two (k : Nat) (hk : 0 < k) : T (2 ^ k) 2 = 2 ^ k := by
  rw [T, R_two_pow k hk]
  simp only [coeff_add, coeff_C_mul, coeff_X, coeff_X_pow]
  norm_num

/-- At every positive power of two the printed identity fails when m is zero and q is one.
Both sides are computed in closed form: the left side is `2 ^ k - 1` and the right side is
`2 ^ (k + 2) - 1`. Each triple produced here has `q` at least `2 ^ m`, so this family says
nothing about the identity under the digit restriction `q < 2 ^ m`. -/
theorem printed_recurrence_ne_at_two_pow (k : Nat) (hk : 0 < k) :
    b (2 ^ 0 * 2 ^ k + 1) ≠ kurkovSum (2 ^ k) 0 1 := by
  have hsum : kurkovSum (2 ^ k) 0 1 = T (2 ^ k) 1 * b 1 + T (2 ^ k) 2 * b 2 := by
    rw [kurkovSum, wt_two_pow k, padicValNat_two_pow_add_one k hk]
    rw [show Finset.Icc (1 + 0) (1 + 1) = ({1, 2} : Finset Nat) by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num
  rw [hsum, T_two_pow_one k hk, T_two_pow_two k hk, b_one, b_two]
  rw [show (2 : Nat) ^ 0 * 2 ^ k + 1 = 2 ^ k + 1 by ring, b_two_pow_add_one k hk]
  have hp : (0 : Int) < 2 ^ k := by positivity
  intro h
  linarith

/-- The identity, read with the printed unbounded range for q, is false. -/
theorem not_kurkovRowRecurrence : ¬ KurkovRowRecurrence := fun h =>
  printed_recurrence_ne_at_two_pow 1 (by decide) (h (2 ^ 1) 0 1)

#print axioms not_kurkovRowRecurrence
#print axioms R_two_pow

end
end D5.S1.Recurrence.Parity.DyadicPowerRowClosedForm
