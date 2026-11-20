/- GID: D5/S1/Recurrence/Algebraic/OEISA289916StrictIncrease
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/OEISA289916StrictIncrease
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.NoZeroDivisors]
   utility: none
   digest: The coefficients of Barker's generating function for A289916 are strictly increasing. -/

import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Strict increase of the coefficients of Barker's generating function for OEIS A289916. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Algebraic.OEISA289916StrictIncrease

open PowerSeries

/-- Denominator of Barker's generating function. -/
noncomputable def den : PowerSeries ℤ :=
  (1 - X + X ^ 2) * (X ^ 4 - X ^ 3 - X ^ 2 - X + 1)

/-- Numerator of Barker's generating function. -/
noncomputable def num : PowerSeries ℤ :=
  (1 + X) ^ 2 * (1 - X + X ^ 2 - X ^ 3 + X ^ 4 - X ^ 5 + X ^ 6)

/-- Coefficients of `1 / ((1 + z^3) Q(z))`, shifted by nine so that negative indices read zero. -/
private def H : ℕ → ℤ
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0
  | 9 => 1
  | n + 10 => H (n + 9) + H (n + 8) + H (n + 5) + H (n + 4) - H (n + 3)

private theorem H_rec (n : ℕ) :
    H (n + 10) = H (n + 9) + H (n + 8) + H (n + 5) + H (n + 4) - H (n + 3) :=
  rfl

/-- The sequence with Barker's generating function. -/
private def V (n : ℕ) : ℤ := H (n + 9) + 2 * H (n + 8) + H (n + 7) + H (n + 2) + 2 * H (n + 1) + H n

private theorem H_mono : ∀ n, 0 ≤ H n ∧ H n ≤ H (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 10 with h | h
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
      have a := ih (m + 9) (by omega)
      have b := ih (m + 6) (by omega)
      have c := ih (m + 4) (by omega)
      have r := H_rec (m + 1)
      rw [show m + 1 + 10 = m + 10 + 1 by ring, show m + 1 + 9 = m + 10 by ring,
        show m + 1 + 8 = m + 9 by ring, show m + 1 + 5 = m + 6 by ring,
        show m + 1 + 4 = m + 5 by ring, show m + 1 + 3 = m + 4 by ring] at r
      exact ⟨by linarith [a.1, a.2], by linarith [a.1, b.1, c.2]⟩

private theorem H_pos (n : ℕ) (h : 9 ≤ n) : 1 ≤ H n := by
  induction n, h using Nat.le_induction with
  | base => decide
  | succ k _ ih => linarith [(H_mono k).2]

private theorem H_strict (n : ℕ) : H (n + 10) < H (n + 11) := by
  have r := H_rec (n + 1)
  simp only [show n + 1 + 10 = n + 11 by ring, show n + 1 + 9 = n + 10 by ring,
    show n + 1 + 8 = n + 9 by ring, show n + 1 + 5 = n + 6 by ring,
    show n + 1 + 4 = n + 5 by ring, show n + 1 + 3 = n + 4 by ring] at r
  have := H_pos (n + 9) (by omega)
  linarith [(H_mono (n + 6)).1, (H_mono (n + 4)).2]

private theorem V_strict (n : ℕ) : V n < V (n + 1) := by
  unfold V
  have m := fun k => (H_mono k).2
  rcases n with _ | n
  · decide
  · have s := H_strict n
    simp only [show n + 1 + 1 + 9 = n + 11 by ring, show n + 1 + 9 = n + 10 by ring,
      show n + 1 + 8 = n + 9 by ring, show n + 1 + 7 = n + 8 by ring,
      show n + 1 + 1 + 2 = n + 4 by ring, show n + 1 + 2 = n + 3 by ring]
    linarith [m (n + 8), m (n + 9), m (n + 3), m (n + 2), m (n + 1)]

private theorem V_rec (n : ℕ) :
    V (n + 10) = V (n + 9) + V (n + 8) + V (n + 5) + V (n + 4) - V (n + 3) := by
  unfold V
  have h := fun k => H_rec k
  have := h (n + 9); have := h (n + 8); have := h (n + 7); have := h (n + 2); have := h (n + 1)
  have := h n
  simp only [add_assoc] at *
  norm_num at *
  linarith

private theorem V_small : V 0 = 1 ∧ V 1 = 3 ∧ V 2 = 5 ∧ V 3 = 8 ∧ V 4 = 13 ∧ V 5 = 22 ∧ V 6 = 39 ∧
    V 7 = 69 ∧ V 8 = 120 ∧ V 9 = 206 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem V_gf' : mk V * (1 - X - X ^ 2 - X ^ 5 - X ^ 6 + X ^ 7) =
    (1 + 2 * X + X ^ 2 + X ^ 7 + 2 * X ^ 8 + X ^ 9 : PowerSeries ℤ) := by
  simp only [mul_add, mul_sub, mul_one]
  ext n
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := V_small
  rcases Nat.lt_or_ge n 10 with hn | hn
  · interval_cases n <;> simp [coeff_X_pow, coeff_mul_X_pow', coeff_X, coeff_one,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    have h := V_rec m
    simp [coeff_X_pow, coeff_mul_X_pow', coeff_X, coeff_one,
      show m + 10 - 2 = m + 8 by omega,
      show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega,
      show m + 10 - 7 = m + 3 by omega]
    linarith

private theorem V_gf : mk V * den = num := by
  have h1 : (1 + X : PowerSeries ℤ) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp at this
  apply mul_left_cancel₀ h1
  have := V_gf'
  unfold den num
  linear_combination this

private theorem den_ne : den ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  simp [den] at this

/-- Barker's generating function determines a unique integer sequence, and that sequence is
strictly increasing. -/
theorem result :
    (∃! v : ℕ → ℤ, mk v * den = num) ∧
      ∀ v : ℕ → ℤ, mk v * den = num → ∀ n, v n < v (n + 1) := by
  have uniq : ∀ v : ℕ → ℤ, mk v * den = num → v = V := by
    intro v hv
    have : mk v = mk V := mul_right_cancel₀ den_ne (hv.trans V_gf.symm)
    funext n
    have := congrArg (coeff n) this
    simpa using this
  refine ⟨⟨V, V_gf, fun v hv => uniq v hv⟩, fun v hv n => ?_⟩
  rw [uniq v hv]
  exact V_strict n

end D5.S1.Recurrence.Algebraic.OEISA289916StrictIncrease
