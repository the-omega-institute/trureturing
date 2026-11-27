/- GID: D5/S1/Recurrence/Residue/OEISA189733FiniteSums
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/OEISA189733FiniteSums
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Basic]
   utility: none
   digest: Every upper entry of Curtz's rational array is an alternating binomial sum. -/

import D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

/-! Finite binomial sums for the entries of Curtz's array. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Residue.OEISA189733FiniteSums

open D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture Finset

/-- The alternating binomial moment sum. -/
private def F (m e : ℕ) : ℚ := ∑ j ∈ range (e + 1), (-1) ^ j * (e - j).choose j / (m + j + 1)

private theorem F_rec (m e : ℕ) : F m (e + 2) = F m (e + 1) - F (m + 1) e := by
  let f : ℕ → ℚ := fun j => (-1) ^ j * ((e + 2 - j).choose j : ℕ) / ((m : ℚ) + (j : ℕ) + 1)
  let g : ℕ → ℚ := fun j => (-1) ^ j * ((e + 1 - j).choose j : ℕ) / ((m : ℚ) + (j : ℕ) + 1)
  let k : ℕ → ℚ := fun j => (-1) ^ j * ((e - j).choose j : ℕ) / (((m + 1 : ℕ) : ℚ) + (j : ℕ) + 1)
  have hL : F m (e + 2) = (∑ i ∈ range (e + 1), f (i + 1)) + f (e + 2) + f 0 := by
    show ∑ j ∈ range (e + 2 + 1), f j = _
    rw [sum_range_succ', sum_range_succ]
  have hR : F m (e + 1) = (∑ i ∈ range (e + 1), g (i + 1)) + g 0 := by
    show ∑ j ∈ range (e + 1 + 1), g j = _
    rw [sum_range_succ']
  have hK : F (m + 1) e = ∑ i ∈ range (e + 1), k i := rfl
  have hlast : f (e + 2) = 0 := by
    simp only [f, show e + 2 - (e + 2) = 0 by omega,
      Nat.choose_eq_zero_of_lt (show 0 < e + 2 by omega)]
    simp
  have h0 : f 0 = g 0 := by simp [f, g]
  have hmid : ∀ i ∈ range (e + 1), f (i + 1) = g (i + 1) - k i := by
    intro i hi
    have hi' : i ≤ e := Nat.lt_succ_iff.mp (mem_range.mp hi)
    simp only [f, g, k]
    rw [show e + 2 - (i + 1) = (e - i) + 1 by omega, show e + 1 - (i + 1) = e - i by omega,
      Nat.choose_succ_succ']
    push_cast
    ring
  rw [hL, hR, hK, hlast, h0, sum_congr rfl hmid, sum_sub_distrib]
  ring

private theorem triangle_eq (e : ℕ) : ∀ m, triangle m (e + 1) = (-1) ^ m * F m e := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro m
    rcases e with _ | _ | e
    · simp [triangle, F, div_eq_mul_inv]
    · simp [triangle, F, sum_range_succ, div_eq_mul_inv]
    · have h1 := ih (e + 1) (by omega) m
      have h2 := ih e (by omega) (m + 1)
      rw [show e + 1 + 1 + 1 = (e + 1) + 2 by ring, triangle, h1, h2, F_rec]
      rw [pow_succ]
      ring

private theorem F_trunc (m e : ℕ) :
    F m e = ∑ j ∈ range (e / 2 + 1), (-1) ^ j * (e - j).choose j / ((m : ℚ) + j + 1) := by
  unfold F
  symm
  apply sum_subset
  · intro j hj
    simp only [mem_range] at *
    omega
  · intro j hj hj'
    simp only [mem_range, not_lt] at hj hj'
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- Every upper entry `B(m, m + d) = triangle m d` with `d ≥ 1` of Curtz's array is the
alternating binomial sum `(-1)^m ∑_{j ≤ (d-1)/2} (-1)^j C(d-1-j, j) / (m + j + 1)`. -/
theorem result (m d : ℕ) (hd : 1 ≤ d) :
    triangle m d = (-1) ^ m *
      ∑ j ∈ range ((d - 1) / 2 + 1), (-1) ^ j * (d - 1 - j).choose j / ((m : ℚ) + j + 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [triangle_eq, F_trunc]
  simp

end D5.S1.Recurrence.Residue.OEISA189733FiniteSums
