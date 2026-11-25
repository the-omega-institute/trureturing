/- GID: D5/S1/Recurrence/Residue/OEISA189733Reflection
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/OEISA189733Reflection
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Algebra.Group.ForwardDiff]
   utility: none
   digest: Curtz's full array has signed reflection; its first column is a binomial transform. -/

import D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic.Ring

/-! Reflection and the inverse binomial transform for Curtz's full square array. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Residue.OEISA189733Reflection

open D5.S1.Recurrence.Residue.OEISA189733DenominatorConjecture Finset

/-- Curtz's full square array: the upper triangle `B m n = triangle m (n - m)` for `m ≤ n`,
and the lower branch `B m n = B (m - 1) (n + 1) - B (m - 1) n` for `m > n`. -/
def B : ℕ → ℕ → ℚ
  | 0, n => triangle 0 n
  | m + 1, n => if m + 1 ≤ n then triangle (m + 1) (n - (m + 1)) else B m (n + 1) - B m n

private theorem B_upper (m n : ℕ) (h : m ≤ n) : B m n = triangle m (n - m) := by
  cases m with
  | zero => simp [B]
  | succ m => simp [B, h]

private theorem B_lower (m n : ℕ) (h : n < m + 1) : B (m + 1) n = B m (n + 1) - B m n := by
  simp [B, show ¬ (m + 1 ≤ n) by omega]

private theorem B_diag (m : ℕ) : B m m = 0 := by
  rw [B_upper m m le_rfl, Nat.sub_self]; simp [triangle]

private theorem B_diff (m n : ℕ) : B (m + 1) n = B m (n + 1) - B m n := by
  rcases Nat.lt_or_ge n (m + 1) with h | h
  · exact B_lower m n h
  · obtain ⟨d, rfl⟩ : ∃ d, n = m + 1 + d := ⟨n - (m + 1), by omega⟩
    rw [B_upper _ _ (by omega), B_upper _ _ (by omega), B_upper _ _ (by omega),
      show m + 1 + d + 1 - m = d + 2 by omega, show m + 1 + d - m = d + 1 by omega,
      show m + 1 + d - (m + 1) = d by omega, triangle]
    ring

private theorem B_upper_rec (n m : ℕ) (h : n < m) : B n (m + 1) = B n m + B (n + 1) m := by
  rw [B_upper _ _ (by omega), B_upper _ _ (by omega), B_upper _ _ (by omega)]
  obtain ⟨d, rfl⟩ : ∃ d, m = n + 1 + d := ⟨m - (n + 1), by omega⟩
  rw [show n + 1 + d + 1 - n = d + 2 by omega, show n + 1 + d - n = d + 1 by omega,
    show n + 1 + d - (n + 1) = d by omega, triangle]

private theorem reflection_lower : ∀ m n, n ≤ m → B m n = (-1) ^ (m + n + 1) * B n m := by
  intro m
  induction m with
  | zero =>
    intro n hn
    obtain rfl : n = 0 := by omega
    simp [B_diag]
  | succ m ih =>
    intro n hn
    rcases Nat.eq_or_lt_of_le hn with h | h
    · subst h; simp [B_diag]
    · rw [B_lower m n h]
      rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp h) with h' | h'
      · subst h'
        rw [B_diag, B_upper n (n + 1) (by omega)]
        rw [show n + 1 + n + 1 = 2 * (n + 1) by ring, pow_mul]
        simp [triangle]
      · rw [ih (n + 1) (by omega), ih n (by omega), B_upper_rec n m h']
        rw [show m + (n + 1) + 1 = (m + n + 1) + 1 by ring,
          show m + 1 + n + 1 = (m + n + 1) + 1 by ring, pow_succ]
        ring

private theorem reflection (m n : ℕ) : B m n = (-1) ^ (m + n + 1) * B n m := by
  rcases le_total n m with h | h
  · exact reflection_lower m n h
  · rw [reflection_lower n m h, ← mul_assoc, ← pow_add,
      show m + n + 1 + (n + m + 1) = 2 * (m + n + 1) by ring, pow_mul]
    simp

private theorem B_iter (m : ℕ) : B m = (fwdDiff 1)^[m] (B 0) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ← ih]
    funext n
    simp [fwdDiff, B_diff]

private theorem B_binomial (m n : ℕ) :
    B m n = ∑ j ∈ range (m + 1), (-1) ^ (m - j) * (m.choose j : ℚ) * B 0 (n + j) := by
  rw [B_iter, fwdDiff_iter_eq_sum_shift]
  apply sum_congr rfl
  intro j _
  simp [zsmul_eq_mul]

/-- The full square array agrees with `triangle` on and above the diagonal, has zero diagonal,
the reflection `B m n = (-1)^(m+n+1) B n m` and the difference identity everywhere; its zeroth
column is the inverse binomial transform of the zeroth row `b_j = B 0 j = triangle 0 j`, namely
`B n 0 = ∑ (-1)^(n-j) C(n, j) b_j = (-1)^(n+1) b_n`. -/
theorem result :
    (∀ m d, B m (m + d) = triangle m d) ∧
    (∀ m, B m m = 0) ∧
    (∀ m n, B m n = (-1) ^ (m + n + 1) * B n m) ∧
    (∀ m n, B (m + 1) n = B m (n + 1) - B m n) ∧
    ∀ n, B n 0 = ∑ j ∈ range (n + 1), (-1) ^ (n - j) * (n.choose j : ℚ) * triangle 0 j ∧
      B n 0 = (-1) ^ (n + 1) * triangle 0 n := by
  refine ⟨fun m d => by rw [B_upper m (m + d) (by omega), Nat.add_sub_cancel_left],
    B_diag, reflection, B_diff, fun n => ⟨?_, ?_⟩⟩
  · rw [B_binomial]; apply sum_congr rfl; intro j _; simp [B]
  · rw [reflection]; simp [B]

end D5.S1.Recurrence.Residue.OEISA189733Reflection
