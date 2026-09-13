/- GID: D5/S1/Recurrence/Invariants/StephanHarmonicMeanNumeratorClosedForm
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/StephanHarmonicMeanNumeratorClosedForm
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Tactic.FieldSimp, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Closed form for Stephan's harmonic-mean-numerator recurrence, OEIS A107928. -/

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The harmonic-mean-numerator recurrence

The value at index zero is a sentinel used only to totalize the recurrence;
OEIS A107928 starts at index one. Since the recurrence stays positive,
`Int.toNat` preserves every reduced numerator used below.
-/

namespace D5.S1.Recurrence.Invariants.StephanHarmonicMeanNumeratorClosedForm

/-- OEIS A107928, totalized at index zero by the sentinel value zero. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | n + 3 =>
      ((2 * (a (n + 2) : ℚ) * (a (n + 1) : ℚ)) /
          ((a (n + 1) : ℚ) + (a (n + 2) : ℚ))).num.toNat
termination_by n => n
decreasing_by all_goals omega

example : a 1 = 2 := by norm_num [a]
example : a 2 = 3 := by norm_num [a]
example : a 3 = 12 := by
  simp [a]
  rw [show (2 * 3 * 2 / (2 + 3) : ℚ) = 12 / 5 by norm_num]
  change ((((12 : ℤ) : ℚ) / ((5 : ℤ) : ℚ)).num.toNat) = 12
  rw [Rat.num_div_eq_of_coprime (by norm_num) (by decide)]
  rfl

/-- Stephan's three-residue closed form for OEIS A107928. -/
theorem stephan_a107928 : ∀ m : ℕ, 1 ≤ m →
    a (3 * m) = 12 * 8 ^ (m - 1) ∧
      a (3 * m + 1) = 3 * 8 ^ m ∧
      a (3 * m + 2) = 2 * 8 ^ m := by
  have reduced_numerators : ∀ m : ℕ,
      (((((12 * 8 ^ m : ℕ) : ℤ) : ℚ) / ((5 : ℤ) : ℚ)).num.toNat = 12 * 8 ^ m) ∧ (((((24 * 8 ^ m : ℕ) : ℤ) : ℚ) / ((7 : ℤ) : ℚ)).num.toNat = 24 * 8 ^ m) := by
    intro m
    have hpow5 : Nat.Coprime (8 ^ m) 5 :=
      Nat.Coprime.pow_left m (by decide)
    have hpow7 : Nat.Coprime (8 ^ m) 7 :=
      Nat.Coprime.pow_left m (by decide)
    have h5 : Nat.Coprime (12 * 8 ^ m) 5 :=
      Nat.Coprime.mul_left (by decide) hpow5
    have h7 : Nat.Coprime (24 * 8 ^ m) 7 :=
      Nat.Coprime.mul_left (by decide) hpow7
    constructor
    · rw [Rat.num_div_eq_of_coprime (by norm_num)
        (by simpa [Int.natAbs_mul, Int.natAbs_pow] using h5)]
      exact Int.toNat_natCast _
    · rw [Rat.num_div_eq_of_coprime (by norm_num)
        (by simpa [Int.natAbs_mul, Int.natAbs_pow] using h7)]
      exact Int.toNat_natCast _
  have next_block : ∀ m : ℕ, a (3 * m + 1) = 3 * 8 ^ m →
      a (3 * m + 2) = 2 * 8 ^ m →
      a (3 * m + 3) = 12 * 8 ^ m ∧ a (3 * m + 4) = 3 * 8 ^ (m + 1) ∧ a (3 * m + 5) = 2 * 8 ^ (m + 1) := by
    intro m h1 h2
    have h3 : a (3 * m + 3) = 12 * 8 ^ m := by
      rw [a, h1, h2]
      rw [show
        (2 * ((2 * 8 ^ m : ℕ) : ℚ) * ((3 * 8 ^ m : ℕ) : ℚ)) /
            (((3 * 8 ^ m : ℕ) : ℚ) + ((2 * 8 ^ m : ℕ) : ℚ)) =
          ((((12 * 8 ^ m : ℕ) : ℤ) : ℚ) / ((5 : ℤ) : ℚ)) by
        push_cast
        field_simp
        ring]
      exact (reduced_numerators m).1
    have h4 : a (3 * m + 4) = 3 * 8 ^ (m + 1) := by
      rw [show 3 * m + 4 = (3 * m + 1) + 3 by omega, a]
      rw [show 3 * m + 1 + 2 = 3 * m + 3 by omega,
        show 3 * m + 1 + 1 = 3 * m + 2 by omega, h3, h2]
      rw [show
        (2 * ((12 * 8 ^ m : ℕ) : ℚ) * ((2 * 8 ^ m : ℕ) : ℚ)) /
            (((2 * 8 ^ m : ℕ) : ℚ) + ((12 * 8 ^ m : ℕ) : ℚ)) =
          ((((24 * 8 ^ m : ℕ) : ℤ) : ℚ) / ((7 : ℤ) : ℚ)) by
        push_cast
        field_simp
        ring]
      rw [(reduced_numerators m).2, pow_succ]
      ring
    have h5 : a (3 * m + 5) = 2 * 8 ^ (m + 1) := by
      rw [show 3 * m + 5 = (3 * m + 2) + 3 by omega, a]
      rw [show 3 * m + 2 + 2 = 3 * m + 4 by omega,
        show 3 * m + 2 + 1 = 3 * m + 3 by omega, h4, h3]
      rw [show
        (2 * ((3 * 8 ^ (m + 1) : ℕ) : ℚ) * ((12 * 8 ^ m : ℕ) : ℚ)) /
            (((12 * 8 ^ m : ℕ) : ℚ) + ((3 * 8 ^ (m + 1) : ℕ) : ℚ)) =
          ((16 * 8 ^ m : ℕ) : ℚ) by
        push_cast
        rw [pow_succ]
        field_simp
        ring]
      simp only [Rat.num_natCast, Int.toNat_natCast, pow_succ]
      ring
    exact ⟨h3, h4, h5⟩
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction k with
  | zero =>
      have h3 : a 3 = 12 := by
        simp [a]
        rw [show (2 * 3 * 2 / (2 + 3) : ℚ) = 12 / 5 by norm_num]
        change ((((12 : ℤ) : ℚ) / ((5 : ℤ) : ℚ)).num.toNat) = 12
        rw [Rat.num_div_eq_of_coprime (by norm_num) (by decide)]
        rfl
      have h4 : a 4 = 24 := by
        rw [show 4 = 1 + 3 by omega, a]
        rw [show 1 + 2 = 3 by omega, show 1 + 1 = 2 by omega, h3, a]
        rw [show
          (2 * ((12 : ℕ) : ℚ) * ((3 : ℕ) : ℚ)) /
              (((3 : ℕ) : ℚ) + ((12 : ℕ) : ℚ)) =
            (((24 : ℤ) : ℚ) / ((5 : ℤ) : ℚ)) by norm_num]
        rw [Rat.num_div_eq_of_coprime (by norm_num) (by decide)]
        rfl
      have h5 : a 5 = 16 := by
        rw [show 5 = 2 + 3 by omega, a]
        rw [show 2 + 2 = 4 by omega, show 2 + 1 = 3 by omega, h4, h3]
        rw [show
          (2 * ((24 : ℕ) : ℚ) * ((12 : ℕ) : ℚ)) /
              (((12 : ℕ) : ℚ) + ((24 : ℕ) : ℚ)) =
            ((16 : ℕ) : ℚ) by norm_num]
        simp
      simpa using And.intro h3 (And.intro h4 h5)
  | succ k ih =>
      rcases next_block (1 + k) ih.2.1 ih.2.2 with ⟨h0, h1, h2⟩
      constructor
      · rw [show 3 * (1 + Nat.succ k) = 3 * (1 + k) + 3 by omega,
          show 1 + Nat.succ k - 1 = 1 + k by omega]
        exact h0
      · constructor
        · rw [show 3 * (1 + Nat.succ k) + 1 = 3 * (1 + k) + 4 by omega,
            show 1 + Nat.succ k = 1 + k + 1 by omega]
          exact h1
        · rw [show 3 * (1 + Nat.succ k) + 2 = 3 * (1 + k) + 5 by omega,
            show 1 + Nat.succ k = 1 + k + 1 by omega]
          exact h2

#print axioms stephan_a107928

end D5.S1.Recurrence.Invariants.StephanHarmonicMeanNumeratorClosedForm
