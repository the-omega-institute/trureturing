/- GID: D5/S1/Recurrence/MatharA119967Refutation
   generality: I
   mirror-B: D5/B/S1/Recurrence/MatharA119967Refutation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Basic]
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Recurrence/MatharA119967Refutation.claim; result=D5/S1/Recurrence/MatharA119967Refutation.result; claim=D5/S1/Recurrence/MatharA119967Refutation.claim
   digest: The printed A119967 recurrence has strictly positive residual at every valid index. -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.MatharA119967Refutation
open scoped BigOperators

/-- Paul Barry's offset-zero finite sum in OEIS A119967. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1), n.choose (2 * k) * k.choose (k / 2)

/-- The signed left side printed by Mathar; coefficient subtraction is in ℤ. -/
def residual (n : ℕ) : ℤ :=
  ((n : ℤ) + 2) * ((n : ℤ) - 3) * a n +
    (2 + 2 * (n : ℤ) - (n : ℤ) ^ 2) * a (n - 1) +
    (3 * (n : ℤ) - 5) * ((n : ℤ) - 2) * a (n - 2) -
    ((n : ℤ) - 2) * ((n : ℤ) - 3) * a (n - 3) -
    ((n : ℤ) - 2) * ((n : ℤ) - 3) * a (n - 4)

/-- Both onset readings of the unchanged printed expression. The source does
not specify an onset: four is the least index with all lags nonnegative. -/
def claim : Prop :=
  (∀ n : ℕ, 4 ≤ n → residual n = 0) ∨
    (∃ N : ℕ, 4 ≤ N ∧ ∀ n : ℕ, N ≤ n → residual n = 0)

private theorem a_mono : Monotone a := by
  intro n m h
  unfold a
  calc
    _ ≤ ∑ k ∈ Finset.range (n / 2 + 1), m.choose (2 * k) * k.choose (k / 2) :=
      Finset.sum_le_sum fun k _ => Nat.mul_le_mul_right _ (Nat.choose_le_choose _ h)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (by intros; exact Nat.zero_le _)

private theorem a_pos (n : ℕ) : 0 < a n := by
  have h := Finset.single_le_sum (f := fun k => n.choose (2 * k) * k.choose (k / 2))
    (fun k _ => Nat.zero_le _) (show 0 ∈ Finset.range (n / 2 + 1) by simp)
  have hle : 1 ≤ a n := by simpa [a] using h
  omega

/-- Strict positivity holds at every valid lag index, so moving the onset
cannot make the printed recurrence valid. -/
theorem residual_pos : ∀ n : ℕ, 4 ≤ n → 0 < residual n := by
  intro n hn
  have hn' : (4 : ℤ) ≤ n := by exact_mod_cast hn
  have h₁ : (a (n - 1) : ℤ) ≤ a n := by
    exact_mod_cast a_mono (Nat.sub_le n 1)
  have h₃ : (a (n - 3) : ℤ) ≤ a (n - 2) := by
    exact_mod_cast a_mono (show n - 3 ≤ n - 2 by omega)
  have h₄ : (a (n - 4) : ℤ) ≤ a (n - 2) := by
    exact_mod_cast a_mono (show n - 4 ≤ n - 2 by omega)
  have hp₁ : (0 : ℤ) < a (n - 1) := by exact_mod_cast a_pos (n - 1)
  have hp₂ : (0 : ℤ) < a (n - 2) := by exact_mod_cast a_pos (n - 2)
  have hA : 0 ≤ ((n : ℤ) + 2) * ((n : ℤ) - 3) :=
    mul_nonneg (by omega) (by omega)
  have hD : 0 ≤ ((n : ℤ) - 2) * ((n : ℤ) - 3) :=
    mul_nonneg (by omega) (by omega)
  have hfirst := mul_nonneg hA (sub_nonneg.mpr h₁)
  have hthird := mul_nonneg hD (sub_nonneg.mpr h₃)
  have hfourth := mul_nonneg hD (sub_nonneg.mpr h₄)
  have hrest := mul_nonneg (show (0 : ℤ) ≤ (n : ℤ) - 4 by omega) hp₁.le
  have hstrict : 0 < ((n : ℤ) - 2) * ((n : ℤ) + 1) * (a (n - 2) : ℤ) :=
    mul_pos (mul_pos (by omega) (by omega)) hp₂
  dsimp only [residual]
  nlinarith

/-- Neither the literal all-valid-index reading nor any eventual onset holds. -/
theorem result : ¬ claim := by
  rintro (h | ⟨N, hN, h⟩)
  · have hfour := h 4 (by decide)
    norm_num [residual, a, Finset.sum_range_succ, Nat.choose] at hfour
  · exact (ne_of_gt (residual_pos N hN)) (h N le_rfl)

end D5.S1.Recurrence.MatharA119967Refutation
