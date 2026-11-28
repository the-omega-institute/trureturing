import OmegaBuild.Commands
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-! Omega original.
Cubic sums of the diagonal weights on the second exterior power. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OmegaMath.ExteriorSquareTrace

open scoped BigOperators

/-- The pair sum keeps each unordered pair in its increasing orientation. -/
def pairCubes {N : ℕ} (h : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then (h i + h j) ^ 3 else 0

/-- A cubic trace formula with the correction for a nonzero fundamental trace. -/
theorem pairCubes_eq (N : ℕ) (h : Fin N → ℝ) :
    pairCubes h = ((N : ℝ) - 4) * (∑ i, h i ^ 3) +
      3 * (∑ i, h i) * (∑ i, h i ^ 2) := by
  induction N with
  | zero => simp [pairCubes]
  | succ N ih =>
    let g : Fin N → ℝ := fun i => h i.succ
    have hdecomp : pairCubes h = (∑ j, (h 0 + g j)^3) + pairCubes g := by
      unfold pairCubes
      rw [Fin.sum_univ_succ]
      simp only [Fin.sum_univ_succ (f := fun j => if (0 : Fin (N+1)) < j then
          (h 0 + h j) ^ 3 else 0), lt_self_iff_false, ite_false, Fin.succ_pos, ite_true, zero_add]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Fin.sum_univ_succ]
      simp [g]
    have hexpand :
        (∑ j, (h 0 + g j)^3) =
          (N : ℝ) * h 0 ^ 3 + 3 * h 0 ^ 2 * (∑ j, g j) +
            3 * h 0 * (∑ j, g j ^ 2) + (∑ j, g j ^ 3) := by
      calc
        _ = ∑ j : Fin N, (h 0 ^ 3 + 3 * h 0 ^ 2 * g j + 3 * h 0 * g j ^ 2 + g j ^ 3) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by
          simp [Finset.sum_add_distrib, ← Finset.mul_sum, nsmul_eq_mul]
    rw [hdecomp, hexpand, ih g, Nat.cast_succ]
    rw [Fin.sum_univ_succ (f := fun i => h i ^ 3), Fin.sum_univ_succ (f := h),
      Fin.sum_univ_succ (f := fun i => h i ^ 2)]
    change _ = ((N : ℝ) + 1 - 4) * (h 0 ^ 3 + ∑ i, g i ^ 3) +
      3 * (h 0 + ∑ i, g i) * (h 0 ^ 2 + ∑ i, g i ^ 2)
    ring

end OmegaMath.ExteriorSquareTrace
