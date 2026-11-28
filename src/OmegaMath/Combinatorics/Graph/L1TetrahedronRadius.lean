import OmegaBuild.Commands
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

compile_only_with_mathlib

/-! Omega original.

The four vertices of the balanced sign tetrahedron have diameter one and
average distance at least three halves after doubling in real three-dimensional L1.
-/

namespace ChordalL1

open Finset

theorem exists_three_dimensional_radius_family :
    ∃ x : Fin 4 → PiLp 1 (fun _ : Fin 3 => ℝ),
      (∀ a, ‖x a‖ ≤ 1) ∧ (∀ a b, ‖x a - x b‖ ≤ 1) ∧
      ∀ y, (6 : ℝ) ≤ ∑ a, ‖(2 : ℝ) • x a - y‖ := by
  let table : Fin 4 → Fin 3 → ℝ := ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]
  let E := PiLp 1 (fun _ : Fin 3 => ℝ)
  let x (a : Fin 4) : E := (1 / 4 : ℝ) • WithLp.toLp 1 (table a)
  have get (a : Fin 4) (j : Fin 3) : x a j = table a j / 4 := by
    change (1 / 4 : ℝ) * table a j = table a j / 4
    ring
  have h₁ (a : Fin 4) : ‖x a‖ ≤ 1 := by
    rw [PiLp.norm_eq_of_L1, Fin.sum_univ_three]
    fin_cases a <;> norm_num [get, table, Real.norm_eq_abs]
  have sub_get (a b : Fin 4) (j : Fin 3) : (x a - x b) j = table a j / 4 - table b j / 4 := by
    change x a j - x b j = _
    rw [get, get]
  have h₂ (a b : Fin 4) : ‖x a - x b‖ ≤ 1 := by
    rw [PiLp.norm_eq_of_L1, Fin.sum_univ_three]
    fin_cases a <;> fin_cases b <;> norm_num [sub_get, table, Real.norm_eq_abs]
  refine ⟨x, h₁, h₂, fun y => ?_⟩
  have hc (j : Fin 3) : 2 ≤ ∑ a : Fin 4, |2 * x a j - y j| := by
    have h := abs_sub (1 / 2 - y j) (-1 / 2 - y j)
    rw [show (1 / 2 - y j) - (-1 / 2 - y j) = 1 by ring, abs_one] at h
    fin_cases j <;> norm_num [Fin.sum_univ_four, get, table] at h ⊢ <;> linarith
  have doubled_get (a : Fin 4) (j : Fin 3) :
      ((2 : ℝ) • x a - y) j = 2 * x a j - y j := rfl
  have hexpand (a : Fin 4) : ‖(2 : ℝ) • x a - y‖ =
      ∑ j : Fin 3, |2 * x a j - y j| := by
    rw [PiLp.norm_eq_of_L1]
    exact sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, doubled_get]
  have hlo : (6 : ℝ) ≤ ∑ a : Fin 4, ‖(2 : ℝ) • x a - y‖ := by
    simp_rw [hexpand]
    rw [sum_comm, Fin.sum_univ_three]
    linarith [hc 0, hc 1, hc 2]
  exact hlo

end ChordalL1
