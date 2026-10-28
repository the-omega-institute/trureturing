import Reg.Support.DependentFamily
import D5.S3.Combinatorics.MinimalForts.RotationWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.MinimalForts.RotationWindow

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.MinimalForts.RotationWindow

abbrev Parameters := ℝ × ℝ × ℤ × ℤ

def signature : Signature where
  Params := Parameters
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p T => (p.2.2.1 : ℝ) * p.2.1 + (p.2.2.2 : ℝ) * p.1 - T)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ p b : ℝ, 0 < p → Irrational (b / p) →
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ N : ℕ, M ≤ N → ∀ T : ℝ,
      ∃ x z : ℤ, (N : ℤ) ≤ x ∧ x ≤ 3 * (N : ℤ) ∧
        |R.readout () (p, b, x, z) T| < ε

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨M, hM⟩ := h 1 (Real.sqrt 2) (by norm_num)
    (by simpa only [div_one] using irrational_sqrt_two) (1 / 2) (by norm_num)
  obtain ⟨x, z, _, _, hbad⟩ := hM M le_rfl 0
  norm_num [rejected, realize] at hbad

def family : Registration arena (type_of% (@uniform_real_window)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_real_window, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(1, 0, 0, 0), 0, 1, ?_⟩
    norm_num [actual, realize]

end Reg.D5.S3.Combinatorics.MinimalForts.RotationWindow
