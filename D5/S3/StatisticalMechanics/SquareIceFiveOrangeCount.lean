/- GID: D5/S3/StatisticalMechanics/SquareIceFiveOrangeCount
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/SquareIceFiveOrangeCount
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Five-orange height functions and finite downsets on the square lattice. -/

module

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Rat.Cast.Order
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Height functions of volume five reduce to five-point downsets of the ground height. -/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.SquareIceFiveOrangeCount

/-- The initial height of a width-`ℓ` stack. -/
def ground (ℓ : ℕ) (v : ℤ × ℤ) : ℤ :=
  if v.1 < 0 then |v.1| + |v.2|
  else if v.1 < (ℓ : ℤ) then |v.1 + v.2|
  else |v.2 + (ℓ : ℤ) - 1| + |v.1 - (ℓ : ℤ) + 1|

/-- Finite perturbations above the initial height satisfying the ice rule. -/
def IsHeight (ℓ : ℕ) (h : ℤ × ℤ → ℤ) : Prop :=
  {v | h v ≠ ground ℓ v}.Finite ∧
  (∀ v, ground ℓ v ≤ h v) ∧
  ∀ v, |h v - h (v.1 + 1, v.2)| = 1 ∧ |h v - h (v.1, v.2 + 1)| = 1

/-- The number of removed oranges. -/
noncomputable def volume (ℓ : ℕ) (h : ℤ × ℤ → ℤ) : ℚ :=
  ∑ᶠ v, ((h v - ground ℓ v : ℤ) : ℚ) / 2

/-- The five-orange count of Govindarajan, Guttmann and Subramanyan. -/
def claim : Prop :=
  ∀ ℓ : ℕ, 3 ≤ ℓ →
    (Nat.card {h : ℤ × ℤ → ℤ // IsHeight ℓ h ∧ volume ℓ h = 5} : ℤ) =
      (ℓ.choose 5 : ℤ) + 10 * ℓ.choose 3 - 2 * ℓ.choose 2 + 36 * ℓ - 14

private def Adjacent (u v : ℤ × ℤ) : Prop :=
  |u.1 - v.1| + |u.2 - v.2| = 1

private theorem ground_nonneg (ℓ : ℕ) (v : ℤ × ℤ) : 0 ≤ ground ℓ v := by
  unfold ground
  split_ifs <;> positivity

private theorem ground_nearest (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (v : ℤ × ℤ) :
    (∀ i : ℤ, 0 ≤ i → i < ℓ → ground ℓ v ≤ |v.1 - i| + |v.2 + i|) ∧
    ∃ i : ℤ, 0 ≤ i ∧ i < ℓ ∧ ground ℓ v = |v.1 - i| + |v.2 + i| := by
  constructor
  · intro i hi hil
    unfold ground
    split_ifs <;> simp only [abs_eq_max_neg] <;> omega
  · by_cases hx : v.1 < 0
    · refine ⟨0, by omega, by omega, ?_⟩
      unfold ground
      simp only [ite_eq_left hx, sub_zero, add_zero]
    · by_cases hxl : v.1 < (ℓ : ℤ)
      · refine ⟨v.1, by omega, hxl, ?_⟩
        unfold ground
        simp only [ite_eq_right hx, ite_eq_left hxl, sub_self, abs_zero, zero_add]
        congr 1 <;> omega
      · refine ⟨(ℓ : ℤ) - 1, by omega, by omega, ?_⟩
        unfold ground
        simp only [ite_eq_right hx, ite_eq_right hxl]
        conv_lhs => rw [add_comm]
        congr 2 <;> omega

private theorem ground_edges (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (v : ℤ × ℤ) :
    |ground ℓ v - ground ℓ (v.1 + 1, v.2)| = 1 ∧
    |ground ℓ v - ground ℓ (v.1, v.2 + 1)| = 1 := by
  unfold ground
  dsimp only
  split_ifs <;> simp only [abs_eq_max_neg] <;> omega

theorem result : claim := by
  sorry

end D5.S3.StatisticalMechanics.SquareIceFiveOrangeCount
