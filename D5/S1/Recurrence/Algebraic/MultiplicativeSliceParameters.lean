/- GID: D5/S1/Recurrence/Algebraic/MultiplicativeSliceParameters
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/MultiplicativeSliceParameters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two coefficient equations characterize a geometric real family and a constant unit family. -/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace D5.S1.Recurrence.Algebraic.MultiplicativeSliceParameters

/-- The two coefficient equations at every pair of positive indices. -/
def ForcedEquations (p : ℕ → ℝ) (c : ℕ → ℕ → ℝ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    (1 - p m) * (1 - p n) * c m n = 1 - p (m + n) ∧
    p m * p n * c m n = -p (m + n)

/-- The real geometric parameter family, including the zero parameter. -/
def GeometricFamily (p : ℕ → ℝ) (c : ℕ → ℕ → ℝ) : Prop :=
  ∃ t : ℝ, t ≠ 1 ∧ t ≠ -1 ∧
    (∀ m : ℕ, 0 < m → p m = t ^ m / (t ^ m - 1)) ∧
    (∀ m n : ℕ, 0 < m → 0 < n →
      c m n = -((t ^ m - 1) * (t ^ n - 1)) / (t ^ (m + n) - 1))

/-- The constant unit coefficients on positive indices. -/
def UnitFamily (p : ℕ → ℝ) (c : ℕ → ℕ → ℝ) : Prop :=
  (∀ m : ℕ, 0 < m → p m = 1) ∧
    (∀ m n : ℕ, 0 < m → 0 < n → c m n = -1)

/-- The coefficient equations have exactly the geometric and unit families of solutions;
any zero or unit entry propagates to every positive index. -/
theorem result (p : ℕ → ℝ) (c : ℕ → ℕ → ℝ) :
    (ForcedEquations p c ↔ GeometricFamily p c ∨ UnitFamily p c) ∧
    (ForcedEquations p c →
      ((∃ m, 0 < m ∧ p m = 0) → ∀ n, 0 < n → p n = 0) ∧
      ((∃ m, 0 < m ∧ p m = 1) → ∀ n, 0 < n → p n = 1) ∧
      ((∀ m, 0 < m → p m ≠ 0) ∧ (∀ m, 0 < m → p m ≠ 1) ∨
        (∀ n, 0 < n → p n = 0) ∨ (∀ n, 0 < n → p n = 1))) := by
  sorry

end D5.S1.Recurrence.Algebraic.MultiplicativeSliceParameters
