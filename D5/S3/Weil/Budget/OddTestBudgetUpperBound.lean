/- GID: D5/S3/Weil/Budget/OddTestBudgetUpperBound
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/OddTestBudgetUpperBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A feasible odd test bounds a negative rank-one pencil's budget from above. -/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/- Library-search audit trail (2026-08-31):
   * D5 body-shape searches for odd-test budgets, negative rank-one pencils,
     and Rayleigh upper bounds found no exact theorem or canonical definition.
   * Pinned Mathlib has no exact rank-one budget theorem. The proof directly
     applies `Complex.normSq_pos` and `le_div_iff₀` to the source quotient.
   * Public Lean code searches for negative rank-one and positive-semidefinite
     Rayleigh-quotient results found no exact third-party theorem. -/

open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Budget.OddTestBudgetUpperBound

/-- A selected finite odd test whose negative rank-one pencil is nonnegative
forces the candidate budget below the test's Rayleigh upper bound. -/
theorem odd_test_budget_at_most_upper
    (n : Nat) (baseMatrix : Matrix (Fin n) (Fin n) Complex)
    (boundary test : Fin n -> Complex) (reference budget : Real)
    (boundaryNonzero : star boundary ⬝ᵥ test ≠ 0)
    (oddPencilNonnegative :
      0 <= Complex.re (star test ⬝ᵥ (baseMatrix *ᵥ test)) -
        (budget - reference) * Complex.normSq (star boundary ⬝ᵥ test)) :
    budget <= reference +
      Complex.re (star test ⬝ᵥ (baseMatrix *ᵥ test)) /
        Complex.normSq (star boundary ⬝ᵥ test) := by
  have boundarySqPositive :
      0 < Complex.normSq (star boundary ⬝ᵥ test) :=
    Complex.normSq_pos.mpr boundaryNonzero
  have shiftedBudgetBound :
      (budget - reference) * Complex.normSq (star boundary ⬝ᵥ test) <=
        Complex.re (star test ⬝ᵥ (baseMatrix *ᵥ test)) := by
    linarith
  have quotientBound :
      budget - reference <=
        Complex.re (star test ⬝ᵥ (baseMatrix *ᵥ test)) /
          Complex.normSq (star boundary ⬝ᵥ test) :=
    (le_div_iff₀ boundarySqPositive).2 shiftedBudgetBound
  linarith

#print axioms odd_test_budget_at_most_upper

end D5.S3.Weil.Budget.OddTestBudgetUpperBound
