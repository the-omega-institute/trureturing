/- GID: D5/S3/Weil/Budget/OddTestBudgetUpperBound
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/OddTestBudgetUpperBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A feasible odd test bounds a negative rank-one pencil's budget from above. -/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-08-31):
   * D5 body-shape searches found the generic parity endpoint construction in
     `ParityWeylInterval`, but no finite-matrix theorem exposing this atom's
     negative rank-one pencil and odd-test family.
   * Pinned Mathlib has no exact rank-one budget theorem. The proof directly
     applies `Complex.normSq_pos`, `le_div_iff₀`, and `le_csInf_iff` to the
     source quotient set.
   * Public Lean code searches for negative rank-one and positive-semidefinite
     Rayleigh-quotient results found no exact third-party theorem. -/

open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Budget.OddTestBudgetUpperBound

/-- The Rayleigh quotients of all finite tests with nonzero boundary pairing. -/
def oddRayleighQuotients
    (n : Nat) (baseMatrix : Matrix (Fin n) (Fin n) Complex)
    (boundary : Fin n -> Complex) : Set Real :=
  {quotient | exists test : Fin n -> Complex,
    star boundary ⬝ᵥ test ≠ 0 /\
      quotient = Complex.re (star test ⬝ᵥ (baseMatrix *ᵥ test)) /
        Complex.normSq (star boundary ⬝ᵥ test)}

/-- The source upper endpoint: the reference budget plus the infimum of every
admissible finite odd-test Rayleigh quotient. -/
noncomputable def oddTestUpperEndpoint
    (n : Nat) (baseMatrix : Matrix (Fin n) (Fin n) Complex)
    (boundary : Fin n -> Complex) (reference : Real) : Real :=
  reference + sInf (oddRayleighQuotients n baseMatrix boundary)

/-- If the negative rank-one pencil is nonnegative for every admissible finite
odd test, then the candidate budget is at most the odd-family endpoint. -/
theorem odd_test_budget_at_most_upper
    (n : Nat) (baseMatrix : Matrix (Fin n) (Fin n) Complex)
    (boundary : Fin n -> Complex) (reference budget : Real)
    (admissibleTest : exists test : Fin n -> Complex,
      star boundary ⬝ᵥ test ≠ 0)
    (quotientsBoundedBelow :
      BddBelow (oddRayleighQuotients n baseMatrix boundary))
    (oddPencilNonnegative :
      forall test : Fin n -> Complex, star boundary ⬝ᵥ test ≠ 0 ->
        0 <= Complex.re (star test ⬝ᵥ (baseMatrix *ᵥ test)) -
          (budget - reference) *
            Complex.normSq (star boundary ⬝ᵥ test)) :
    budget <= oddTestUpperEndpoint n baseMatrix boundary reference := by
  fail_if_success rfl
  fail_if_success assumption
  have quotientSetNonempty :
      (oddRayleighQuotients n baseMatrix boundary).Nonempty := by
    obtain ⟨test, boundaryNonzero⟩ := admissibleTest
    exact ⟨_, test, boundaryNonzero, rfl⟩
  have infimumBound :
      budget - reference <=
        sInf (oddRayleighQuotients n baseMatrix boundary) := by
    refine (le_csInf_iff quotientsBoundedBelow quotientSetNonempty).2 ?_
    rintro quotient ⟨test, boundaryNonzero, rfl⟩
    have boundarySqPositive :
        0 < Complex.normSq (star boundary ⬝ᵥ test) :=
      Complex.normSq_pos.mpr boundaryNonzero
    apply (le_div_iff₀ boundarySqPositive).2
    linarith [oddPencilNonnegative test boundaryNonzero]
  unfold oddTestUpperEndpoint
  linarith

#print axioms odd_test_budget_at_most_upper

end D5.S3.Weil.Budget.OddTestBudgetUpperBound
