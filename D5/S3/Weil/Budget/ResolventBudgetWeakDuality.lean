/- GID: D5/S3/Weil/Budget/ResolventBudgetWeakDuality
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/ResolventBudgetWeakDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Local matching and resolvent feasibility give weak primal-dual order. -/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-08-31):
   * D5 searches for weak duality, Fourier majorants, resolvent budgets, and
     primal-dual inequalities found no exact owner. `ProjectiveStrongDuality`
     assumes attained finite strong duality on a circle carrier, while
     `ResolventFrontierGeometry` supplies adjacent budget geometry only.
   * Body-shape searches for the local pairing identity together with the two
     dual inequalities found no reusable D5 declaration or primitive.
   * Pinned Mathlib's cone-program file announces weak duality as future work;
     `integral_mono` and `integral_const_mul` are the exact measure-order and
     scalar-integration results used below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace D5.S3.Weil.Budget.ResolventBudgetWeakDuality

/-- A locally matched positive residual measure cannot make a feasible white
spectral floor exceed the value of a feasible Fourier-majorant certificate. -/
theorem resolvent_budget_weak_duality
    {Test : Type*}
    (fourierReading : Test → ℝ → ℝ)
    (atZero weilPairing : Test → ℝ)
    (mu : Measure ℝ)
    (phi : Test)
    (a lambda theta C : ℝ)
    (lambdaNonnegative : 0 ≤ lambda)
    (thetaNonnegative : 0 ≤ theta)
    (fourierIntegrable : Integrable (fourierReading phi) mu)
    (resolventIntegrable :
      Integrable (fun xi : ℝ => 1 / (xi ^ 2 + a ^ 2)) mu)
    (localMatching :
      weilPairing phi =
        lambda * atZero phi + ∫ xi, fourierReading phi xi ∂mu)
    (dualMajorant : ∀ xi : ℝ,
      0 ≤ fourierReading phi xi + theta * (1 / (xi ^ 2 + a ^ 2)))
    (dualFloor : 1 ≤ atZero phi + theta / (2 * a))
    (primalBudget :
      lambda / (2 * a) + ∫ xi, 1 / (xi ^ 2 + a ^ 2) ∂mu ≤ C) :
    lambda ≤ weilPairing phi + theta * C := by
  let weight : ℝ → ℝ := fun xi => 1 / (xi ^ 2 + a ^ 2)
  have negativeIntegrable : Integrable (fun xi => -theta * weight xi) mu :=
    resolventIntegrable.const_mul (-theta)
  have integralMajorant :
      ∫ xi, -theta * weight xi ∂mu ≤
        ∫ xi, fourierReading phi xi ∂mu := by
    apply integral_mono negativeIntegrable fourierIntegrable
    intro xi
    dsimp only [weight]
    linarith [dualMajorant xi]
  have integralMajorant' :
      -theta * (∫ xi, weight xi ∂mu) ≤
        ∫ xi, fourierReading phi xi ∂mu := by
    rw [integral_const_mul] at integralMajorant
    exact integralMajorant
  have weightedBudget :
      theta * (lambda / (2 * a) + ∫ xi, weight xi ∂mu) ≤ theta * C :=
    mul_le_mul_of_nonneg_left primalBudget thetaNonnegative
  have scaledFloor :
      lambda ≤ lambda * (atZero phi + theta / (2 * a)) :=
    calc
      lambda = lambda * 1 := by ring
      _ ≤ lambda * (atZero phi + theta / (2 * a)) :=
        mul_le_mul_of_nonneg_left dualFloor lambdaNonnegative
  calc
    lambda ≤ lambda * (atZero phi + theta / (2 * a)) := scaledFloor
    _ = lambda * atZero phi -
          theta * (∫ xi, weight xi ∂mu) +
          theta * (lambda / (2 * a) + ∫ xi, weight xi ∂mu) := by ring
    _ ≤ lambda * atZero phi +
          ∫ xi, fourierReading phi xi ∂mu + theta * C := by
      linarith [integralMajorant', weightedBudget]
    _ = weilPairing phi + theta * C := by rw [localMatching]

#print axioms resolvent_budget_weak_duality

end D5.S3.Weil.Budget.ResolventBudgetWeakDuality
