/- GID: D5/S1/Depth/ContinuedFractions/CompleteQuotientRecursion
   generality: I
   mirror-B: D5/B/S1/Depth/ContinuedFractions/CompleteQuotientRecursion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A quadratic-chain certificate records inverse continued-fraction pullbacks, whose next constant coefficient equals the current leading coefficient and whose discriminant is constant along the complete-quotient sequence. -/

import D5.S1.Depth.ContinuedFractions.CompleteQuotientBound
import D5.S1.Depth.ContinuedFractions.QuadraticImpliesPeriodic

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'complete_quotient_quadratic_chain_invariants' D5
     Golden/Frozen/accepted` returned no public or private hit.
   * `rg -n 'completeQuotient|QuadraticCoefficients|discriminant' D5/S1/Depth/`
     found the public complete-quotient iteration in `QuadraticImpliesPeriodic` and the
     public pullback/discriminant algebra in `CompleteQuotientBound`; no public theorem
     propagates the pullback along a coefficient chain, and no private hit covers it.
   * Pinned-Mathlib searches for quadratic chains and pullback discriminants returned no
     reusable declaration. The proof reuses `pullback_discriminant` at every successor.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Depth.ContinuedFractions.CompleteQuotientRecursion

open D5.S1.Depth.ContinuedFractions.PeriodicImpliesQuadratic
open D5.S1.Depth.ContinuedFractions.QuadraticImpliesPeriodic
open D5.S1.Depth.ContinuedFractions.CompleteQuotientBound

/-- The inverse of the continued-fraction step `y ↦ q + 1 / y`.

Its relation reads `y * (x - q) = 1`, so it sends a quadratic equation for the
current complete quotient `x` to one for the next complete quotient `y`. -/
def inverseStep (q : ℤ) : MobiusInt := ⟨0, 1, 1, -q⟩

/-- A complete-quotient sequence equipped with compatible nonzero integral quadratic
equations and their exact inverse-step pullback recurrence. -/
structure QuadraticChain (x : ℝ) where
  coefficients : ℕ → QuadraticCoefficients
  nonzero : ∀ n,
    (coefficients n).a ≠ 0 ∨ (coefficients n).b ≠ 0 ∨ (coefficients n).c ≠ 0
  equation : ∀ n,
    let q := completeQuotient x n
    ((coefficients n).a : ℝ) * q ^ 2 +
        ((coefficients n).b : ℝ) * q + (coefficients n).c = 0
  inverse_step : ∀ n,
    (inverseStep (Int.floor (completeQuotient x n))).Rel
      (completeQuotient x (n + 1)) (completeQuotient x n)
  recurrence : ∀ n,
    coefficients (n + 1) =
      (coefficients n).pullback (inverseStep (Int.floor (completeQuotient x n)))

/-- In the inverse-step recurrence, the next constant coefficient is the current
leading coefficient. -/
theorem next_constant_eq_current_leading {x : ℝ} (chain : QuadraticChain x) (n : ℕ) :
    (chain.coefficients (n + 1)).c = (chain.coefficients n).a := by
  rw [chain.recurrence n]
  simp [QuadraticCoefficients.pullback, inverseStep]

/-- Every quadratic equation in a complete-quotient chain has the initial
discriminant. -/
theorem quadratic_chain_discriminant_eq_initial {x : ℝ} (chain : QuadraticChain x)
    (n : ℕ) :
    (chain.coefficients n).discriminant = (chain.coefficients 0).discriminant := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [chain.recurrence n, pullback_discriminant]
      simp [inverseStep, MobiusInt.det, ih]

/-- The inverse-step quadratic recurrence simultaneously supplies the classical
coefficient crossover and a single discriminant shared by the whole sequence. -/
theorem complete_quotient_quadratic_chain_invariants {x : ℝ} (chain : QuadraticChain x) :
    (∀ n, (chain.coefficients (n + 1)).c = (chain.coefficients n).a) ∧
      ∃ D : ℤ, ∀ n, (chain.coefficients n).discriminant = D := by
  constructor
  · exact fun n => next_constant_eq_current_leading chain n
  · refine ⟨(chain.coefficients 0).discriminant, ?_⟩
    exact fun n => quadratic_chain_discriminant_eq_initial chain n

example :
    (QuadraticCoefficients.pullback ⟨1, -1, -1⟩ (inverseStep 1)).c = 1 := by
  norm_num [QuadraticCoefficients.pullback, inverseStep]

#print axioms complete_quotient_quadratic_chain_invariants

end D5.S1.Depth.ContinuedFractions.CompleteQuotientRecursion
