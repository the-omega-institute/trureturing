/- GID: D5/S3/Analytic/GoldenTomography/FinitePronySecondMomentRange
   generality: G
   mirror-B: D5/B/S3/Analytic/GoldenTomography/FinitePronySecondMomentRange
   mirror-E: none(waiver:exact-symbolic-construction)
   anchors: []
   utility: none
   digest: Feasible means, second moments and minimum support for positive Prony families. -/

import D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction
import OmegaMath.MeasureTheory.FiniteWeightedSecondMoment
import OmegaBuild.Commands

/-!
# The attainable second moments of positive Prony families

Chapter 14 §14.3 of *Omega Unification* uses an observed scalar Prony moment.
Specialize the finite weighted-sum criterion to that moment to recover the
feasible mean, the second-moment interval and the minimum number of nodes.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.GoldenTomography.FinitePronySecondMomentRange

open D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Realize three scalar moments by distinct nodes with positive weights. -/
def HasMoments (n : ℕ) (a b M x s : K) : Prop :=
  ∃ t w : Fin n → K, Function.Injective t ∧
    (∀ i, a < t i ∧ t i < b) ∧ (∀ i, 0 < w i) ∧
    pronyMoment t w 0 = M ∧ pronyMoment t w 1 = M * x ∧ pronyMoment t w 2 = s

/-- Full feasibility and minimum node count for the scalar Prony observations. -/
theorem finite_prony_second_moment_range {a b M x s : K} (hM : 0 < M) :
    (∀ n, HasMoments n a b M x s →
      a < x ∧ x < b ∧ M * x ^ 2 ≤ s ∧ s < M * ((a + b) * x - a * b) ∧
        (s = M * x ^ 2 ↔ n = 1)) ∧
    (a < x ∧ x < b ∧ M * x ^ 2 ≤ s ∧ s < M * ((a + b) * x - a * b) →
      HasMoments (if s = M * x ^ 2 then 1 else 2) a b M x s) :=
  Omega.MeasureTheory.FiniteWeightedSecondMoment.finite_weighted_second_moment_range hM

end D5.S3.Analytic.GoldenTomography.FinitePronySecondMomentRange
