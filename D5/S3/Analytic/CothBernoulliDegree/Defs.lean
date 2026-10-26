/- GID: D5/S3/Analytic/CothBernoulliDegree/Defs
   generality: G
   mirror-B: D5/B/S3/Analytic/CothBernoulliDegree/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp, mathlib/module/Mathlib.NumberTheory.Bernoulli]
   utility: none
   digest: Bernoulli remainder of the hyperbolic cotangent and its derivative sign claim. -/

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.Bernoulli

namespace D5.S3.Analytic.CothBernoulliDegree.Defs

open scoped BigOperators

/-- The Bernoulli remainder of `coth t / t`, with integer powers. -/
noncomputable def p (n : ℕ) (t : ℝ) : ℝ :=
  Real.cosh t / Real.sinh t / t -
    ∑ k ∈ Finset.range (n + 1),
      (2 : ℝ) ^ (2 * k) * (bernoulli (2 * k) : ℝ) /
        (Nat.factorial (2 * k) : ℝ) * t ^ ((2 * k : ℤ) - 2)

/-- The signed, power-weighted remainder. -/
noncomputable def P (m n : ℕ) (t : ℝ) : ℝ := (-1) ^ n * t ^ m * p n t

/-- Strict positivity at order `m + 2n - 2`, and its failure at the next order. -/
def claim : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 2 ≤ n →
    (∀ t : ℝ, 0 < t → 0 < iteratedDeriv (m + 2 * n - 2) (P m n) t) ∧
    ¬ (∀ t : ℝ, 0 < t → 0 < iteratedDeriv (m + 2 * n - 1) (P m n) t)

end D5.S3.Analytic.CothBernoulliDegree.Defs
