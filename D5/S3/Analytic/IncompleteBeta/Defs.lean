/- GID: D5/S3/Analytic/IncompleteBeta/Defs
   generality: G
   mirror-B: D5/B/S3/Analytic/IncompleteBeta/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Basic]
   utility: none
   digest: Coefficients, Turanian coefficient sums, and Karp's incomplete-beta positivity claim. -/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

namespace D5.S3.Analytic.IncompleteBeta

noncomputable def coeff (a b : ℝ) (j : ℕ) : ℝ :=
  Real.Gamma (a + b + j) / (Real.Gamma b * Real.Gamma (a + j + 1))

noncomputable def phi (a b α β : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (coeff a (b + α) k * coeff a (b + β) (n - k) -
      coeff a b k * coeff a (b + α + β) (n - k))

def claim : Prop :=
  ∀ a b α β : ℝ, 0 < a → 0 < b → 0 < α → 0 < β →
    ∀ n : ℕ, 0 < phi a b α β n

end D5.S3.Analytic.IncompleteBeta
