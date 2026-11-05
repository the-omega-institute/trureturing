/- GID: D5/S3/Analytic/IncompleteBetaShape/Defs
   generality: G
   mirror-B: D5/B/S3/Analytic/IncompleteBetaShape/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coefficient differences for real shifts of the first incomplete-beta parameter. -/

import D5.S3.Analytic.IncompleteBeta.Defs

namespace D5.S3.Analytic.IncompleteBetaShape.Defs

open D5.S3.Analytic.IncompleteBeta

/-- The coefficient of x^n in the normalized difference
x^(-2a-alpha-beta) (1-x)^(-2b) psi, by (1) and (6) of the source.
These coefficients do not depend on x, so its x-quantifier is vacuous for them. -/
noncomputable def psi (a b α β : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (coeff (a + α) b k * coeff (a + β) b (n - k) -
      coeff a b k * coeff (a + α + β) b (n - k))

def claim : Prop :=
  ∀ a b α β : ℝ, 0 < a → 0 < b → 0 < α → 0 < β →
    ∀ n : ℕ, (b < 1 → psi a b α β n < 0) ∧
      (1 < b → 0 < psi a b α β n)

end D5.S3.Analytic.IncompleteBetaShape.Defs
