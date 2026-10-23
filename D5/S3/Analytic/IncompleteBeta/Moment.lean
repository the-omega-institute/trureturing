/- GID: D5/S3/Analytic/IncompleteBeta/Moment
   generality: G
   mirror-B: D5/B/S3/Analytic/IncompleteBeta/Moment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Basic]
   utility: none
   digest: Finite coefficient convolution and its beta moment kernel. -/

import D5.S3.Analytic.IncompleteBeta.Defs

noncomputable section

open scoped BigOperators

namespace D5.S3.Analytic.IncompleteBeta

def convolution (a s t : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), coeff a s k * coeff a t (n - k)

def W (a : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    u ^ (a + k) * (1 - u) ^ (a + n - k) /
      (Real.Gamma (a + k + 1) * Real.Gamma (a + n - k + 1))

end D5.S3.Analytic.IncompleteBeta
