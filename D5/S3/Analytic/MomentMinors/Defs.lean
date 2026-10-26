/- GID: D5/S3/Analytic/MomentMinors/Defs
   generality: G
   mirror-B: D5/B/S3/Analytic/MomentMinors/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.Bochner.Basic, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real]
   utility: none
   digest: Probability laws, moment gaps, and the two moment minor inequalities. -/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open MeasureTheory

namespace D5.S3.Analytic.MomentMinors.Defs

/-- The first moment of a real probability law. -/
def mean (μ : Measure ℝ) : ℝ := ∫ x, x ∂μ

/-- The standing assumption that moments exist at every parameter of the interval `I`.
Logarithmic moments are required at the two limiting parameters. -/
structure Admissible (μ : Measure ℝ) (I : Set ℝ) : Prop where
  probability : IsProbabilityMeasure μ
  positive : ∀ᵐ x ∂μ, 0 < x
  integrable_id : Integrable id μ
  integrable_rpow : ∀ s ∈ I, Integrable (fun x : ℝ => x ^ s) μ
  integrable_log : 0 ∈ I → Integrable Real.log μ
  integrable_mul_log : 1 ∈ I → Integrable (fun x : ℝ => x * Real.log x) μ

/-- The normalized moment gap, including its two logarithmic limits. -/
def lam (μ : Measure ℝ) (s : ℝ) : ℝ :=
  if s = 0 then Real.log (mean μ) - ∫ x, Real.log x ∂μ
  else if s = 1 then (∫ x, x * Real.log x ∂μ) - mean μ * Real.log (mean μ)
  else ((∫ x, x ^ s ∂μ) - mean μ ^ s) / (s * (s - 1))

/-- The second minor of the midpoint moment kernel. -/
def xi (μ : Measure ℝ) (s t : ℝ) : ℝ :=
  lam μ s * lam μ t - lam μ ((s + t) / 2) ^ 2

/-- The iterated second minor on two parameter pairs. -/
def phi (μ : Measure ℝ) (s t u v : ℝ) : ℝ :=
  xi μ s t * xi μ u v -
    (xi μ ((s + u) / 2) ((t + v) / 2) -
      xi μ ((s + v) / 2) ((t + u) / 2)) ^ 2

/-- The second minor restricted to pairs of a common displacement. -/
def sigma (μ : Measure ℝ) (a x : ℝ) : ℝ := xi μ x (x + a)

/-- The second minor of the displaced midpoint kernel. -/
def theta (μ : Measure ℝ) (a x y : ℝ) : ℝ :=
  sigma μ a x * sigma μ a y - sigma μ a ((x + y) / 2) ^ 2

/-- The eight-parameter moment minor inequality. -/
def claim1 : Prop :=
  ∀ (I : Set ℝ), I.OrdConnected → ∀ (μ : Measure ℝ), Admissible μ I →
  ∀ (r₁ s₁ u₁ v₁ r₂ s₂ u₂ v₂ : ℝ),
    r₁ ∈ I → s₁ ∈ I → u₁ ∈ I → v₁ ∈ I →
    r₂ ∈ I → s₂ ∈ I → u₂ ∈ I → v₂ ∈ I →
    phi μ r₁ s₁ u₁ v₁ * phi μ r₂ s₂ u₂ v₂ ≥
      ((xi μ ((r₁ + r₂) / 2) ((s₁ + s₂) / 2) -
          xi μ ((r₁ + s₂) / 2) ((s₁ + r₂) / 2)) *
        (xi μ ((u₁ + u₂) / 2) ((v₁ + v₂) / 2) -
          xi μ ((u₁ + v₂) / 2) ((v₁ + u₂) / 2)) -
        (xi μ ((r₁ + u₂) / 2) ((s₁ + v₂) / 2) -
          xi μ ((r₁ + v₂) / 2) ((s₁ + u₂) / 2)) *
        (xi μ ((u₁ + r₂) / 2) ((v₁ + s₂) / 2) -
          xi μ ((u₁ + s₂) / 2) ((v₁ + r₂) / 2))) ^ 2

/-- The displaced-parameter moment minor inequality. -/
def claim2 : Prop :=
  ∀ (I : Set ℝ), I.OrdConnected → ∀ (μ : Measure ℝ), Admissible μ I →
  ∀ (a x y z v : ℝ),
    x ∈ I → x + a ∈ I → y ∈ I → y + a ∈ I →
    z ∈ I → z + a ∈ I → v ∈ I → v + a ∈ I →
    theta μ a x y * theta μ a z v ≥
      (theta μ a ((x + z) / 2) ((y + v) / 2) -
        theta μ a ((x + v) / 2) ((y + z) / 2)) ^ 2

/-- Both moment minor inequalities for every admissible law on every interval. -/
def claim : Prop := claim1 ∧ claim2

end D5.S3.Analytic.MomentMinors.Defs
