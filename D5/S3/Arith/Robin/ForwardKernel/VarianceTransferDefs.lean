/- GID: D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Increments, cumulative variances and triangular averages of a real error term, with the short-interval variance hypotheses. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Definitions for transferring short-interval variance asymptotics to moving triangular averages. -/

namespace D5.S3.Arith.Robin.ForwardKernel.VarianceTransferDefs

open Set MeasureTheory Filter

noncomputable section

/-- The increment of `E` over a step of length `h` starting at `x`. -/
def increment (E : ℝ → ℝ) (h x : ℝ) : ℝ :=
  E (x + h) - E x

/-- The cumulative variance of increments of length `h` up to `Y`. -/
def cumulativeVariance (E : ℝ → ℝ) (Y h : ℝ) : ℝ :=
  ∫ x in (1 : ℝ)..Y, increment E h x ^ 2

/-- The integral of all increments of length at most `h` at `x`. -/
def triangularPrimitive (E : ℝ → ℝ) (h x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..h, increment E u x

/-- The triangular average `h⁻² ∫₀ʰ (E(x+u) - E(x)) du`. -/
def triangularAverage (E : ℝ → ℝ) (h x : ℝ) : ℝ :=
  triangularPrimitive E h x / h ^ 2

/-- The length `c X^{4/5}`. -/
def fixedLength (c X : ℝ) : ℝ :=
  c * X ^ (4 / 5 : ℝ)

/-- The logarithm `log (X / (c X^{4/5}))`. -/
def lengthLog (c X : ℝ) : ℝ :=
  Real.log (X / fixedLength c X)

/-- The dyadic mean-square scale `X^{1/5} log X`. -/
def meanSquareScale (X : ℝ) : ℝ :=
  X ^ (1 / 5 : ℝ) * Real.log X

/-- Measurability together with boundedness on every compact interval. -/
def LocallyBoundedMeasurable (E : ℝ → ℝ) : Prop :=
  Measurable E ∧ ∀ a b : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Set.Icc a b, |E x| ≤ M

/-- The cumulative variance is asymptotic to `Y h log (Y/h)`, uniformly for
`Y^{3/4} ≤ h ≤ Y^{7/8}`. -/
def CumulativeVarianceBandAsymptoticFor (E : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℝ in atTop, ∀ h : ℝ,
    Y ^ (3 / 4 : ℝ) ≤ h → h ≤ Y ^ (7 / 8 : ℝ) →
      |cumulativeVariance E Y h / (Y * h * Real.log (Y / h)) - 1| ≤ ε

/-- A uniform short-interval mean-square bound for relative steps `θ ≤ 1`. -/
def ShortIntervalMeanSquareBoundFor (E : ℝ → ℝ) : Prop :=
  ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
    (∫ x in X..(2 * X), (E ((1 + θ) * x) - E x) ^ 2) ≤
      C * θ * X ^ 2 * (Real.log (2 / θ)) ^ 2

end

end D5.S3.Arith.Robin.ForwardKernel.VarianceTransferDefs
