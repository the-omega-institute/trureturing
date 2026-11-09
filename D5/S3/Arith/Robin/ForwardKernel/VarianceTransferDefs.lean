/- GID: D5/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/VarianceTransferDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Increments, profile averages and parameterized short-interval variance hypotheses for a real error term. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Definitions for transferring short-interval variance asymptotics to moving profile averages. -/

namespace D5.S3.Arith.Robin.ForwardKernel.VarianceTransferDefs

open Set MeasureTheory Filter

noncomputable section

/-- The increment of `E` over a step of length `h` starting at `x`. -/
def increment (E : ℝ → ℝ) (h x : ℝ) : ℝ :=
  E (x + h) - E x

/-- The cumulative variance of increments of length `h` up to `Y`. -/
def cumulativeVariance (E : ℝ → ℝ) (Y h : ℝ) : ℝ :=
  ∫ x in (1 : ℝ)..Y, increment E h x ^ 2

/-- Lebesgue measure restricted to the unit interval. -/
abbrev unitMeasure : Measure ℝ :=
  volume.restrict (Set.Ioc (0 : ℝ) 1)

/-- A Borel representative of an integrable real profile on the unit interval. -/
def ProfileIntegrable (g : ℝ → ℝ) : Prop :=
  Measurable g ∧ Integrable g unitMeasure

/-- An exponent strictly inside a band contained in `(0,1)`. -/
def ValidBand (α θ β : ℝ) : Prop :=
  0 < α ∧ α < θ ∧ θ < β ∧ β < 1

/-- The profile-weighted integral of increments of length at most `h` at `x`. -/
def profilePrimitive (E g : ℝ → ℝ) (h x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..h, g (u / h) * increment E u x

/-- The profile primitive normalized by the square of its length. -/
def profileAverage (E g : ℝ → ℝ) (h x : ℝ) : ℝ :=
  profilePrimitive E g h x / h ^ 2

/-- The profile average at the moving length `x^θ`. -/
abbrev movingAverage (E : ℝ → ℝ) (θ : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  profileAverage E g (x ^ θ) x

/-- The integral of the absolute value of a profile on the unit interval. -/
def profileL1 (g : ℝ → ℝ) : ℝ :=
  ∫ s, |g s| ∂unitMeasure

/-- The oriented integral of a profile from `r` to one. -/
def tailProfile (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ s in r..(1 : ℝ), g s

/-- The quadratic energy of a profile for the covariance kernel `min s t`. -/
def Q (g : ℝ → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, g s * g t * min s t

/-- The comparison length `c X^θ`. -/
def fixedLength (θ c X : ℝ) : ℝ :=
  c * X ^ θ

/-- The logarithm `log (X / (c X^θ))`. -/
def lengthLog (θ c X : ℝ) : ℝ :=
  Real.log (X / fixedLength θ c X)

/-- The dyadic mean-square scale `X^(1-θ) log X`. -/
def meanSquareScale (θ X : ℝ) : ℝ :=
  X ^ (1 - θ) * Real.log X

/-- Measurability together with boundedness on every compact interval. -/
def LocallyBoundedMeasurable (E : ℝ → ℝ) : Prop :=
  Measurable E ∧ ∀ a b : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Set.Icc a b, |E x| ≤ M

/-- The cumulative variance is asymptotic to `Y h log (Y/h)`, uniformly for
`Y^α ≤ h ≤ Y^β`. -/
def CumulativeVarianceBandAsymptoticFor (E : ℝ → ℝ) (α β : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℝ in atTop, ∀ h : ℝ,
    Y ^ α ≤ h → h ≤ Y ^ β →
      |cumulativeVariance E Y h / (Y * h * Real.log (Y / h)) - 1| ≤ ε

/-- A uniform short-interval mean-square bound for relative steps `θ ≤ 1`. -/
def ShortIntervalMeanSquareBoundFor (E : ℝ → ℝ) : Prop :=
  ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
    (∫ x in X..(2 * X), (E ((1 + θ) * x) - E x) ^ 2) ≤
      C * θ * X ^ 2 * (Real.log (2 / θ)) ^ 2

end

end D5.S3.Arith.Robin.ForwardKernel.VarianceTransferDefs
