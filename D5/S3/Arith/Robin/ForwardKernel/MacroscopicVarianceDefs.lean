/- GID: D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Window bounds and macroscopic increments define block errors and weighted moments. -/

import D5.S3.Arith.Robin.ForwardKernel.MovingLengthCells
import D5.S3.Arith.Robin.ForwardKernel.MomentTransferDefs
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Macroscopic length functions, block errors and weighted covariance. -/

namespace D5.S3.Arith.Robin.ForwardKernel.MacroscopicVarianceDefs

open Set MeasureTheory
open scoped BigOperators
open VarianceTransferDefs MovingLengthCells MomentTransferDefs DyadicProbability

noncomputable section

/-- Relative variance error throughout a comparable macroscopic window. -/
def VarianceWindowBound (E : ℝ → ℝ) (α β X ε : ℝ) : Prop :=
  ∀ Y ∈ Icc (X / 2) (4 * X), ∀ v : ℝ,
    Y ^ α ≤ v → v ≤ Y ^ β →
    |cumulativeVariance E Y v / (Y * v * Real.log (Y / v)) - 1| ≤ ε

/-- The square-integral scale for increments of length `X^θ`. -/
def varianceScale (θ X : ℝ) : ℝ := X * X ^ θ * Real.log X

/-- An increment whose length is prescribed at the macroscopic position. -/
def macroIncrement (E a : ℝ → ℝ) (θ X x : ℝ) : ℝ :=
  increment E (X ^ θ * a (x / X)) x

/-- The squared integral on the dyadic interval divided by its variance scale. -/
def normalizedSquare (θ X : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ x in X..(2 * X), f x ^ 2) / varianceScale θ X

/-- A nonnegative continuously differentiable length with uniform size and derivative bounds. -/
def MacroscopicLengthBounds (a : ℝ → ℝ) (M L : ℝ) : Prop :=
  ContDiffOn ℝ 1 a (Icc (1 : ℝ) 2) ∧
  (∀ u ∈ Icc (1 : ℝ) 2, a u ∈ Icc (0 : ℝ) M) ∧
  ∀ u ∈ Icc (1 : ℝ) 2, |derivWithin a (Icc (1 : ℝ) 2) u| ≤ L

/-- The normalized sum of squared errors from freezing at the left endpoint of each block. -/
def freezingError (E a : ℝ → ℝ) (θ : ℝ) (n : ℕ) (X : ℝ) : ℝ :=
  (∑ j ∈ Finset.range n,
    ∫ x in (cellPoint n j * X)..(cellPoint n (j + 1) * X),
      (macroIncrement E a θ X x - increment E (X ^ θ * a (cellPoint n j)) x) ^ 2) /
    varianceScale θ X

/-- Covariance of two macroscopic increments with a macroscopic weight. -/
def weightedMacroCovariance (E a b w : ℝ → ℝ) (θ X : ℝ) : ℝ :=
  (∫ x in X..(2 * X), w (x / X) * macroIncrement E a θ X x *
    macroIncrement E b θ X x) / varianceScale θ X

/-- A weighted covariance under logarithmic dyadic probability. -/
def weightedDyadicCovariance (E φ : ℝ → ℝ) (a b X s t : ℝ) : ℝ :=
  ∫ x, φ (dyadicU X x) * dyadicB E a s x * dyadicB E b t x
    ∂dyadicProbabilityMeasure X

/-- A weighted first moment under logarithmic dyadic probability. -/
def weightedDyadicFirstMoment (E φ : ℝ → ℝ) (θ X s : ℝ) : ℝ :=
  ∫ x, φ (dyadicU X x) * dyadicB E θ s x ∂dyadicProbabilityMeasure X

end

end D5.S3.Arith.Robin.ForwardKernel.MacroscopicVarianceDefs
