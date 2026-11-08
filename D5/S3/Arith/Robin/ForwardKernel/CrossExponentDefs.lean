/- GID: D5/S3/Arith/Robin/ForwardKernel/CrossExponentDefs
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/CrossExponentDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Interval square norms and averaging scales for cross-exponent increments. -/

import D5.S3.Arith.Robin.ForwardKernel.VarianceTransferDefs

/-! Definitions of interval norms and cross-exponent averaging scales. -/

namespace D5.S3.Arith.Robin.ForwardKernel.CrossExponentDefs

open Set MeasureTheory Filter

open VarianceTransferDefs

noncomputable section

/-- The square-root integral norm on an oriented interval. -/
def intervalL2 (A B : ℝ) (u : ℝ → ℝ) : ℝ :=
  Real.sqrt (∫ x in A..B, u x ^ 2)

/-- An increment whose length is a fixed multiple of a power of its starting point. -/
def movingIncrement (E : ℝ → ℝ) (θ s x : ℝ) : ℝ :=
  increment E (s * x ^ θ) x

/-- The endpoint of a moving increment. -/
def movingShift (θ s x : ℝ) : ℝ :=
  x + s * x ^ θ

/-- The forward average over a window of length `R`. -/
def windowAverage (R : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..R, u (x + r)) / R

/-- Two successive forward averages at the same scale. -/
def doubleAverage (R : ℝ) (E : ℝ → ℝ) : ℝ → ℝ :=
  windowAverage R (windowAverage R E)

/-- The difference between double averages at consecutive dyadic scales. -/
def smoothingBlock (R : ℝ) (E : ℝ → ℝ) (x : ℝ) : ℝ :=
  doubleAverage R E x - doubleAverage (2 * R) E x

/-- Uniform cumulative variance bounds for lengths comparable to the scale `R`. -/
def ComparableLengthVarianceUpperFor (E R : ℝ → ℝ) : Prop :=
  (∀ᶠ X : ℝ in atTop, 0 < R X) ∧
  ∀ A B d : ℝ, 0 < A → A ≤ B → 0 < d →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ u ∈ Icc (A * R X) (B * R X),
        cumulativeVariance E (d * X) u ≤
          C * X * R X * Real.log X

end
end D5.S3.Arith.Robin.ForwardKernel.CrossExponentDefs
