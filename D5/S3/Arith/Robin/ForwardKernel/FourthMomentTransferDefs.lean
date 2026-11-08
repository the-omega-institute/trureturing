/- GID: D5/S3/Arith/Robin/ForwardKernel/FourthMomentTransferDefs
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FourthMomentTransferDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourth energy and interval-weighted moments define moving-length contracts. -/

import D5.S3.Arith.Robin.ForwardKernel.MomentTransferDefs
import D5.S3.Arith.Robin.ForwardKernel.MovingLengthCells

/-! Fixed-scale and moving-length fourth-moment definitions. -/

namespace D5.S3.Arith.Robin.ForwardKernel.FourthMomentTransferDefs

open Set MeasureTheory Filter
open scoped Topology BigOperators
open VarianceTransferDefs MomentTransferDefs DyadicProbability MovingLengthCells

noncomputable section
set_option autoImplicit false

/-- Local fourth energy on a window. -/
def localFourthEnergyWindow (E : ℝ → ℝ) (α β C X ε : ℝ) : Prop :=
  ∀ A B : ℝ, X / 2 ≤ A → A ≤ B → B ≤ 4 * X →
    ∀ v : ℝ, (4 * X) ^ α ≤ v → v ≤ (X / 2) ^ β →
      (∫ y in A..B, |increment E v y| ^ 4) ≤
        C * v ^ 2 * Real.log X ^ 2 * (B - A + ε * X)

/-- The local fourth-energy hypothesis. -/
def LocalFourthEnergyFor (E : ℝ → ℝ) (α β C : ℝ) : Prop :=
  0 ≤ C ∧ ∃ ε : ℝ → ℝ, (∀ X, 0 ≤ ε X) ∧
    Tendsto ε atTop (𝓝 0) ∧
    ∀ᶠ X : ℝ in atTop, localFourthEnergyWindow E α β C X (ε X)

/-- A fixed-scale normalized increment. -/
def fixedScaleB (E : ℝ → ℝ) (θ c X x : ℝ) : ℝ :=
  increment E (c * X ^ θ) x / Real.sqrt (X ^ θ * Real.log X)

/-- A mixed moment on a macroscopic interval. -/
def fixedBlockMoment (E : ℝ → ℝ) (θ : ℝ) (k : ℕ)
    (c : Fin k → ℝ) (u v X : ℝ) : ℝ :=
  ∫ x, (Icc u v).indicator (fun _ : ℝ => (1 : ℝ)) (dyadicU X x) *
    (∏ i, fixedScaleB E θ (c i) X x) ∂dyadicProbabilityMeasure X

/-- Interval-weighted fixed-scale convergence. -/
def FixedScaleMixedMoments (E : ℝ → ℝ) (θ : ℝ) (k : ℕ)
    (W : (Fin k → ℝ) → ℝ) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ c : Fin k → ℝ,
    (∀ i, c i ∈ Icc (0 : ℝ) M) → ∀ u v : ℝ,
    1 ≤ u → u < v → v ≤ 2 →
    Tendsto (fixedBlockMoment E θ k c u v) atTop
      (𝓝 ((dyadicProbabilityMeasure 1).real (Icc u v) * W c))

/-- A moving normalized increment. -/
def movingB (E a : ℝ → ℝ) (θ X x : ℝ) : ℝ :=
  fixedScaleB E θ (a (dyadicU X x)) X x

/-- A normalized increment frozen on cells. -/
def frozenB (E a : ℝ → ℝ) (θ : ℝ) (n : ℕ) (X x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n,
    (Ioc (cellPoint n j) (cellPoint n (j + 1))).indicator
      (fun _ : ℝ => fixedScaleB E θ (a (cellPoint n j)) X x) (dyadicU X x)

/-- The uniform fourth-moment constant. -/
def fourthK (C M : ℝ) : ℝ := 1312 * C * M ^ 2 / Real.log 2

/-- The fourth-order freezing constant. -/
def freezeCoefficient (C L : ℝ) (n : ℕ) : ℝ :=
  1312 * C * (1 + L) ^ 2 / (3 * (n : ℝ) ^ 2 * Real.log 2)

end
end D5.S3.Arith.Robin.ForwardKernel.FourthMomentTransferDefs
