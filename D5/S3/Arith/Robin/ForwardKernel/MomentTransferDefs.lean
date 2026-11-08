/- GID: D5/S3/Arith/Robin/ForwardKernel/MomentTransferDefs
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MomentTransferDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dyadic moment interfaces and the fourth Brownian kernel. -/

import D5.S3.Arith.Robin.ForwardKernel.DyadicProbability
import D5.S3.Arith.Robin.ForwardKernel.WeightRemoval
import Mathlib.MeasureTheory.Integral.Pi

/-! Shared definitions for transferring moments of moving profile responses. -/

namespace D5.S3.Arith.Robin.ForwardKernel.MomentTransferDefs

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs ProfileKernelDefs DyadicProbability

noncomputable section
set_option autoImplicit false

/-- The product of `k` copies of Lebesgue measure on the unit interval. -/
abbrev cubeMeasure (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi (fun _ : Fin k => unitMeasure)

/-- The complementary exponent `1 - θ`. -/
def kappa (θ : ℝ) : ℝ := 1 - θ

/-- The exponent of the macroscopic scale in the normalized response. -/
def dyadicR (θ : ℝ) : ℝ := kappa θ / 2

/-- The position within the dyadic interval, scaled by its left endpoint. -/
def dyadicU (X x : ℝ) : ℝ := x / X

/-- The increment of length `s * x^θ`, normalized by its local variance scale. -/
def dyadicB (E : ℝ → ℝ) (θ s x : ℝ) : ℝ :=
  increment E (s * x ^ θ) x / Real.sqrt (x ^ θ * Real.log x)

/-- The price-weighted profile response normalized by the dyadic mean-square scale. -/
def dyadicZ (E : ℝ → ℝ) (θ : ℝ) (g : ℝ → ℝ) (X x : ℝ) : ℝ :=
  profileResponse E θ g x / Real.sqrt (meanSquareScale θ X)

/-- The mixed increment moment with its macroscopic position weight. -/
def dyadicMixedMoment
    (E : ℝ → ℝ) (θ X : ℝ) (k : ℕ) (s : Fin k → ℝ) : ℝ :=
  ∫ x, dyadicU X x ^ ((k : ℝ) * dyadicR θ) *
    ∏ i, dyadicB E θ (s i) x
    ∂dyadicProbabilityMeasure X

/-- A uniform absolute moment bound and a measurable limit of the mixed moments. -/
def MomentInterface
    (E : ℝ → ℝ) (θ : ℝ) (k : ℕ)
    (M : (Fin k → ℝ) → ℝ) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1,
        (∫ x, |dyadicB E θ s x| ^ k
          ∂dyadicProbabilityMeasure X) ≤ C) ∧
  Measurable M ∧
  ∀ s : Fin k → ℝ,
    (∀ i, s i ∈ Icc (0 : ℝ) 1) →
      Tendsto
        (fun X : ℝ => dyadicMixedMoment E θ X k s)
        atTop (𝓝 (M s))

/-- A mixed increment moment with one exponent for each factor. -/
def jointDyadicMixedMoment {k : ℕ} (E : ℝ → ℝ) (e : Fin k → ℝ)
    (X : ℝ) (s : Fin k → ℝ) : ℝ :=
  ∫ x, dyadicU X x ^ (∑ i, dyadicR (e i)) *
    ∏ i, dyadicB E (e i) (s i) x ∂dyadicProbabilityMeasure X

/-- Uniform absolute moments and joint mixed-moment limits on the unit cube. -/
def JointMomentInterface {k : ℕ} (E : ℝ → ℝ) (e : Fin k → ℝ)
    (M : (Fin k → ℝ) → ℝ) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℝ in atTop,
    ∀ i : Fin k, ∀ s ∈ Icc (0 : ℝ) 1,
      (∫ x, |dyadicB E (e i) s x| ^ k ∂dyadicProbabilityMeasure X) ≤ C) ∧
  ∀ s : Fin k → ℝ, (∀ i, s i ∈ Icc (0 : ℝ) 1) →
    Tendsto (fun X : ℝ => jointDyadicMixedMoment E e X s) atTop (𝓝 (M s))

/-- A mixed moment of two normalized profile responses. -/
def jointZMoment (E : ℝ → ℝ) (a b : ℝ) (g₁ g₂ : ℝ → ℝ)
    (p q : ℕ) (X : ℝ) : ℝ :=
  ∫ x, dyadicZ E a g₁ X x ^ p * dyadicZ E b g₂ X x ^ q
    ∂dyadicProbabilityMeasure X

/-- The sum of the three pairings of the Brownian covariance kernel. -/
def brownianW4 (s : Fin 4 → ℝ) : ℝ :=
  min (s 0) (s 1) * min (s 2) (s 3) +
  min (s 0) (s 2) * min (s 1) (s 3) +
  min (s 0) (s 3) * min (s 1) (s 2)

/-- The fourth-order macroscopic moment constant for logarithmic dyadic sampling. -/
def dyadicMomentConstant (θ : ℝ) : ℝ :=
  (2 ^ (2 * kappa θ) - 1) / (2 * kappa θ * Real.log 2)

/-- The normalized increment is jointly measurable in its profile parameter and position. -/
lemma dyadicB_measurable {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E) (θ : ℝ) :
    Measurable (fun p : ℝ × ℝ => dyadicB E θ p.1 p.2) := by
  exact ((WeightRemoval.increment_measurable hE θ).comp
    (measurable_snd.prodMk measurable_fst)).div
    ((measurable_snd.pow_const θ).mul measurable_snd.log).sqrt

end

end D5.S3.Arith.Robin.ForwardKernel.MomentTransferDefs
