/- GID: D5/S3/Analytic/Probability/RandomExponentialProductSLLN
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/RandomExponentialProductSLLN
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bounded iid operator exponentials satisfy the strong law on every Banach space. -/

import D5.S3.Quantum.AURICOmega.ExponentialTail
import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Products of bounded iid operator exponentials and their deterministic Abel estimate. -/

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

namespace D5.S3.Analytic.Probability.RandomExponentialProductSLLN

/-- The factors are multiplied from left to right in increasing index order. -/
def randomProduct {𝕜 X Ω : Type} [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (a : ℕ → Ω → X →L[𝕜] X) (n : ℕ) (t : ℝ) (ω : Ω) :
    X →L[𝕜] X :=
  (List.ofFn fun i : Fin n => NormedSpace.exp (((t / n : ℝ) : 𝕜) • a i ω)).prod

/-- Almost sure convergence in the strong operator topology, uniformly on compact time intervals. -/
def claim : Prop :=
  ∀ (𝕜 X Ω : Type) [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [CompleteSpace X] [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
    letI := NormedAlgebra.restrictScalars ℝ 𝕜 (X →L[𝕜] X)
    letI : MeasurableSpace (X →L[𝕜] X) := borel (X →L[𝕜] X)
    ∀ (a : ℕ → Ω → X →L[𝕜] X),
      (∀ i, AEStronglyMeasurable (a i) μ) →
      Pairwise (fun i j => IndepFun (a i) (a j) μ) →
      (∀ i, IdentDistrib (a i) (a 0) μ μ) →
      ∀ (m : ℝ), (∀ i, ∀ᵐ ω ∂μ, ‖a i ω‖ ≤ m) →
      ∀ (x : X) (t : ℝ), 0 ≤ t → ∀ᵐ ω ∂μ,
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (0 : ℝ) t,
          ‖(randomProduct a n s ω -
            NormedSpace.exp (((s : ℝ) : 𝕜) • ∫ z, a 0 z ∂μ)) x‖ < ε

private def eulerProduct {e : Type*} [Ring e] [Module ℝ e]
    (a : ℕ → e) (h : ℝ) (n : ℕ) : e :=
  (List.ofFn fun i : Fin n => 1 + h • a i).prod

private def centeredSum {e : Type*} [AddCommGroup e] (a : ℕ → e) (b : e) (n : ℕ) : e :=
  ∑ i ∈ Finset.range n, (a i - b)

private lemma euler_abel_bound {e : Type*} [NormedRing e] [NormedAlgebra ℝ e]
    [NormOneClass e] (a : ℕ → e) (b : e) (m h r : ℝ) (n : ℕ)
    (hm : 0 ≤ m) (hh : 0 ≤ h) (hr : 0 ≤ r)
    (ha : ∀ i < n, ‖a i‖ ≤ m) (hb : ‖b‖ ≤ m)
    (hs : ∀ k ≤ n, ‖centeredSum a b k‖ ≤ r) :
    ‖eulerProduct a h n - (1 + h • b) ^ n‖ ≤
      h * Real.exp (h * m * n) * (1 + 2 * h * m * n) * r := by
  sorry

private lemma exponential_euler_bound {e : Type*} [NormedRing e] [NormedAlgebra ℝ e]
    [NormOneClass e] [CompleteSpace e] (a : ℕ → e) (m t : ℝ) (n : ℕ)
    (hm : 0 ≤ m) (ht : 0 ≤ t) (hn : 0 < n)
    (ha : ∀ i < n, ‖a i‖ ≤ m) (hsmall : t / n * m ≤ 1) :
    ‖(List.ofFn fun i : Fin n => NormedSpace.exp ((t / n) • a i)).prod -
      eulerProduct a (t / n) n‖ ≤
      (3 / 4 : ℝ) * m ^ 2 * t ^ 2 * Real.exp (m * t) / n := by
  sorry

private lemma centered_max_sublinear {e : Type*} [NormedAddCommGroup e]
    [NormedSpace ℝ e] (a : ℕ → e) (b : e)
    (hav : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, a i)
      atTop (𝓝 b)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ k ≤ n, ‖centeredSum a b k‖ ≤ ε * n := by
  sorry

private lemma deterministic_uniform {e : Type*} [NormedRing e] [NormedAlgebra ℝ e]
    [NormOneClass e] [CompleteSpace e] (a : ℕ → e) (b : e) (m : ℝ)
    (hm : 0 ≤ m) (ha : ∀ i, ‖a i‖ ≤ m) (hb : ‖b‖ ≤ m)
    (hav : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, a i)
      atTop (𝓝 b)) :
    ∀ t : ℝ, 0 ≤ t → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Set.Icc (0 : ℝ) t,
        ‖(List.ofFn fun i : Fin n => NormedSpace.exp ((s / n) • a i)).prod -
          NormedSpace.exp (s • b)‖ < ε := by
  have hab := euler_abel_bound a b m
  have hex := exponential_euler_bound a m
  have hmax := centered_max_sublinear a b hav
  sorry

private lemma operator_uniform_to_sot {𝕜 X Ω : Type} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a : ℕ → Ω → X →L[𝕜] X)
    (hsm : ∀ i, AEStronglyMeasurable (a i) μ)
    (hind : letI : MeasurableSpace (X →L[𝕜] X) := borel (X →L[𝕜] X)
      Pairwise (fun i j => IndepFun (a i) (a j) μ))
    (hid : letI : MeasurableSpace (X →L[𝕜] X) := borel (X →L[𝕜] X)
      ∀ i, IdentDistrib (a i) (a 0) μ μ)
    (m : ℝ) (ha : ∀ i, ∀ᵐ ω ∂μ, ‖a i ω‖ ≤ m) :
    letI := NormedAlgebra.restrictScalars ℝ 𝕜 (X →L[𝕜] X)
    ∀ (x : X) (t : ℝ), 0 ≤ t → ∀ᵐ ω ∂μ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (0 : ℝ) t,
        ‖(randomProduct a n s ω -
          NormedSpace.exp (((s : ℝ) : 𝕜) • ∫ z, a 0 z ∂μ)) x‖ < ε := by
  have hd := @deterministic_uniform.{0}
  sorry

theorem result : claim := by
  intro 𝕜 X Ω _ _ _ _ _ μ _
  letI := NormedAlgebra.restrictScalars ℝ 𝕜 (X →L[𝕜] X)
  letI : MeasurableSpace (X →L[𝕜] X) := borel (X →L[𝕜] X)
  intro a hsm hind hid m ha
  exact operator_uniform_to_sot μ a hsm hind hid m ha

end D5.S3.Analytic.Probability.RandomExponentialProductSLLN
