/- GID: D5/S3/Zeros/Endpoints/BernoulliBridgeVariance
   generality: G
   mirror-B: D5/B/S3/Zeros/Endpoints/BernoulliBridgeVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compute the Bernoulli bridge variance and its unique midpoint maximum. -/

import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Moments.Variance

namespace D5.S3.Zeros.Endpoints.BernoulliBridgeVariance

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

/-- The identity observable on the Bernoulli bridge has variance `t * (1 - t)`. -/
theorem bernoulli_bridge_variance (t : Set.Icc (0 : ℝ) 1) :
    Var[id; Ber((1 : ℝ), 0, t)] = (t : ℝ) * (1 - t) := by
  rw [variance_eq_integral (μ := Ber((1 : ℝ), 0, t)) measurable_id.aemeasurable]
  have hmean : ∫ x, id x ∂Ber((1 : ℝ), 0, t) = (t : ℝ) := by
    rw [integral_bernoulliMeasure]
    simp
  rw [hmean, integral_bernoulliMeasure]
  simp
  ring

/-- The bridge variance vanishes at both endpoints and is one quarter at the midpoint. -/
theorem bernoulli_bridge_variance_endpoints_and_midpoint :
    Var[id; Ber((1 : ℝ), 0,
        (⟨0, by constructor <;> norm_num⟩ : Set.Icc (0 : ℝ) 1))] = 0 ∧
      Var[id; Ber((1 : ℝ), 0,
        (⟨1, by constructor <;> norm_num⟩ : Set.Icc (0 : ℝ) 1))] = 0 ∧
      Var[id; Ber((1 : ℝ), 0,
        (⟨1 / 2, by constructor <;> norm_num⟩ : Set.Icc (0 : ℝ) 1))] = 1 / 4 := by
  rw [bernoulli_bridge_variance, bernoulli_bridge_variance,
    bernoulli_bridge_variance]
  norm_num

/-- The bridge variance never exceeds one quarter. -/
theorem bernoulli_bridge_variance_le_quarter (t : Set.Icc (0 : ℝ) 1) :
    Var[id; Ber((1 : ℝ), 0, t)] ≤ 1 / 4 := by
  rw [bernoulli_bridge_variance]
  nlinarith [sq_nonneg ((t : ℝ) - 1 / 2)]

/-- The bridge variance reaches one quarter only at the midpoint. -/
theorem bernoulli_bridge_variance_eq_quarter_iff (t : Set.Icc (0 : ℝ) 1) :
    Var[id; Ber((1 : ℝ), 0, t)] = 1 / 4 ↔ (t : ℝ) = 1 / 2 := by
  rw [bernoulli_bridge_variance]
  constructor
  · intro h
    nlinarith [sq_nonneg ((t : ℝ) - 1 / 2)]
  · intro h
    rw [h]
    norm_num

end D5.S3.Zeros.Endpoints.BernoulliBridgeVariance
