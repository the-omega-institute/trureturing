/- GID: D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent seeded Bernoulli prefix laws and stopped moment transfer. -/

import D5.S3.Estimation.SequentialDecisionRisk.StoppedLikelihoodAbsorption
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Estimation.SequentialDecisionRisk.SeededBernoulliStoppedMoment

variable {Seed : Type*} [MeasurableSpace Seed]

local notation "Ber" => fun p : unitInterval => bernoulliMeasure true false p
local notation "Law" => fun (ν : Measure Seed) (p : unitInterval) =>
  ν.prod (Measure.infinitePi (fun _ : ℕ => Ber p))
local notation "Past" => fun (n : ℕ) (ω : Seed × (ℕ → Bool)) =>
  (ω.1, (range n).restrict ω.2)
local notation "Ratio" => fun (p₀ p : unitInterval) (b : Bool) =>
  if b then (p : ℝ) / (p₀ : ℝ) else (1 - (p : ℝ)) / (1 - (p₀ : ℝ))
local notation "Like" => fun (p₀ p : unitInterval) (n : ℕ) (ω : Seed × (ℕ → Bool)) =>
  ∏ i ∈ range n, Ratio p₀ p (ω.2 i)

/-- The private seed is visible initially; the first `n` acquired source bits
are visible at time `n`. -/
def seededFiltration : Filtration ℕ (inferInstance : MeasurableSpace (Seed × (ℕ → Bool))) where
  seq n := MeasurableSpace.comap (Past n) inferInstance
  mono' i j hij := by
    apply MeasurableSpace.comap_le_comap_of_eq_comp
      (h := fun z : Seed × ((k : range j) → Bool) =>
        (z.1, fun k : range i => z.2 ⟨k.1, mem_range.mpr ((mem_range.mp k.2).trans_le hij)⟩))
    · fun_prop
    · rfl
  le' n := (by fun_prop : Measurable (Past n)).comap_le

private lemma ratio_nonneg (p₀ p : unitInterval) (b : Bool) : 0 ≤ Ratio p₀ p b := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact div_nonneg (sub_nonneg.mpr p.2.2) (sub_nonneg.mpr p₀.2.2)
  · exact div_nonneg p.2.1 p₀.2.1

private lemma ratio_mass (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ))
    (h₁ : (p₀ : ℝ) < 1) (b : Bool) :
    ENNReal.ofReal (Ratio p₀ p b) * Ber p₀ {b} = Ber p {b} := by
  cases b <;> simp [bernoulliMeasure_apply, ENNReal.ofReal_div_of_pos,
    h₀, sub_pos.mpr h₁, unitInterval.toNNReal, unitInterval.symm]

private lemma finite_prefix_density (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ))
    (h₁ : (p₀ : ℝ) < 1) (n : ℕ) :
    (Measure.pi (fun _ : range n => Ber p₀)).withDensity
      (fun x => ENNReal.ofReal (∏ i : range n, Ratio p₀ p (x i))) =
    Measure.pi (fun _ : range n => Ber p) := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.withDensity_apply _ (measurableSet_singleton x), lintegral_singleton,
    Measure.pi_singleton, Measure.pi_singleton,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => ratio_nonneg p₀ p (x i)),
    ← prod_mul_distrib]
  exact prod_congr rfl (fun i _ => ratio_mass p₀ p h₀ h₁ (x i))

end D5.S3.Estimation.SequentialDecisionRisk.SeededBernoulliStoppedMoment
