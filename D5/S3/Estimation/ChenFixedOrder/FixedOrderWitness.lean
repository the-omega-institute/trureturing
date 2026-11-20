/- GID: D5/S3/Estimation/ChenFixedOrder/FixedOrderWitness
   generality: I
   mirror-B: D5/B/S3/Estimation/ChenFixedOrder/FixedOrderWitness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Fixed-order inclusion agreement permits distinct weak limits of a common estimator. -/

/-
admission_basis: open-problem-resolution (#32021; Proved)
External source: Jiahua Chen, Low-Order Inclusion Probabilities Do Not Determine
Asymptotic Normality, arXiv:2610.09168v1, Sections 1 and 6.
Preregistration: https://github.com/the-omega-institute/trureturing/issues/32021

fixedOrderWitness defines the shared sample spaces, event agreement, and two distinct limits.
fixedOrderWitness_holds
  proof_shape: content, expanding the same-delivery inclusion and limit arguments.
  escape_witness: tiltedSample_spec identifies both the real pushforward and exact
    stage-wise event agreement, using exists_inclusionPolynomial on the same samples.
  Live support: sampleSize_pos and populationMean_eq_zero give the growth and centering
    clauses. uniformSampleLaw_tendsto gives the common Gaussian baseline using
    map_eraseOrder_cond_uniform. continuous_density, density_bounds, integral_density
    and integral_eval_mul_density_sub_one supply the lift premises. continuous_tilted
    gives convergence of the lifted law and tilted_gaussian_separation distinguishes
    the limit from the baseline using gaussian_gram_posDef.
  Direct frozen dependencies: none.

Supporting escape audits:
https://github.com/the-omega-institute/trureturing/issues/32021#issuecomment-7029401222
-/

import D5.S3.Estimation.ChenFixedOrder.GaussianLimit
import D5.S3.Analytic.Probability.ChenDensityBridge
import D5.S3.Analytic.Probability.MomentPerturbation

/-! The fixed-order inclusion conjecture of Chen, arXiv:2610.09168v1, Sections 1 and 6. -/

open ChenFixedOrderSampling ChenDensityBridge MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace D5.S3.Estimation.ChenFixedOrder.FixedOrderWitness

open D5.S3.Analytic.Probability.MomentPerturbation

/-- Two designs on the same balanced populations and fixed-size sample spaces agree
on every inclusion event through any fixed positive order. The laws of their common
centered and scaled estimator converge weakly to different limits. -/
def fixedOrderWitness : Prop :=
  Tendsto sampleSize atTop atTop ∧
  Tendsto (fun m => Fintype.card (Population m)) atTop atTop ∧
  (∀ m, populationMean m = 0) ∧
  ∀ r : ℕ, 0 < r →
    ∃ (P Q : (m : ℕ) → ProbabilityMeasure (Sample m)) (ν : ProbabilityMeasure ℝ),
      (∀ m, (P m : Measure (Sample m)) = uniformOn Set.univ) ∧
      (∀ m (A : Finset (Population m)), A.card ≤ r →
        (P m : Measure (Sample m)) (inclusion m A) =
        (Q m : Measure (Sample m)) (inclusion m A)) ∧
      Tendsto (fun m => (P m).map (estimator m)) atTop (𝓝 standardGaussian) ∧
      Tendsto (fun m => (Q m).map (estimator m)) atTop (𝓝 ν) ∧
      ν ≠ standardGaussian

theorem fixedOrderWitness_holds : fixedOrderWitness := by
  have hSize : Tendsto sampleSize atTop atTop :=
    tendsto_atTop_mono (fun m : ℕ => by dsimp [sampleSize]; nlinarith) tendsto_id
  have hPopulation : Tendsto (fun m => Fintype.card (Population m)) atTop atTop := by
    refine tendsto_atTop_mono (fun m => ?_) hSize
    simp only [Population, Fintype.card_prod, Fintype.card_fin]
    have h := Nat.pow_le_pow_right (sampleSize_pos m) (show 1 ≤ 3 by decide)
    exact (by simpa only [pow_one] using h : sampleSize m ≤ stratumSize m).trans
      (by omega)
  refine ⟨hSize, hPopulation, populationMean_eq_zero, ?_⟩
  intro r _
  let R := max r 2
  let μ (m : ℕ) : ProbabilityMeasure ℝ := (uniformSampleMeasure m).map (estimator m)
  have hGaussian : GaussianLimit.standardGaussian = standardGaussian := rfl
  have hBaseline : Tendsto μ atTop (𝓝 standardGaussian) :=
    hGaussian ▸ GaussianLimit.uniformSampleLaw_tendsto
  have hNonneg (m : ℕ) (x : ℝ) : 0 ≤ density R (μ m) x :=
    (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (density_bounds R (μ m) x).1
  have hMeasurable (m : ℕ) : Measurable (density R (μ m)) :=
    (continuous_density R (μ m)).measurable
  have hMass (m : ℕ) : ∫ x, density R (μ m) x ∂uniformEstimatorLaw m = 1 :=
    integral_density R (μ m)
  let Q (m : ℕ) := tiltedSample m (density R (μ m)) (hMeasurable m) (hNonneg m) (hMass m)
  have hMoments (m i : ℕ) (_ : 0 < i) (hi : i ≤ r) :
      ∫ x, x ^ i * (density R (μ m) x - 1) ∂uniformEstimatorLaw m = 0 := by
    change ∫ x, x ^ i * (density R (μ m) x - 1) ∂(μ m : Measure ℝ) = 0
    simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
      integral_eval_mul_density_sub_one R (μ m) (Polynomial.X ^ i)
        ((Polynomial.natDegree_X_pow_le i).trans (hi.trans (le_max_left r 2)))
  have hSpec (m : ℕ) :=
    tiltedSample_spec m r (density R (μ m)) (hMeasurable m) (hNonneg m) (hMass m) (hMoments m)
  have hPush (m : ℕ) : (Q m).map (estimator m) = tilted R (μ m) :=
    ProbabilityMeasure.toMeasure_injective (hSpec m).1
  refine ⟨uniformSampleMeasure, Q, tilted R standardGaussian, fun _ => rfl, ?_,
    hBaseline, ?_, (tilted_gaussian_separation R).2⟩
  · intro m A hA
    exact ((hSpec m).2 A hA).symm
  · exact ((continuous_tilted R).continuousAt.tendsto.comp hBaseline).congr
      (fun m => (hPush m).symm)

end D5.S3.Estimation.ChenFixedOrder.FixedOrderWitness
