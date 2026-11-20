/- GID: D5/S3/Analytic/Probability/ChenDensityBridge
   generality: I
   mirror-B: D5/B/S3/Analytic/Probability/ChenDensityBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real density tilts on fixed-size samples preserve inclusion events up to the matched moment order. -/

import D5.S3.Analytic.Probability.ChenFixedOrderSampling
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace ChenDensityBridge

open ChenFixedOrderSampling MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The law of the common estimator under uniform sampling on `Sample m`. -/
noncomputable def uniformEstimatorLaw (m : ℕ) : Measure ℝ :=
  Measure.map (estimator m) (uniformOn (Set.univ : Set (Sample m)))

private theorem integral_uniformEstimatorLaw (m : ℕ) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ x, f x ∂uniformEstimatorLaw m) =
      ∫ S : Sample m, f (estimator m S) ∂(uniformOn (Set.univ : Set (Sample m))) :=
  integral_map (measurable_of_finite (estimator m)).aemeasurable hf.aestronglyMeasurable

private theorem integrable_sample {m : ℕ} {μ : Measure (Sample m)} [IsFiniteMeasure μ]
    (f : Sample m → ℝ) : Integrable f μ :=
  integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)

/-- Lift a normalized real density by evaluating it at the estimator of each sample. -/
noncomputable def tiltedSample (m : ℕ) (g : ℝ → ℝ) (hg : Measurable g)
    (hg_nonneg : ∀ x, 0 ≤ g x) (h_mass : ∫ x, g x ∂uniformEstimatorLaw m = 1) :
    ProbabilityMeasure (Sample m) := by
  let P := uniformOn (Set.univ : Set (Sample m))
  refine ⟨P.withDensity (fun S => ENNReal.ofReal (g (estimator m S))), ⟨?_⟩⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_sample (fun S => g (estimator m S)))
      (Filter.Eventually.of_forall fun S => hg_nonneg (estimator m S)),
    ← integral_uniformEstimatorLaw m hg, h_mass, ENNReal.ofReal_one]

private theorem restricted_perturbation_eq_zero (m r : ℕ) {g : ℝ → ℝ} (hg : Measurable g)
    (h_mass : ∫ x, g x ∂uniformEstimatorLaw m = 1)
    (h_moments : ∀ i : ℕ, 0 < i → i ≤ r →
      ∫ x, x ^ i * (g x - 1) ∂uniformEstimatorLaw m = 0)
    (A : Finset (Population m)) (hA : A.card ≤ r) :
    (∫ S in inclusion m A, (g (estimator m S) - 1)
      ∂(uniformOn (Set.univ : Set (Sample m)))) = 0 := by
  let P := uniformOn (Set.univ : Set (Sample m))
  let f : ℝ → ℝ := fun x => g x - 1
  obtain ⟨p, hp, h_inclusion⟩ := exists_inclusionPolynomial m A
  have h_monomial (i : ℕ) (hi : i ≤ r) :
      (∫ S : Sample m, estimator m S ^ i * f (estimator m S) ∂P) = 0 := by
    cases i with
    | zero =>
        simp only [pow_zero, one_mul]
        change (∫ S : Sample m, g (estimator m S) - 1 ∂P) = 0
        rw [integral_sub (integrable_sample (fun S => g (estimator m S))) (integrable_const 1),
          ← integral_uniformEstimatorLaw m hg, h_mass]
        simp [P]
    | succ i =>
        have h : Measurable (fun x : ℝ => x ^ (i + 1) * f x) :=
          (measurable_id.pow_const _).mul (hg.sub measurable_const)
        rw [← integral_uniformEstimatorLaw m h]
        exact h_moments (i + 1) (Nat.succ_pos _) hi
  rw [h_inclusion f]
  change (∫ S : Sample m, p.eval (estimator m S) * f (estimator m S) ∂P) = 0
  simp_rw [Polynomial.eval_eq_sum_range, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ fun i _ =>
    integrable_sample (fun S => p.coeff i * (estimator m S ^ i * f (estimator m S)))]
  apply Finset.sum_eq_zero
  intro i hi
  rw [integral_const_mul, h_monomial i ?_, mul_zero]
  exact (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans (hp.trans hA)

/-- The lifted law pushes forward to the real tilt and exactly preserves inclusion probabilities
through order `r` when the centered density is orthogonal to those powers. -/
theorem tiltedSample_spec (m r : ℕ) (g : ℝ → ℝ) (hg : Measurable g)
    (hg_nonneg : ∀ x, 0 ≤ g x) (h_mass : ∫ x, g x ∂uniformEstimatorLaw m = 1)
    (h_moments : ∀ i : ℕ, 0 < i → i ≤ r →
      ∫ x, x ^ i * (g x - 1) ∂uniformEstimatorLaw m = 0) :
    (((tiltedSample m g hg hg_nonneg h_mass).map (estimator m) : Measure ℝ) =
      (uniformEstimatorLaw m).withDensity (fun x => ENNReal.ofReal (g x))) ∧
    (∀ A : Finset (Population m), A.card ≤ r →
      (tiltedSample m g hg hg_nonneg h_mass : Measure (Sample m)) (inclusion m A) =
        uniformOn (Set.univ : Set (Sample m)) (inclusion m A)) := by
  constructor
  · have h_est := measurable_of_finite (estimator m)
    ext B hB
    rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply h_est hB]
    change (uniformOn (Set.univ : Set (Sample m))).withDensity
        (fun S => ENNReal.ofReal (g (estimator m S))) (estimator m ⁻¹' B) =
      (uniformEstimatorLaw m).withDensity (fun x => ENNReal.ofReal (g x)) B
    rw [withDensity_apply _ (h_est hB), withDensity_apply _ hB, uniformEstimatorLaw,
      setLIntegral_map hB hg.ennreal_ofReal h_est]
  · intro A hA
    let P := uniformOn (Set.univ : Set (Sample m))
    let E := inclusion m A
    have hE : MeasurableSet E := E.toFinite.measurableSet
    have h_zero := restricted_perturbation_eq_zero m r hg h_mass h_moments A hA
    change (∫ S, g (estimator m S) - 1 ∂P.restrict E) = 0 at h_zero
    rw [integral_sub (integrable_sample (fun S => g (estimator m S))) (integrable_const 1),
      sub_eq_zero, setIntegral_const, smul_eq_mul, mul_one] at h_zero
    change P.withDensity (fun S => ENNReal.ofReal (g (estimator m S))) E = P E
    rw [withDensity_apply _ hE, ← ofReal_integral_eq_lintegral_ofReal
      (integrable_sample (fun S => g (estimator m S)))
      (Filter.Eventually.of_forall fun S => hg_nonneg (estimator m S)),
      h_zero, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P E)]

end ChenDensityBridge
