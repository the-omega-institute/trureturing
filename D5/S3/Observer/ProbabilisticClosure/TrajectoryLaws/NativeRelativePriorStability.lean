/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeRelativePriorStability
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeRelativePriorStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative priors control complete native conditional tails. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeObserverJointLaw
import Mathlib.Probability.ConditionalProbability

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeRelativePriorStability
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open NativeConditionalControl.DepthLaw NativeConditionalControl.Tail NativeObserverJointLaw
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction

private lemma real_comparison {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (E : Set X)
    (h : ENNReal.ofReal a * μ E ≤ ENNReal.ofReal b * ν E) :
    a * μ.real E ≤ b * ν.real E := by
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν E)) h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha,
    ENNReal.toReal_ofReal hb, measureReal_def] using ht

private lemma tv_of_mutual_comparison {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ζ : ℝ)
    (h : ∀ E, MeasurableSet E →
      (1 - ζ) * μ.real E ≤ (1 + ζ) * ν.real E ∧
      (1 - ζ) * ν.real E ≤ (1 + ζ) * μ.real E) :
    measurableTotalVariation μ ν ≤ ENNReal.ofReal ζ := by
  unfold measurableTotalVariation
  refine iSup_le fun E => ?_
  have he := h E.val E.property
  have hc := h E.valᶜ E.property.compl
  rw [measureReal_compl E.property, measureReal_compl E.property,
    probReal_univ, probReal_univ] at hc
  have hforward : μ.real E.val - ν.real E.val ≤ ζ := by nlinarith [he.1, hc.2]
  have hreverse : ν.real E.val - μ.real E.val ≤ ζ := by nlinarith [he.2, hc.1]
  apply max_le
  · rw [← ENNReal.ofReal_toReal (measure_ne_top μ E.val),
      ← ENNReal.ofReal_toReal (measure_ne_top ν E.val),
      ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal hforward
  · rw [← ENNReal.ofReal_toReal (measure_ne_top ν E.val),
      ← ENNReal.ofReal_toReal (measure_ne_top μ E.val),
      ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal hreverse

private lemma conditional_tv {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ζ : ℝ) (hζ : 0 ≤ ζ) (hζ1 : ζ < 1)
    (h : ∀ E, MeasurableSet E →
      ENNReal.ofReal (1 - ζ) * μ E ≤ ν E ∧ ν E ≤ ENNReal.ofReal (1 + ζ) * μ E)
    (S : Set X) (hS : MeasurableSet S) (hμS : μ S ≠ 0) :
    measurableTotalVariation (cond μ S) (cond ν S) ≤ ENNReal.ofReal ζ := by
  have hm : 0 < 1 - ζ := sub_pos.mpr hζ1
  have hM : 0 ≤ 1 + ζ := by linarith
  have hs := h S hS
  have hνS : ν S ≠ 0 := ne_of_gt (lt_of_lt_of_le
    (ENNReal.mul_pos (ne_of_gt (ENNReal.ofReal_pos.mpr hm)) hμS) hs.1)
  let := cond_isProbabilityMeasure hμS
  let := cond_isProbabilityMeasure hνS
  have hx : 0 < μ.real S := ENNReal.toReal_pos hμS (measure_ne_top μ S)
  have hy : 0 < ν.real S := ENNReal.toReal_pos hνS (measure_ne_top ν S)
  have hlo : (1 - ζ) * μ.real S ≤ ν.real S := by
    simpa using real_comparison μ ν (1 - ζ) 1 hm.le (by norm_num) S (by simpa using hs.1)
  have hup : ν.real S ≤ (1 + ζ) * μ.real S := by
    simpa using real_comparison ν μ 1 (1 + ζ) (by norm_num) hM S (by simpa using hs.2)
  apply tv_of_mutual_comparison _ _ ζ
  intro E hE
  have hi := h (S ∩ E) (hS.inter hE)
  have hli : (1 - ζ) * μ.real (S ∩ E) ≤ ν.real (S ∩ E) := by
    simpa using real_comparison μ ν (1 - ζ) 1 hm.le (by norm_num) (S ∩ E) (by simpa using hi.1)
  have hui : ν.real (S ∩ E) ≤ (1 + ζ) * μ.real (S ∩ E) := by
    simpa using real_comparison ν μ 1 (1 + ζ) (by norm_num) hM (S ∩ E) (by simpa using hi.2)
  have cond_real (ρ : Measure X) : (cond ρ S).real E = ρ.real (S ∩ E) / ρ.real S := by
    rw [measureReal_def, cond_apply' hE, ENNReal.toReal_mul, ENNReal.toReal_inv]
    simp only [measureReal_def, div_eq_mul_inv, mul_comm]
  simp only [cond_real μ, cond_real ν, ← mul_div_assoc]
  constructor
  · apply (div_le_div_iff₀ hx hy).mpr
    calc
      ((1 - ζ) * μ.real (S ∩ E)) * ν.real S ≤
          ((1 - ζ) * μ.real (S ∩ E)) * ((1 + ζ) * μ.real S) :=
        mul_le_mul_of_nonneg_left hup (mul_nonneg hm.le ENNReal.toReal_nonneg)
      _ = ((1 + ζ) * ((1 - ζ) * μ.real (S ∩ E))) * μ.real S := by ring
      _ ≤ ((1 + ζ) * ν.real (S ∩ E)) * μ.real S :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hli hM) hx.le
  · apply (div_le_div_iff₀ hy hx).mpr
    calc
      ((1 - ζ) * ν.real (S ∩ E)) * μ.real S ≤
          ((1 - ζ) * ((1 + ζ) * μ.real (S ∩ E))) * μ.real S :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hui hm.le) hx.le
      _ = ((1 + ζ) * μ.real (S ∩ E)) * ((1 - ζ) * μ.real S) := by ring
      _ ≤ ((1 + ζ) * μ.real (S ∩ E)) * ν.real S :=
        mul_le_mul_of_nonneg_left hlo (mul_nonneg hM ENNReal.toReal_nonneg)

private lemma native_joint_comparison (μ ν : PMF Depth) (ζ : ℝ)
    (h : ∀ k, ENNReal.ofReal (1 - ζ) * μ k ≤ ν k ∧
      ν k ≤ ENNReal.ofReal (1 + ζ) * μ k) (E : Set (Depth × Stream)) :
    ENNReal.ofReal (1 - ζ) * jointLaw μ E ≤ jointLaw ν E ∧
      jointLaw ν E ≤ ENNReal.ofReal (1 + ζ) * jointLaw μ E := by
  simp only [jointLaw, Measure.sum_apply_of_countable, Measure.smul_apply, smul_eq_mul]
  constructor
  · have ht := ENNReal.tsum_le_tsum fun k => mul_le_mul' (h k).1
      (le_refl (((rawReadLaw (rate k)).map (fun ω => (k, ω))) E))
    simpa only [mul_assoc, ENNReal.tsum_mul_left] using ht
  · have ht := ENNReal.tsum_le_tsum fun k => mul_le_mul' (h k).2
      (le_refl (((rawReadLaw (rate k)).map (fun ω => (k, ω))) E))
    simpa only [mul_assoc, ENNReal.tsum_mul_left] using ht

/-- Relative priors control the complete conditional tail at every legal finite history. -/
theorem native_relative_prior_tail (μ ν : PMF Depth) (ζ : ℝ)
    (hζ : 0 ≤ ζ) (hζ1 : ζ < 1)
    (hprior : ∀ k, ENNReal.ofReal (1 - ζ) * μ k ≤ ν k ∧
      ν k ≤ ENNReal.ofReal (1 + ζ) * μ k)
    (h : List Operation) (c : AcquiredNativeState) (hc : run h = some c) (s : ActivePhase) :
    measurableTotalVariation (rawTarget μ h c s) (rawTarget ν h c s) ≤
      ENNReal.ofReal (ζ / (1 - ζ)) := by
  have hμ : jointLaw μ (nativeEvent h c) ≠ 0 := by
    rw [history_mass μ h c hc]
    exact ne_of_gt (normalizer_bounds μ h c hc).1
  have hcond := conditional_tv (jointLaw μ) (jointLaw ν) ζ hζ hζ1
    (fun E _ => native_joint_comparison μ ν ζ hprior E) (nativeEvent h c)
    (event_measurable h c) hμ
  have hf : Measurable (fun t : Depth × Stream =>
      validStopped s (rawTail t.2 (readLetters h).length)) :=
    (validStopped_measurable s).comp (by unfold rawTail; fun_prop)
  calc
    _ ≤ measurableTotalVariation (cond (jointLaw μ) (nativeEvent h c))
        (cond (jointLaw ν) (nativeEvent h c)) :=
      measurable_total_variation_map_le _ _ _ hf
    _ ≤ ENNReal.ofReal ζ := hcond
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      apply (le_div_iff₀ (sub_pos.mpr hζ1)).mpr
      nlinarith [sq_nonneg ζ])

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeRelativePriorStability
