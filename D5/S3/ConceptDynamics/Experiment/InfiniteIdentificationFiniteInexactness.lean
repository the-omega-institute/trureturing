/- GID: D5/S3/ConceptDynamics/Experiment/InfiniteIdentificationFiniteInexactness
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/InfiniteIdentificationFiniteInexactness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equivalent coordinates allow infinite separation without finite exact tomography. -/

import D5.S0.Asymptotics.MetricGeometry.VaryingMarginalGreenClassMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw

/- Library-search audit trail (2026-08-24):
   * Exact pinned-Mathlib hits `ProbabilityTheory.strong_law_ae` and
     `ProbabilityTheory.iIndepFun_infinitePi` prove the empirical-mean limits
     for independent coordinate observations.
   * Exact pinned-Mathlib hits `ProbabilityTheory.map_bernoulliMeasure`,
     `ProbabilityTheory.integral_bernoulliMeasure`, and
     `MeasureTheory.measurableSet_tendsto` identify the common coordinate law,
     its mean, and the measurable classifier event.
   * Exact repository hit
     `varying_greenClass_measure_pos_iff` proves that the shared all-false
     finite cylinder has positive mass under both product laws.
   * Repository searches for almost-sure identification, finite exact
     tomography, and this inexact converse found no exact declaration.
     External `loogle` and `leansearch` executables are absent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Experiment.InfiniteIdentificationFiniteInexactness

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology

noncomputable section

open D5.S0.Naming.GreenClassMeasure
open D5.S0.Asymptotics.MetricGeometry.VaryingMarginalGreenClassMeasure

/-- The lower state has success probability one third at every coordinate. -/
def lowerBias : unitInterval := ⟨1 / 3, by norm_num, by norm_num⟩

/-- The upper state has success probability two thirds at every coordinate. -/
def upperBias : unitInterval := ⟨2 / 3, by norm_num, by norm_num⟩

/-- A nondegenerate Boolean coordinate law with success probability `p`. -/
def marginal (p : unitInterval) : Measure Bool :=
  bernoulliMeasure true false p

instance marginal_isProbabilityMeasure (p : unitInterval) :
    IsProbabilityMeasure (marginal p) := by
  unfold marginal
  infer_instance

/-- The independent countable transcript law with constant coordinate bias `p`. -/
def productLaw (p : unitInterval) : Measure (Nat -> Bool) :=
  Measure.infinitePi (fun _ : Nat => marginal p)

instance productLaw_isProbabilityMeasure (p : unitInterval) :
    IsProbabilityMeasure (productLaw p) := by
  unfold productLaw
  infer_instance

/-- The two states select the lower- and upper-bias product laws. -/
def stateLaw : Bool -> Measure (Nat -> Bool)
  | false => productLaw lowerBias
  | true => productLaw upperBias

instance stateLaw_isProbabilityMeasure (state : Bool) :
    IsProbabilityMeasure (stateLaw state) := by
  cases state <;> simp only [stateLaw, productLaw]
  all_goals infer_instance

/-- Coordinate `n`, embedded in the reals for empirical averaging. -/
def coordinateReadout (n : Nat) (transcript : Nat -> Bool) : Real :=
  if transcript n then 1 else 0

/-- The normalized sum of the first `n` coordinate readouts. -/
def empiricalMean (n : Nat) (transcript : Nat -> Bool) : Real :=
  (n : Real)⁻¹ • ∑ i ∈ Finset.range n, coordinateReadout i transcript

/-- The event that empirical means converge to the upper-state bias. -/
def distinguishingEvent : Set (Nat -> Bool) :=
  {transcript | Tendsto (fun n => empiricalMean n transcript) atTop (𝓝 (upperBias : Real))}

/-- The transcript visible after the first `m` coordinates. -/
def finiteTranscript (m : Nat) (transcript : Nat -> Bool) : Fin m -> Bool :=
  fun i => transcript i

private theorem coordinateReadout_measurable (n : Nat) :
    Measurable (coordinateReadout n) := by
  change Measurable ((fun b : Bool => if b then (1 : Real) else 0) ∘
    fun transcript : Nat -> Bool => transcript n)
  exact Measurable.of_discrete.comp (measurable_pi_apply n)

private theorem empiricalMean_measurable (n : Nat) : Measurable (empiricalMean n) := by
  unfold empiricalMean
  exact (Finset.measurable_sum (Finset.range n)
    (fun i _ => coordinateReadout_measurable i)).const_smul (n : Real)⁻¹

private theorem coordinateReadout_hasLaw (p : unitInterval) (n : Nat) :
    HasLaw (coordinateReadout n) (bernoulliMeasure (1 : Real) 0 p) (productLaw p) := by
  refine ⟨(coordinateReadout_measurable n).aemeasurable, ?_⟩
  rw [productLaw]
  change Measure.map ((fun b : Bool => if b then (1 : Real) else 0) ∘
      fun transcript : Nat -> Bool => transcript n)
      (Measure.infinitePi (fun _ : Nat => marginal p)) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [Measure.infinitePi_map_eval (fun _ : Nat => marginal p) n]
  · unfold marginal
    simpa using map_bernoulliMeasure true false
      (fun b : Bool => if b then (1 : Real) else 0) p

private theorem coordinateReadout_identDistrib (p : unitInterval) (n : Nat) :
    IdentDistrib (coordinateReadout n) (coordinateReadout 0) (productLaw p) (productLaw p) :=
  (coordinateReadout_hasLaw p n).identDistrib (coordinateReadout_hasLaw p 0)

private theorem coordinateReadout_integrable (p : unitInterval) :
    Integrable (coordinateReadout 0) (productLaw p) := by
  have hident := (coordinateReadout_hasLaw p 0).identDistrib
    (HasLaw.id (μ := bernoulliMeasure (1 : Real) 0 p))
  exact hident.integrable_iff.mpr
    (integrable_bernoulliMeasure (1 : Real) 0 p id)

private theorem coordinateReadout_integral (p : unitInterval) :
    ∫ transcript, coordinateReadout 0 transcript ∂productLaw p = (p : Real) := by
  have hident := (coordinateReadout_hasLaw p 0).identDistrib
    (HasLaw.id (μ := bernoulliMeasure (1 : Real) 0 p))
  rw [hident.integral_eq, integral_bernoulliMeasure]
  simp

private theorem empiricalMean_tendsto_ae (p : unitInterval) :
    ∀ᵐ transcript ∂productLaw p,
      Tendsto (fun n => empiricalMean n transcript) atTop (𝓝 (p : Real)) := by
  have hIndependent : iIndepFun coordinateReadout (productLaw p) := by
    change iIndepFun (fun i transcript =>
      if transcript i = true then (1 : Real) else 0)
      (Measure.infinitePi (fun _ : Nat => marginal p))
    exact iIndepFun_infinitePi
      (P := fun _ : Nat => marginal p)
      (X := fun _ : Nat => fun b : Bool => if b = true then (1 : Real) else 0)
      (fun _ => Measurable.of_discrete)
  have hStrong := strong_law_ae coordinateReadout (coordinateReadout_integrable p)
    (fun _ _ hne => hIndependent.indepFun hne)
    (coordinateReadout_identDistrib p)
  simpa only [empiricalMean, coordinateReadout_integral] using hStrong

private theorem toNNReal_ne_zero_of_pos (p : unitInterval) (hp : 0 < (p : Real)) :
    (unitInterval.toNNReal p : ENNReal) ≠ 0 := by
  rw [ENNReal.coe_ne_zero]
  intro hzero
  have hval := congrArg ((↑) : NNReal -> Real) hzero
  change (p : Real) = 0 at hval
  exact hp.ne' hval

private theorem toNNReal_symm_ne_zero_of_lt_one (p : unitInterval) (hp : (p : Real) < 1) :
    (unitInterval.toNNReal (unitInterval.symm p) : ENNReal) ≠ 0 := by
  rw [ENNReal.coe_ne_zero]
  intro hzero
  have hval := congrArg ((↑) : NNReal -> Real) hzero
  change 1 - (p : Real) = 0 at hval
  linarith

private theorem lower_marginal_absolutelyContinuous_upper :
    marginal lowerBias ≪ marginal upperBias := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hzero => ?_
  classical
  by_cases ht : true ∈ s
  · by_cases hf : false ∈ s
    · exfalso
      simpa [marginal, bernoulliMeasure_apply, hs, ht, hf] using hzero
    · exfalso
      apply toNNReal_ne_zero_of_pos upperBias (by norm_num [upperBias])
      simpa [marginal, bernoulliMeasure_apply, hs, ht, hf] using hzero
  · by_cases hf : false ∈ s
    · exfalso
      apply toNNReal_symm_ne_zero_of_lt_one upperBias (by norm_num [upperBias])
      simpa [marginal, bernoulliMeasure_apply, hs, ht, hf] using hzero
    · have hempty : s = ∅ := by
        ext b
        cases b <;> simp_all
      simp [hempty]

private theorem upper_marginal_absolutelyContinuous_lower :
    marginal upperBias ≪ marginal lowerBias := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hzero => ?_
  classical
  by_cases ht : true ∈ s
  · by_cases hf : false ∈ s
    · exfalso
      simpa [marginal, bernoulliMeasure_apply, hs, ht, hf] using hzero
    · exfalso
      apply toNNReal_ne_zero_of_pos lowerBias (by norm_num [lowerBias])
      simpa [marginal, bernoulliMeasure_apply, hs, ht, hf] using hzero
  · by_cases hf : false ∈ s
    · exfalso
      apply toNNReal_symm_ne_zero_of_lt_one lowerBias (by norm_num [lowerBias])
      simpa [marginal, bernoulliMeasure_apply, hs, ht, hf] using hzero
    · have hempty : s = ∅ := by
        ext b
        cases b <;> simp_all
      simp [hempty]

private theorem distinguishingEvent_measurable : MeasurableSet distinguishingEvent := by
  exact measurableSet_tendsto (𝓝 (upperBias : Real)) empiricalMean_measurable

private theorem lower_state_event_probability : stateLaw false distinguishingEvent = 0 := by
  rw [← compl_mem_ae_iff]
  have hlower : ∀ᵐ transcript ∂stateLaw false,
      Tendsto (fun n => empiricalMean n transcript) atTop (𝓝 (lowerBias : Real)) := by
    simpa only [stateLaw] using empiricalMean_tendsto_ae lowerBias
  filter_upwards [hlower] with transcript hLower
  intro hUpper
  change Tendsto (fun n => empiricalMean n transcript) atTop
    (𝓝 (upperBias : Real)) at hUpper
  have heq : (lowerBias : Real) = (upperBias : Real) :=
    tendsto_nhds_unique hLower hUpper
  norm_num [lowerBias, upperBias] at heq

private theorem upper_state_event_probability : stateLaw true distinguishingEvent = 1 := by
  rw [← mem_ae_iff_prob_eq_one distinguishingEvent_measurable]
  change ∀ᵐ transcript ∂productLaw upperBias,
    Tendsto (fun n => empiricalMean n transcript) atTop (𝓝 (upperBias : Real))
  exact empiricalMean_tendsto_ae upperBias

private theorem lower_allFalseCylinder_pos (m : Nat) :
    0 < stateLaw false (greenClass (Finset.range m) (fun _ => false)) := by
  rw [stateLaw, productLaw]
  refine (varying_greenClass_measure_pos_iff
    (fun _ : Nat => marginal lowerBias) (Finset.range m) (fun _ => false)).2 ?_
  intro _i _hi
  rw [marginal, bernoulliMeasure_apply_of_notMem_of_mem lowerBias
    (measurableSet_singleton false) (by decide) (by decide)]
  rw [ENNReal.coe_pos, ← NNReal.coe_pos]
  change 0 < 1 - (lowerBias : Real)
  norm_num [lowerBias]

private theorem upper_allFalseCylinder_pos (m : Nat) :
    0 < stateLaw true (greenClass (Finset.range m) (fun _ => false)) := by
  rw [stateLaw, productLaw]
  refine (varying_greenClass_measure_pos_iff
    (fun _ : Nat => marginal upperBias) (Finset.range m) (fun _ => false)).2 ?_
  intro _i _hi
  rw [marginal, bernoulliMeasure_apply_of_notMem_of_mem upperBias
    (measurableSet_singleton false) (by decide) (by decide)]
  rw [ENNReal.coe_pos, ← NNReal.coe_pos]
  change 0 < 1 - (upperBias : Real)
  norm_num [upperBias]

private theorem finiteTranscript_eq_allFalse {m : Nat} {transcript : Nat -> Bool}
    (htranscript : transcript ∈ greenClass (Finset.range m) (fun _ => false)) :
    finiteTranscript m transcript = fun _ => false := by
  funext i
  exact htranscript i (Finset.mem_range.2 i.isLt)

private theorem no_finite_exact_decoder :
    ¬ ∃ (m : Nat) (decode : (Fin m -> Bool) -> Bool),
      (∀ᵐ transcript ∂stateLaw false,
        decode (finiteTranscript m transcript) = false) ∧
      (∀ᵐ transcript ∂stateLaw true,
        decode (finiteTranscript m transcript) = true) := by
  rintro ⟨m, decode, falseExact, trueExact⟩
  let allFalse : Fin m -> Bool := fun _ => false
  have decodeFalse : decode allFalse = false := by
    by_contra hdecode
    have hnull : stateLaw false
        {transcript | decode (finiteTranscript m transcript) ≠ false} = 0 := by
      rw [← compl_mem_ae_iff]
      filter_upwards [falseExact] with transcript htranscript
      simpa using htranscript
    have hsubset : greenClass (Finset.range m) (fun _ => false) ⊆
        {transcript | decode (finiteTranscript m transcript) ≠ false} := by
      intro transcript htranscript
      change decode (finiteTranscript m transcript) ≠ false
      rw [finiteTranscript_eq_allFalse htranscript]
      exact hdecode
    exact (lower_allFalseCylinder_pos m).ne'
      (measure_mono_null hsubset hnull)
  have decodeTrue : decode allFalse = true := by
    by_contra hdecode
    have hnull : stateLaw true
        {transcript | decode (finiteTranscript m transcript) ≠ true} = 0 := by
      rw [← compl_mem_ae_iff]
      filter_upwards [trueExact] with transcript htranscript
      simpa using htranscript
    have hsubset : greenClass (Finset.range m) (fun _ => false) ⊆
        {transcript | decode (finiteTranscript m transcript) ≠ true} := by
      intro transcript htranscript
      change decode (finiteTranscript m transcript) ≠ true
      rw [finiteTranscript_eq_allFalse htranscript]
      exact hdecode
    exact (upper_allFalseCylinder_pos m).ne'
      (measure_mono_null hsubset hnull)
  rw [decodeFalse] at decodeTrue
  contradiction

/-- Independent product laws with mutually absolutely continuous coordinates
can be separated almost surely by the complete transcript, while no finite
prefix admits an almost-surely exact decoder for both states. -/
theorem infinite_identification_not_finite_exact_tomography :
    marginal lowerBias ≪ marginal upperBias ∧
    marginal upperBias ≪ marginal lowerBias ∧
    MeasurableSet distinguishingEvent ∧
    stateLaw false distinguishingEvent = 0 ∧
    stateLaw true distinguishingEvent = 1 ∧
    ¬ ∃ (m : Nat) (decode : (Fin m -> Bool) -> Bool),
      (∀ᵐ transcript ∂stateLaw false,
        decode (finiteTranscript m transcript) = false) ∧
      (∀ᵐ transcript ∂stateLaw true,
        decode (finiteTranscript m transcript) = true) := by
  exact ⟨lower_marginal_absolutelyContinuous_upper,
    upper_marginal_absolutelyContinuous_lower,
    distinguishingEvent_measurable,
    lower_state_event_probability,
    upper_state_event_probability,
    no_finite_exact_decoder⟩

#print axioms infinite_identification_not_finite_exact_tomography

end

end D5.S3.ConceptDynamics.Experiment.InfiniteIdentificationFiniteInexactness
