/- GID: D5/S3/Estimation/SequentialDecisionRisk/MeasurableDeficiencyTriangle
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/MeasurableDeficiencyTriangle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One-way measurable experiment deficiency satisfies the triangle inequality. -/

import D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Probability.Kernel.Composition.MeasureComp

/- Library-search audit trail (2026-08-28):
   * `FiniteDeficiencyTriangle` proves only the finite stochastic-matrix case and
     is not an exact hit for arbitrary measurable experiments.
   * Repository name and body-shape searches found no arbitrary-carrier
     experiment-deficiency primitive. The imported `measurableTotalVariation`
     is the canonical arbitrary-law distance and is reused here.
   * Pinned Mathlib supplies kernel and measure composition, Markov composition
     instances, the layer-cake formula, and complete-lattice infimum laws. It
     has no packaged measurable total-variation contraction theorem, so that
     bridge is proved locally from measurable-event total variation. -/

noncomputable section

open scoped ENNReal ProbabilityTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.SequentialDecisionRisk.MeasurableDeficiencyTriangle

open Filter MeasureTheory ProbabilityTheory Set
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction

/-- Uniform total-variation error of one Markov simulator between two
measurable statistical experiments. -/
def measurableSimulationError
    {State SourceObservation TargetObservation : Type*}
    [MeasurableSpace State] [MeasurableSpace SourceObservation]
    [MeasurableSpace TargetObservation]
    (target : Kernel State TargetObservation)
    (source : Kernel State SourceObservation)
    (simulator : Kernel SourceObservation TargetObservation) : ENNReal :=
  ⨆ state, measurableTotalVariation
    (target state) ((simulator ∘ₖ source) state)

/-- One-way deficiency is the infimum of uniform simulation error over all
Markov kernels between the observation carriers. -/
def measurableDeficiency
    {State SourceObservation TargetObservation : Type*}
    [MeasurableSpace State] [MeasurableSpace SourceObservation]
    [MeasurableSpace TargetObservation]
    (target : Kernel State TargetObservation)
    (source : Kernel State SourceObservation) : ENNReal :=
  ⨅ simulator :
      {K : Kernel SourceObservation TargetObservation // IsMarkovKernel K},
    measurableSimulationError target source simulator.1

private theorem measurable_total_variation_triangle
    {A : Type*} [MeasurableSpace A] (mu nu rho : Measure A) :
    measurableTotalVariation mu rho <=
      measurableTotalVariation mu nu + measurableTotalVariation nu rho := by
  unfold measurableTotalVariation
  refine iSup_le fun event => ?_
  have hmunu :
      max (mu event.1 - nu event.1) (nu event.1 - mu event.1) <=
        ⨆ candidate : {event : Set A // MeasurableSet event},
          max (mu candidate.1 - nu candidate.1)
            (nu candidate.1 - mu candidate.1) :=
    le_iSup (fun candidate : {event : Set A // MeasurableSet event} =>
      max (mu candidate.1 - nu candidate.1)
        (nu candidate.1 - mu candidate.1)) event
  have hnurho :
      max (nu event.1 - rho event.1) (rho event.1 - nu event.1) <=
        ⨆ candidate : {event : Set A // MeasurableSet event},
          max (nu candidate.1 - rho candidate.1)
            (rho candidate.1 - nu candidate.1) :=
    le_iSup (fun candidate : {event : Set A // MeasurableSet event} =>
      max (nu candidate.1 - rho candidate.1)
        (rho candidate.1 - nu candidate.1)) event
  apply max_le
  · exact tsub_le_tsub_add_tsub.trans <| add_le_add
      (le_max_left _ _ |>.trans hmunu) (le_max_left _ _ |>.trans hnurho)
  · calc
      rho event.1 - mu event.1 <=
          (rho event.1 - nu event.1) + (nu event.1 - mu event.1) :=
        tsub_le_tsub_add_tsub
      _ <= (⨆ candidate : {event : Set A // MeasurableSet event},
              max (nu candidate.1 - rho candidate.1)
                (rho candidate.1 - nu candidate.1)) +
            ⨆ candidate : {event : Set A // MeasurableSet event},
              max (mu candidate.1 - nu candidate.1)
                (nu candidate.1 - mu candidate.1) := add_le_add
        (le_max_right _ _ |>.trans hnurho) (le_max_right _ _ |>.trans hmunu)
      _ = _ := add_comm _ _

private theorem lintegral_tsub_le_measurable_total_variation
    {A : Type*} [MeasurableSpace A]
    (mu nu : Measure A) (f : A -> ENNReal)
    (hf : Measurable f) (hf_one : ∀ x, f x <= 1) :
    (∫⁻ x, f x ∂mu) - (∫⁻ x, f x ∂nu) <=
      measurableTotalVariation mu nu := by
  let g : A -> Real := fun x => (f x).toReal
  have hg : Measurable g := ENNReal.measurable_toReal.comp hf
  have hg_nonnegative : 0 <= g := fun x => ENNReal.toReal_nonneg
  have hf_ne_top (x : A) : f x ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num) (hf_one x)
  have hofReal (x : A) : ENNReal.ofReal (g x) = f x :=
    ENNReal.ofReal_toReal (hf_ne_top x)
  have hmu :
      (∫⁻ x, f x ∂mu) =
        ∫⁻ t in Ioi (0 : Real), mu {x | t <= g x} := by
    calc
      (∫⁻ x, f x ∂mu) = ∫⁻ x, ENNReal.ofReal (g x) ∂mu :=
        lintegral_congr fun x => (hofReal x).symm
      _ = _ := lintegral_eq_lintegral_meas_le mu
        (Eventually.of_forall hg_nonnegative) hg.aemeasurable
  have hnu :
      (∫⁻ x, f x ∂nu) =
        ∫⁻ t in Ioi (0 : Real), nu {x | t <= g x} := by
    calc
      (∫⁻ x, f x ∂nu) = ∫⁻ x, ENNReal.ofReal (g x) ∂nu :=
        lintegral_congr fun x => (hofReal x).symm
      _ = _ := lintegral_eq_lintegral_meas_le nu
        (Eventually.of_forall hg_nonnegative) hg.aemeasurable
  let bonus : Real -> ENNReal :=
    fun t => (Ioc (0 : Real) 1).indicator
      (fun _ => measurableTotalVariation mu nu) t
  have hbonus_measurable : Measurable bonus := by
    exact measurable_const.indicator measurableSet_Ioc
  have htail (t : Real) (ht : t ∈ Ioi (0 : Real)) :
      mu {x | t <= g x} <= nu {x | t <= g x} + bonus t := by
    by_cases ht_one : t <= 1
    · have ht_mem : t ∈ Ioc (0 : Real) 1 := ⟨ht, ht_one⟩
      simp only [bonus, indicator_of_mem ht_mem]
      have hset : MeasurableSet {x | t <= g x} :=
        measurableSet_le measurable_const hg
      have hgap :
          mu {x | t <= g x} - nu {x | t <= g x} <=
            measurableTotalVariation mu nu := by
        refine (le_max_left
          (mu {x | t <= g x} - nu {x | t <= g x})
          (nu {x | t <= g x} - mu {x | t <= g x})).trans ?_
        exact le_iSup
          (fun event : {event : Set A // MeasurableSet event} =>
            max (mu event.1 - nu event.1) (nu event.1 - mu event.1))
          ⟨{x | t <= g x}, hset⟩
      simpa [add_comm] using tsub_le_iff_right.mp hgap
    · have hgt : 1 < t := lt_of_not_ge ht_one
      have hempty : {x | t <= g x} = ∅ := by
        ext x
        simp only [mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        have hg_one : g x <= 1 := by
          simpa [g] using ENNReal.toReal_mono (by norm_num) (hf_one x)
        exact not_le_of_gt (hg_one.trans_lt hgt)
      have ht_not_mem : t ∉ Ioc (0 : Real) 1 := fun h => ht_one h.2
      simp [bonus, indicator_of_notMem ht_not_mem, hempty]
  have hintegral :
      (∫⁻ t in Ioi (0 : Real), mu {x | t <= g x}) <=
        ∫⁻ t in Ioi (0 : Real), nu {x | t <= g x} + bonus t := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact htail t ht
  have hbonus_integral :
      (∫⁻ t in Ioi (0 : Real), bonus t) =
        measurableTotalVariation mu nu := by
    simp [bonus, lintegral_indicator, Real.volume_Ioc]
  apply tsub_le_iff_right.mpr
  rw [hmu, hnu]
  calc
    (∫⁻ t in Ioi (0 : Real), mu {x | t <= g x}) <=
        ∫⁻ t in Ioi (0 : Real), nu {x | t <= g x} + bonus t := hintegral
    _ = (∫⁻ t in Ioi (0 : Real), nu {x | t <= g x}) +
        ∫⁻ t in Ioi (0 : Real), bonus t := by
      rw [lintegral_add_right _ hbonus_measurable]
    _ = measurableTotalVariation mu nu +
        ∫⁻ t in Ioi (0 : Real), nu {x | t <= g x} := by
      rw [hbonus_integral, add_comm]

private theorem measurable_total_variation_comp_le
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu nu : Measure A) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (K : Kernel A B) [IsMarkovKernel K] :
    measurableTotalVariation (K ∘ₘ mu) (K ∘ₘ nu) <=
      measurableTotalVariation mu nu := by
  unfold measurableTotalVariation
  refine iSup_le fun event => ?_
  have hmeasurable : Measurable fun x => K x event.1 :=
    K.measurable_coe event.2
  have hone (x : A) : K x event.1 <= 1 := by
    exact (measure_mono (subset_univ event.1)).trans_eq measure_univ
  rw [Measure.bind_apply event.2 K.aemeasurable,
    Measure.bind_apply event.2 K.aemeasurable]
  apply max_le
  · exact lintegral_tsub_le_measurable_total_variation
      mu nu (fun x => K x event.1) hmeasurable hone
  · calc
      (∫⁻ x, K x event.1 ∂nu) - (∫⁻ x, K x event.1 ∂mu) <=
          measurableTotalVariation nu mu :=
        lintegral_tsub_le_measurable_total_variation
          nu mu (fun x => K x event.1) hmeasurable hone
      _ = measurableTotalVariation mu nu := by
        simp only [measurableTotalVariation, max_comm]

/-- Composition of approximate Markov simulators proves the one-way
deficiency triangle inequality for arbitrary measurable experiments. -/
theorem measurable_deficiency_triangle
    {State FirstObservation MiddleObservation FinalObservation : Type*}
    [MeasurableSpace State] [MeasurableSpace FirstObservation]
    [MeasurableSpace MiddleObservation] [MeasurableSpace FinalObservation]
    (first : Kernel State FirstObservation) [IsMarkovKernel first]
    (middle : Kernel State MiddleObservation) [IsMarkovKernel middle]
    (final : Kernel State FinalObservation) [IsMarkovKernel final] :
    measurableDeficiency final first <=
      measurableDeficiency final middle + measurableDeficiency middle first := by
  unfold measurableDeficiency
  apply ENNReal.le_iInf_add_iInf
  intro middleToFinal firstToMiddle
  letI : IsMarkovKernel middleToFinal.1 := middleToFinal.2
  letI : IsMarkovKernel firstToMiddle.1 := firstToMiddle.2
  let composite : Kernel FirstObservation FinalObservation :=
    middleToFinal.1 ∘ₖ firstToMiddle.1
  letI : IsMarkovKernel composite := inferInstance
  have herror :
      measurableSimulationError final first composite <=
        measurableSimulationError final middle middleToFinal.1 +
          measurableSimulationError middle first firstToMiddle.1 := by
    unfold measurableSimulationError
    refine iSup_le fun state => ?_
    calc
      measurableTotalVariation (final state) ((composite ∘ₖ first) state) <=
          measurableTotalVariation
              (final state) ((middleToFinal.1 ∘ₖ middle) state) +
            measurableTotalVariation
              ((middleToFinal.1 ∘ₖ middle) state)
              ((composite ∘ₖ first) state) :=
        measurable_total_variation_triangle _ _ _
      _ = measurableTotalVariation
              (final state) ((middleToFinal.1 ∘ₖ middle) state) +
            measurableTotalVariation
              ((middleToFinal.1 ∘ₖ middle) state)
              ((middleToFinal.1 ∘ₖ (firstToMiddle.1 ∘ₖ first)) state) := by
        rw [show composite ∘ₖ first =
            middleToFinal.1 ∘ₖ (firstToMiddle.1 ∘ₖ first) by
          simp only [composite, Kernel.comp_assoc]]
      _ <= measurableTotalVariation
              (final state) ((middleToFinal.1 ∘ₖ middle) state) +
            measurableTotalVariation
              (middle state) ((firstToMiddle.1 ∘ₖ first) state) := by
        apply add_le_add le_rfl
        simpa only [Kernel.comp_apply] using
          measurable_total_variation_comp_le
            (middle state) ((firstToMiddle.1 ∘ₖ first) state) middleToFinal.1
      _ <= (⨆ candidate, measurableTotalVariation
              (final candidate) ((middleToFinal.1 ∘ₖ middle) candidate)) +
            ⨆ candidate, measurableTotalVariation
              (middle candidate) ((firstToMiddle.1 ∘ₖ first) candidate) :=
        add_le_add
          (le_iSup (fun candidate => measurableTotalVariation
            (final candidate) ((middleToFinal.1 ∘ₖ middle) candidate)) state)
          (le_iSup (fun candidate => measurableTotalVariation
            (middle candidate) ((firstToMiddle.1 ∘ₖ first) candidate)) state)
  calc
    (⨅ simulator :
        {K : Kernel FirstObservation FinalObservation // IsMarkovKernel K},
        measurableSimulationError final first simulator.1) <=
        measurableSimulationError final first composite :=
      iInf_le_of_le (⟨composite, inferInstance⟩) le_rfl
    _ <= measurableSimulationError final middle middleToFinal.1 +
        measurableSimulationError middle first firstToMiddle.1 := herror

#print axioms measurable_deficiency_triangle

end D5.S3.Estimation.SequentialDecisionRisk.MeasurableDeficiencyTriangle
