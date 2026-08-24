/- GID: D5/S3/Observer/ProbabilisticClosure/ConullImageProbabilityIsomorphism
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/ConullImageProbabilityIsomorphism
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A conull measurable injection pulls a probability law back to its domain. -/

import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/- Library-search audit trail (2026-08-24):
   * Current-tree searches for measurable equivalences, conull ranges, measure
     pullbacks, and probability-space isomorphisms found no exact theorem.
   * Pinned Mathlib exact hits `Measurable.measurableEmbedding`,
     `MeasurableEmbedding.equivRange`, and `map_comap_subtype_coe` supply the
     standard-Borel embedding, its canonical equivalence with the range, and
     the pushforward of the range pullback. They are applied directly below.
   * `ae_mem_iff_measure_eq`, `Measure.restrict_eq_self_of_ae_mem`,
     `MeasurableEquiv.map_map_symm`, and
     `Measure.isProbabilityMeasure_of_map` close the conull and probability
     obligations. No single pinned theorem packaged all public clauses.
   * `loogle` and `leansearch` executables are absent from PATH on this lane. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace D5.S3.Observer.ProbabilisticClosure.ConullImageProbabilityIsomorphism

universe u v

/-- A measurable injection between standard Borel spaces whose image has full
probability mass pulls the probability measure back to the domain. The
canonical measurable equivalence with the image is measure-preserving. -/
theorem conull_measurable_injection_probability_isomorphism
    {X : Type u} {O : Type v}
    [MeasurableSpace X] [MeasurableSpace O]
    [StandardBorelSpace X] [StandardBorelSpace O]
    (q : X -> O) (nu : Measure O) [IsProbabilityMeasure nu]
    (hq : Measurable q) (hq_injective : Function.Injective q)
    (h_range : nu (Set.range q) = 1) :
    let embedding : MeasurableEmbedding q := hq.measurableEmbedding hq_injective
    let rangeMeasure : Measure (Set.range q) :=
      nu.comap (fun z : Set.range q => (z : O))
    exists mu : Measure X,
      IsProbabilityMeasure mu /\
        Measure.map q mu = nu /\
        MeasurePreserving embedding.equivRange mu rangeMeasure := by
  let embedding : MeasurableEmbedding q := hq.measurableEmbedding hq_injective
  let rangeMeasure : Measure (Set.range q) :=
    nu.comap (fun z : Set.range q => (z : O))
  have h_ae_range : ∀ᵐ x ∂nu, x ∈ Set.range q := by
    exact (ae_mem_iff_measure_eq embedding.measurableSet_range.nullMeasurableSet).2 (by
      simpa using h_range)
  have h_restrict : nu.restrict (Set.range q) = nu :=
    Measure.restrict_eq_self_of_ae_mem h_ae_range
  have h_range_map :
      Measure.map (fun z : Set.range q => (z : O)) rangeMeasure = nu := by
    change Measure.map (fun z : Set.range q => (z : O))
      (nu.comap (fun z : Set.range q => (z : O))) = nu
    rw [map_comap_subtype_coe embedding.measurableSet_range]
    exact h_restrict
  letI : IsProbabilityMeasure rangeMeasure := by
    letI : IsProbabilityMeasure
        (Measure.map (fun z : Set.range q => (z : O)) rangeMeasure) :=
      h_range_map.symm ▸ inferInstance
    exact Measure.isProbabilityMeasure_of_map (fun z : Set.range q => (z : O))
  let mu : Measure X := rangeMeasure.map embedding.equivRange.symm
  letI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map embedding.equivRange.symm.measurable.aemeasurable
  refine ⟨mu, inferInstance, ?_, ?_⟩
  · calc
      Measure.map q mu =
          Measure.map (fun z : Set.range q => (z : O))
            (Measure.map embedding.equivRange mu) := by
              rw [Measure.map_map
                (MeasurableEmbedding.subtype_coe embedding.measurableSet_range).measurable
                embedding.equivRange.measurable]
              apply Measure.map_congr
              filter_upwards with x
              exact congrArg Subtype.val (embedding.equivRange_apply x).symm
      _ = Measure.map (fun z : Set.range q => (z : O)) rangeMeasure := by
        rw [show Measure.map embedding.equivRange mu = rangeMeasure by
          exact MeasurableEquiv.map_map_symm embedding.equivRange]
      _ = nu := h_range_map
  · refine { measurable := embedding.equivRange.measurable, map_eq := ?_ }
    exact MeasurableEquiv.map_map_symm embedding.equivRange

#print axioms conull_measurable_injection_probability_isomorphism

end D5.S3.Observer.ProbabilisticClosure.ConullImageProbabilityIsomorphism
