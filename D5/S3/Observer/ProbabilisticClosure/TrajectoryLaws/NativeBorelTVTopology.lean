/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual event-supremum TV topology and complete-coordinate Borel structure. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelRepresentation
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRowRisks
import Mathlib.Topology.EMetricSpace.Lipschitz

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelTVTopology
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open FourthSegmentStoppedLaw NativeFullResidual NativeBorelCommonFlow NativeBorelRepresentation
open NativeConditionalControl.Tail
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open D5.S3.Estimation.DataProcessing.MeasurableTotalVariationTriangle

/-- The distance is the actual supremum over measurable events. -/
abbrev tvEMetric (s : ActivePhase) : PseudoEMetricSpace (ProbabilityMeasure (ValidTail s)) :=
  PseudoEMetricSpace.ofEDist
    (fun (P Q : ProbabilityMeasure (ValidTail s)) =>
      measurableTotalVariation (P : Measure (ValidTail s)) (Q : Measure (ValidTail s)))
    (fun P => by simp [measurableTotalVariation])
    (fun P Q => measurable_total_variation_comm (P : Measure (ValidTail s)) (Q : Measure (ValidTail s)))
    (fun P Q R => measurable_total_variation_triangle (P : Measure (ValidTail s)) (Q : Measure (ValidTail s)) (R : Measure (ValidTail s)))

abbrev tvTopology (s : ActivePhase) : TopologicalSpace (ProbabilityMeasure (ValidTail s)) :=
  (tvEMetric s).toUniformSpace.toTopologicalSpace

abbrev coordinateTopology (s : ActivePhase) :
    TopologicalSpace (ProbabilityMeasure (ValidTail s)) :=
  TopologicalSpace.induced (coordinateEquiv s) inferInstance

private theorem finite_approximation (s : ActivePhase)
    (P : ProbabilityMeasure (ValidTail s)) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset (ValidTail s), (P : Measure _).real (F : Set (ValidTail s))ᶜ < ε := by
  classical
  have ht : Tendsto (fun F : Finset (ValidTail s) => ∑ t ∈ F, (P : Measure _) {t})
      atTop (𝓝 1) := by
    have h := (ENNReal.summable (f := fun t : ValidTail s => (P : Measure _) {t})).hasSum
    have hp : (∑' t : ValidTail s, (P : Measure _) {t}) = 1 := (coordinateEquiv s P).property
    rw [hp] at h
    exact h
  have hr := (ENNReal.continuousAt_toReal ENNReal.one_ne_top).tendsto.comp ht
  have hc : Tendsto (fun F : Finset (ValidTail s) =>
      (P : Measure _).real (F : Set (ValidTail s))ᶜ) atTop (𝓝 0) := by
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub hr using 1
    · funext F
      rw [measureReal_compl F.measurableSet, probReal_univ, Measure.real]
      simp only [sum_measure_singleton, Function.comp_apply]
    · simp
  exact (hc.eventually (gt_mem_nhds hε)).exists

private theorem coordinate_continuous (s : ActivePhase) (t : ValidTail s) :
    @Continuous (ProbabilityMeasure (ValidTail s)) ℝ≥0∞ (coordinateTopology s) _
      (fun P => (P : Measure _) {t}) := by
  letI := coordinateTopology s
  have he : Continuous (coordinateEquiv s) := continuous_induced_dom
  exact (continuous_apply t (A := fun _ : ValidTail s => ℝ≥0∞)).comp
    (continuous_subtype_val.comp he)

private theorem tv_coordinate_continuous (s : ActivePhase) (t : ValidTail s) :
    @Continuous (ProbabilityMeasure (ValidTail s)) ℝ≥0∞ (tvTopology s) _
      (fun P => (P : Measure _) {t}) := by
  letI := tvEMetric s
  have hl : LipschitzWith 1 (fun P : ProbabilityMeasure (ValidTail s) =>
      (P : Measure _).real {t}) := by
    intro P Q
    simp only [ENNReal.coe_one, one_mul, edist_dist, Real.dist_eq]
    change ENNReal.ofReal |(P : Measure (ValidTail s)).real {t} - (Q : Measure (ValidTail s)).real {t}| ≤
      measurableTotalVariation (P : Measure (ValidTail s)) (Q : Measure (ValidTail s))
    rw [← ENNReal.ofReal_toReal
      (NativePaidHistoryCommonRowRisks.probability_tv_finite (P : Measure (ValidTail s)) (Q : Measure (ValidTail s)))]
    exact ENNReal.ofReal_le_ofReal
      (NativePaidHistoryCommonRowRisks.event_gap _ _ _ (measurableSet_singleton t))
  have he : (fun P : ProbabilityMeasure (ValidTail s) => (P : Measure _) {t}) =
      (fun P : ProbabilityMeasure (ValidTail s) => ENNReal.ofReal ((P : Measure _).real {t})) := by
    funext P
    exact (ENNReal.ofReal_toReal (measure_ne_top (P : Measure _) {t})).symm
  rw [he]
  exact ENNReal.continuous_ofReal.comp hl.continuous

private theorem coordinate_to_tv (s : ActivePhase) :
    @Continuous (ProbabilityMeasure (ValidTail s)) (ProbabilityMeasure (ValidTail s))
      (coordinateTopology s) (tvTopology s) id := by
  apply (@continuous_iff_continuousAt _ _ (coordinateTopology s) (tvTopology s) id).mpr
  intro P
  letI := coordinateTopology s
  change Tendsto id (𝓝 P) (@nhds _ (tvTopology s) P)
  letI := tvEMetric s
  apply EMetric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨r, hr, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  obtain ⟨F, hF⟩ := finite_approximation s P (half_pos (show 0 < (r : ℝ) by exact_mod_cast hr))
  have hs : Tendsto (fun Q : ProbabilityMeasure (ValidTail s) =>
      ∑ t ∈ F, |(P : Measure _).real {t} - (Q : Measure _).real {t}|)
      (@nhds _ (coordinateTopology s) P) (𝓝 0) := by
    convert tendsto_finsetSum F (fun t _ =>
      ((tendsto_const_nhds (x := (P : Measure (ValidTail s)).real {t})).sub ((ENNReal.continuousAt_toReal (measure_ne_top (P : Measure _) {t})).tendsto.comp
        (coordinate_continuous s t).continuousAt)).abs) using 1 <;>
      simp [Measure.real, ProbabilityMeasure.coeFn_def, ENNReal.toReal]
  filter_upwards [hs.eventually (gt_mem_nhds (half_pos
    (show 0 < (r : ℝ) by exact_mod_cast hr)))] with Q hQ
  change measurableTotalVariation (Q : Measure (ValidTail s)) (P : Measure (ValidTail s)) < ε
  rw [measurable_total_variation_comm]
  apply lt_of_le_of_lt (tv_finite_coordinate_bound s P Q F)
  apply lt_trans _ hrε
  apply ENNReal.ofReal_lt_coe_iff (by positivity) |>.mpr
  linarith

/-- Both neighborhood directions hold on all laws, including laws of infinite support. -/
theorem tv_topology_eq_coordinates (s : ActivePhase) : tvTopology s = coordinateTopology s := by
  apply le_antisymm
  · letI := tvTopology s
    apply continuous_iff_le_induced.mp
    change @Continuous _ _ (tvTopology s) _ (coordinateEquiv s)
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro t
    exact tv_coordinate_continuous s t
  · have hc := continuous_iff_le_induced.mp (coordinate_to_tv s)
    simpa only [induced_id] using hc

/-- The Borel sigma algebra of actual TV equals the inherited evaluation/Giry structure. -/
theorem tv_borel_eq (s : ActivePhase) :
    @borel (ProbabilityMeasure (ValidTail s)) (tvTopology s) = (inferInstance : MeasurableSpace (ProbabilityMeasure (ValidTail s))) := by
  rw [tv_topology_eq_coordinates]
  letI := coordinateTopology s
  exact (coordinateEquiv s).measurableEmbedding.borelSpace ⟨rfl⟩ |>.measurable_eq.symm

abbrev descriptorTVTopology (s : ActivePhase) : TopologicalSpace (RegularDescriptor s) :=
  TopologicalSpace.induced Subtype.val (tvTopology s)

/-- Restriction uses exactly Regular, with all source tail inequalities unchanged. -/
theorem descriptor_tv_borel_eq (s : ActivePhase) :
    @borel (RegularDescriptor s) (descriptorTVTopology s) = (inferInstance : MeasurableSpace (RegularDescriptor s)) := by
  rw [descriptorTVTopology, borel_comap, tv_borel_eq]
  rfl

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelTVTopology
