/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual event-supremum TV topology and complete-coordinate Borel structure. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelCommonFlow
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRowRisks
import Mathlib.Topology.EMetricSpace.Lipschitz

/- This instance layer retains the native descriptor and paid-history dependency family.
   The I classification does not enlarge its original endpoint boxes or mathematical quantifiers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelTVTopology
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open FourthSegmentStoppedLaw NativeFullResidual NativeBorelCommonFlow
open NativeConditionalControl.Tail

abbrev Simplex (s : ActivePhase) :=
  {p : ValidTail s → ℝ≥0∞ // ∑' t, p t = 1}

private def reconstruct (s : ActivePhase) (p : Simplex s) :
    ProbabilityMeasure (ValidTail s) :=
  ⟨Measure.sum (fun t => p.val t • Measure.dirac t), ⟨by simpa using p.property⟩⟩

/-- All coordinates, including infinity, give an invertible measurable coding. -/
def coordinateEquiv (s : ActivePhase) : ProbabilityMeasure (ValidTail s) ≃ᵐ Simplex s where
  toFun (D : ProbabilityMeasure (ValidTail s)) := ⟨fun t => D.val {t}, by
    have h := congrArg (fun μ : Measure (ValidTail s) => μ Set.univ)
      (Measure.sum_smul_dirac (D : Measure _))
    simpa only [ProbabilityMeasure.val_eq_to_measure, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
      Measure.dirac_apply, Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply,
      smul_eq_mul, mul_one, measure_univ] using h⟩
  invFun := reconstruct s
  left_inv D := by
    apply Subtype.ext
    exact Measure.sum_smul_dirac _
  right_inv p := by
    apply Subtype.ext
    funext t
    exact Measure.sum_smul_dirac_singleton
  measurable_toFun := (Measurable.of_eval (fun t =>
    (Measure.measurable_coe (measurableSet_singleton t)).comp
      measurable_subtype_coe)).subtype_mk
  measurable_invFun := by
    apply Measurable.subtype_mk
    apply Measure.measurable_of_measurable_coe
    intro E hE
    simp only [reconstruct, Measure.sum_apply _ hE, Measure.smul_apply, smul_eq_mul]
    exact Measurable.tsum (fun t =>
      ((measurable_pi_apply t).comp measurable_subtype_coe).mul_const _)

theorem regular_measurable (s : ActivePhase) :
    MeasurableSet {D : ProbabilityMeasure (ValidTail s) | Regular s D} := by
  let k : ℝ≥0∞ := match s with | .p => 1 | .beta => upper
  have he : Measurable (emission s) := by
    cases s
    · exact (Measure.measurable_coe (measurableSet_singleton _)).comp measurable_subtype_coe
    · exact measurable_const.sub ((Measure.measurable_coe
        (measurableSet_singleton _)).comp measurable_subtype_coe)
  have hset : {D : ProbabilityMeasure (ValidTail s) | Regular s D} =
      {D | lower ≤ emission s D} ∩ ({D | emission s D ≤ upper} ∩
        ⋂ j : ℕ, {D : ProbabilityMeasure (ValidTail s) |
          (D : Measure _) (tailSet s j) ≤ k * tailRate ^ j}) := by
    ext D
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    cases s <;> rfl
  rw [hset]
  refine (measurableSet_le measurable_const he).inter
    ((measurableSet_le he measurable_const).inter (MeasurableSet.iInter (fun j => ?_)))
  exact measurableSet_le ((Measure.measurable_coe
    (Set.to_countable (tailSet s j)).measurableSet).comp
    (show Measurable (fun D : ProbabilityMeasure (ValidTail s) =>
      (D : Measure (ValidTail s))) from measurable_subtype_coe)) measurable_const

private instance simplex_standardBorel (s : ActivePhase) : StandardBorelSpace (Simplex s) :=
  (measurableSet_eq_fun (Measurable.tsum (fun t : ValidTail s => measurable_pi_apply t))
    measurable_const).standardBorel

instance probability_standardBorel (s : ActivePhase) :
    StandardBorelSpace (ProbabilityMeasure (ValidTail s)) := by
  let e := coordinateEquiv s
  let simplexUpgrade := upgradeStandardBorel (Simplex s)
  letI : TopologicalSpace (Simplex s) := simplexUpgrade.toTopologicalSpace
  letI : BorelSpace (Simplex s) := simplexUpgrade.toBorelSpace
  letI : PolishSpace (Simplex s) := simplexUpgrade.toPolishSpace
  letI : TopologicalSpace (ProbabilityMeasure (ValidTail s)) :=
    TopologicalSpace.induced e inferInstance
  letI : BorelSpace (ProbabilityMeasure (ValidTail s)) :=
    e.measurableEmbedding.borelSpace ⟨rfl⟩
  letI : PolishSpace (ProbabilityMeasure (ValidTail s)) := e.toEquiv.polishSpace_induced
  infer_instance

instance descriptor_standardBorel (s : ActivePhase) : StandardBorelSpace (RegularDescriptor s) :=
  (regular_measurable s).standardBorel

/-- Source regularity forces zero noncompletion mass without deleting its coordinate. -/
theorem regular_infinity_zero (s : ActivePhase) (D : RegularDescriptor s) :
    law D {infinity s} = 0 := by
  have hr : tailRate < 1 := by
    apply (ENNReal.toReal_lt_toReal (by unfold tailRate; finiteness) (by simp)).mp
    norm_num [tailRate]
  cases s <;> (apply le_antisymm _ bot_le)
  · have hb : ∀ j, law D {infinity .p} ≤ tailRate ^ j := by
      intro j
      refine (measure_mono ?_).trans (by simpa only [law, one_mul] using D.property.2.2 j)
      intro t ht
      obtain rfl := Set.mem_singleton_iff.mp ht
      exact Or.inl rfl
    exact ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr)
      (Filter.Eventually.of_forall hb)
  · have hb : ∀ j, law D {infinity .beta} ≤ upper * tailRate ^ j := by
      intro j
      refine (measure_mono ?_).trans (D.property.2.2 j)
      intro t ht
      obtain rfl := Set.mem_singleton_iff.mp ht
      exact Or.inl rfl
    have ht := ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr)
      (Or.inr (show upper ≠ ∞ by unfold upper; finiteness))
    simp only [mul_zero] at ht
    exact ge_of_tendsto ht (Filter.Eventually.of_forall hb)

theorem residualB_measurable : Measurable residualB := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  simp only [residualB, Measure.smul_apply, smul_eq_mul,
    prependB_embedding.comap_apply]
  exact (measurable_const.sub measurable_u).inv.mul
    ((Measure.measurable_coe (prependB_embedding.measurableSet_image.mpr hE)).comp
      (measurable_law .p))

theorem residualA_measurable : Measurable residualA := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  simp only [residualA, Measure.smul_apply, smul_eq_mul,
    prependA_embedding.comap_apply]
  exact measurable_v.inv.mul
    ((Measure.measurable_coe (prependA_embedding.measurableSet_image.mpr hE)).comp
      (measurable_law .beta))


private theorem finite_event_bound (s : ActivePhase)
    (P Q : ProbabilityMeasure (ValidTail s)) (F : Finset (ValidTail s)) (E : Set (ValidTail s)) :
    (P : Measure _).real E - (Q : Measure _).real E ≤
      (∑ t ∈ F, |(P : Measure _).real {t} - (Q : Measure _).real {t}|) +
        (P : Measure _).real (F : Set (ValidTail s))ᶜ := by
  classical
  have hp := measureReal_inter_add_sdiff (μ := (P : Measure _))
    (s := E) F.measurableSet
  have htail : (P : Measure _).real (E \ (F : Set (ValidTail s))) ≤
      (P : Measure _).real (F : Set (ValidTail s))ᶜ :=
    measureReal_mono (fun _ ht => ht.2)
  have hq : (Q : Measure _).real (E ∩ (F : Set (ValidTail s))) ≤ (Q : Measure _).real E :=
    measureReal_mono Set.inter_subset_left
  have hd : (P : Measure _).real (E ∩ (F : Set (ValidTail s))) -
      (Q : Measure _).real (E ∩ (F : Set (ValidTail s))) ≤
        ∑ t ∈ F, |(P : Measure _).real {t} - (Q : Measure _).real {t}| := by
    have he : E ∩ (F : Set (ValidTail s)) = (F.filter (fun t => t ∈ E) : Set (ValidTail s)) := by
      ext t
      simp [and_comm]
    rw [he, ← sum_measureReal_singleton, ← sum_measureReal_singleton, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ t ∈ F.filter (fun t => t ∈ E),
          |(P : Measure _).real {t} - (Q : Measure _).real {t}| :=
        Finset.sum_le_sum (fun t _ => le_abs_self _)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun t _ _ => abs_nonneg _)
  linarith

/-- A finite coordinate neighborhood controls the actual event-supremum TV distance. -/
theorem tv_finite_coordinate_bound (s : ActivePhase)
    (P Q : ProbabilityMeasure (ValidTail s)) (F : Finset (ValidTail s)) :
    D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction.measurableTotalVariation
      (P : Measure (ValidTail s)) (Q : Measure (ValidTail s)) ≤
        ENNReal.ofReal ((∑ t ∈ F, |(P : Measure _).real {t} - (Q : Measure _).real {t}|) +
          (P : Measure _).real (F : Set (ValidTail s))ᶜ) := by
  classical
  unfold D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction.measurableTotalVariation
  refine iSup_le (fun E => max_le ?_ ?_)
  · rw [← ENNReal.ofReal_toReal (measure_ne_top (P : Measure _) E.val),
      ← ENNReal.ofReal_toReal (measure_ne_top (Q : Measure _) E.val),
      ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal (finite_event_bound s P Q F E.val)
  · have hc := finite_event_bound s P Q F E.valᶜ
    rw [measureReal_compl E.property, measureReal_compl E.property,
      probReal_univ, probReal_univ] at hc
    rw [← ENNReal.ofReal_toReal (measure_ne_top (Q : Measure _) E.val),
      ← ENNReal.ofReal_toReal (measure_ne_top (P : Measure _) E.val),
      ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg]
    apply ENNReal.ofReal_le_ofReal
    change (Q : Measure _).real E.val - (P : Measure _).real E.val ≤ _
    linarith


open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open FourthSegmentStoppedLaw NativeFullResidual NativeBorelCommonFlow NativeBorelTVTopology
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
