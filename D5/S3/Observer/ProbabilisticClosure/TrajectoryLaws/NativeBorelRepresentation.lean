/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelRepresentation
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete-coordinate measurable reconstruction and normalized full legal residuals. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelCommonFlow
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelRepresentation
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
  measurable_toFun := (measurable_pi_lambda _ (fun t =>
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

private theorem prefix_rangeB : Set.range prependB = {pAtom 0 0}ᶜ := by
  ext t
  constructor
  · rintro ⟨x, rfl⟩
    exact p_not_prefix x
  · intro ht
    rcases p_partition t with h | ⟨x, rfl⟩
    · exact False.elim (ht h)
    · exact ⟨x, rfl⟩

private theorem prefix_rangeA : Set.range prependA = {betaStop}ᶜ := by
  ext t
  constructor
  · rintro ⟨x, rfl⟩
    exact b_not_prefix x
  · intro ht
    rcases b_partition t with h | ⟨x, rfl⟩
    · exact False.elim (ht h)
    · exact ⟨x, rfl⟩

instance residualB_probability (Q : PDescriptor) : IsProbabilityMeasure (residualB Q) := by
  constructor
  rw [residualB, Measure.smul_apply, smul_eq_mul, prependB_embedding.comap_apply,
    Set.image_univ, prefix_rangeB, measure_compl (measurableSet_singleton _) (by finiteness),
    measure_univ]
  have hu : u Q < 1 := Q.property.2.1.trans_lt (by
    apply (ENNReal.toReal_lt_toReal (by unfold upper; finiteness) (by simp)).mp
    norm_num [upper])
  exact ENNReal.inv_mul_cancel (ne_of_gt (tsub_pos_iff_lt.mpr hu))
    (ENNReal.sub_ne_top (by simp))

instance residualA_probability (W : BDescriptor) : IsProbabilityMeasure (residualA W) := by
  constructor
  rw [residualA, Measure.smul_apply, smul_eq_mul, prependA_embedding.comap_apply,
    Set.image_univ, prefix_rangeA, measure_compl (measurableSet_singleton _) (by finiteness),
    measure_univ]
  exact ENNReal.inv_mul_cancel (ne_of_gt (lt_of_lt_of_le (by norm_num [lower]) W.property.1))
    (ne_of_lt (W.property.2.1.trans_lt (by unfold upper; finiteness)))

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

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelRepresentation
