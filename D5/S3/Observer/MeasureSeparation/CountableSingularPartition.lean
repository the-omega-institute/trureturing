/- GID: D5/S3/Observer/MeasureSeparation/CountableSingularPartition
   generality: G
   mirror-B: D5/B/S3/Observer/MeasureSeparation/CountableSingularPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pairwise singular probability laws admit disjoint full-measure supports. -/

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.NullMeasurable

/- Library-search audit trail (2026-08-24):
   * Repository searches for pairwise singular measure families, common
     measurable partitions, and products of Radon--Nikodym derivatives missed.
   * Pinned Mathlib exact hits `Measure.rnDeriv_eq_zero_of_mutuallySingular`,
     `Measure.ae_rnDeriv_ne_zero_imp_of_ae`, and
     `MeasureTheory.exists_subordinate_pairwise_disjoint` are applied below.
   * Pinned Mathlib also supplies `Measure.absolutelyContinuous_smul` and
     `Measure.absolutelyContinuous_sum_right` for the source's mixture measure.
   * `loogle` and `leansearch` executables are absent from PATH. -/

noncomputable section

open Set Function MeasureTheory

namespace D5.S3.Observer.MeasureSeparation.CountableSingularPartition

/-- A countable pairwise singular family of probability laws has disjoint
measurable full-measure supports. For the source's positive normalized mixture,
the pairwise products of the corresponding densities vanish almost everywhere. -/
theorem countable_pairwise_singular_common_partition
    {alpha : Type*} [MeasurableSpace alpha]
    (probability : Nat -> Measure alpha)
    [forall n, IsProbabilityMeasure (probability n)]
    (weight : Nat -> ENNReal)
    (weight_pos : forall n, 0 < weight n)
    (weight_sum : tsum weight = 1)
    (singular : Pairwise fun n m => probability n ⟂ₘ probability m) :
    let lambda := Measure.sum fun n => weight n • probability n
    let density := fun n => (probability n).rnDeriv lambda
    (forall n m, n ≠ m ->
      density n * density m =ᵐ[lambda] (0 : alpha -> ENNReal)) /\
    exists support : Nat -> Set alpha,
      (forall n, MeasurableSet (support n)) /\
      Pairwise (Disjoint on support) /\
      forall n, probability n (support n) = 1 := by
  dsimp only
  let lambda := Measure.sum fun n => weight n • probability n
  let density := fun n => (probability n).rnDeriv lambda
  have lambda_univ : lambda univ = 1 := by
    simp [lambda, weight_sum]
  letI : IsFiniteMeasure lambda :=
    { measure_univ_lt_top := lambda_univ.trans_lt ENNReal.one_lt_top }
  have absolutely_continuous (n : Nat) : probability n ≪ lambda := by
    exact (Measure.absolutelyContinuous_smul (ne_of_gt (weight_pos n))).trans
      (Measure.absolutelyContinuous_sum_right n Measure.AbsolutelyContinuous.rfl)
  have density_product_zero : forall n m, n ≠ m ->
      density n * density m =ᵐ[lambda] (0 : alpha -> ENNReal) := by
    intro n m hnm
    have competing_zero : density m =ᵐ[probability n] (0 : alpha -> ENNReal) := by
      exact Measure.rnDeriv_eq_zero_of_mutuallySingular
        (singular hnm).symm (absolutely_continuous n)
    have lifted := Measure.ae_rnDeriv_ne_zero_imp_of_ae
      (μ := probability n) lambda competing_zero
    filter_upwards [lifted] with x hx
    by_cases hzero : density n x = 0
    · simp [hzero]
    · have hmzero : density m x = 0 := hx (by simpa [density] using hzero)
      simp [hmzero]
  refine ⟨density_product_zero, ?_⟩
  let rawSupport : Nat -> Set alpha := fun n => {x | density n x ≠ 0}
  have raw_measurable : forall n, MeasurableSet (rawSupport n) := by
    intro n
    change MeasurableSet {x | (probability n).rnDeriv lambda x ≠ 0}
    exact (Measure.measurable_rnDeriv _ _ (measurableSet_singleton 0).compl)
  have raw_ae_disjoint : Pairwise (AEDisjoint lambda on rawSupport) := by
    intro n m hnm
    change lambda (rawSupport n ∩ rawSupport m) = 0
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [density_product_zero n m hnm] with x hx
    simp only [rawSupport, mem_inter_iff, mem_setOf_eq, not_and]
    intro hn hm
    exact (mul_ne_zero hn hm) hx
  obtain ⟨support, _support_sub, raw_ae_support, support_measurable,
      support_disjoint⟩ :=
    exists_subordinate_pairwise_disjoint
      (fun n => (raw_measurable n).nullMeasurableSet) raw_ae_disjoint
  refine ⟨support, support_measurable, support_disjoint, ?_⟩
  intro n
  have raw_full : ∀ᵐ x ∂(probability n), x ∈ rawSupport n := by
    rw [← Measure.withDensity_rnDeriv_eq _ _ (absolutely_continuous n),
      ae_withDensity_iff (Measure.measurable_rnDeriv _ _)]
    exact Filter.Eventually.of_forall fun _ hne => hne
  have support_full : ∀ᵐ x ∂(probability n), x ∈ support n := by
    have transferred := (absolutely_continuous n).ae_le (raw_ae_support n)
    filter_upwards [raw_full, transferred] with x hx hxt
    exact hxt.mp hx
  have support_compl_zero : probability n (support n)ᶜ = 0 := by
    exact mem_ae_iff.mp support_full
  calc
    probability n (support n) =
        probability n (support n) + probability n (support n)ᶜ := by
      rw [support_compl_zero, add_zero]
    _ = probability n (support n ∪ (support n)ᶜ) :=
      (measure_union disjoint_compl_right (support_measurable n).compl).symm
    _ = 1 := by rw [union_compl_self, measure_univ]

#print axioms countable_pairwise_singular_common_partition

end D5.S3.Observer.MeasureSeparation.CountableSingularPartition
