/- GID: D5/S3/Observer/MetricGeometryLaws/ClosedConvexDistanceWitnessDuality
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometryLaws/ClosedConvexDistanceWitnessDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compact convex distance equals normalized support-witness violation. -/

import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.HausdorffDistance

/- Library-search audit trail (2026-08-28):
   * Repository and pinned-Mathlib searches found no exact distance/support
     duality theorem on a general real normed carrier.
   * Exact pinned-Mathlib component hits `geometric_hahn_banach_open`,
     `Metric.le_infDist`, `ContinuousLinearMap.sSup_unit_ball_eq_norm`, and the
     conditionally complete `sSup` bounds are applied directly below.
   * The source's behavior image is inherited from the preceding compact convex
     state-space context. Compactness makes every real support value finite, so
     no extended-real replacement or Euclidean specialization is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.MetricGeometryLaws.ClosedConvexDistanceWitnessDuality

open Set

/-- In a real normed coordinate space, distance to a nonempty compact convex
realizable image is exactly the largest violation of a support inequality by a
continuous linear witness of dual norm at most one. -/
theorem closed_convex_distance_witness_duality
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (image : Set E) (imageCompact : IsCompact image)
    (imageConvex : Convex ℝ image) (imageNonempty : image.Nonempty)
    (signature : E) :
    Metric.infDist signature image =
      sSup {violation : ℝ | ∃ witness : StrongDual ℝ E,
        ‖witness‖ ≤ 1 ∧
          violation = witness signature - sSup (witness '' image)} := by
  let violations : Set ℝ :=
    {violation | ∃ witness : StrongDual ℝ E,
      ‖witness‖ ≤ 1 ∧
        violation = witness signature - sSup (witness '' image)}
  change Metric.infDist signature image = sSup violations
  have supportBounded (witness : StrongDual ℝ E) :
      BddAbove (witness '' image) :=
    (imageCompact.image witness.continuous).bddAbove
  have violation_le_distance
      {violation : ℝ} (violationMem : violation ∈ violations) :
      violation ≤ Metric.infDist signature image := by
    rcases violationMem with ⟨witness, witnessNorm, rfl⟩
    apply (Metric.le_infDist imageNonempty).2
    intro realized realizedMem
    have realized_le_support :
        witness realized ≤ sSup (witness '' image) :=
      le_csSup (supportBounded witness) ⟨realized, realizedMem, rfl⟩
    calc
      witness signature - sSup (witness '' image) ≤
          witness signature - witness realized :=
        sub_le_sub_left realized_le_support _
      _ = witness (signature - realized) := by rw [map_sub]
      _ ≤ |witness (signature - realized)| := le_abs_self _
      _ = ‖witness (signature - realized)‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ ‖witness‖ * ‖signature - realized‖ :=
        witness.le_opNorm _
      _ ≤ 1 * ‖signature - realized‖ :=
        mul_le_mul_of_nonneg_right witnessNorm (norm_nonneg _)
      _ = dist signature realized := by
        rw [one_mul, dist_eq_norm]
  have zeroViolation : (0 : ℝ) ∈ violations := by
    refine ⟨0, by simp, ?_⟩
    have zeroImage : (0 : StrongDual ℝ E) '' image = {0} := by
      ext value
      constructor
      · rintro ⟨realized, realizedMem, rfl⟩
        simp
      · intro valueMem
        have valueZero : value = 0 := by simpa using valueMem
        subst value
        rcases imageNonempty with ⟨realized, realizedMem⟩
        exact ⟨realized, realizedMem, by simp⟩
    rw [zeroImage, csSup_singleton]
    simp
  have violationsNonempty : violations.Nonempty := ⟨0, zeroViolation⟩
  have violationsBounded : BddAbove violations :=
    ⟨Metric.infDist signature image,
      fun _ violationMem => violation_le_distance violationMem⟩
  apply le_antisymm
  · apply le_of_forall_lt_imp_le_of_dense
    intro radius radiusBelowDistance
    by_cases radiusPositive : 0 < radius
    · have ballDisjoint :
          Disjoint (Metric.ball signature radius) image :=
        Metric.disjoint_ball_infDist.mono
          (Metric.ball_subset_ball radiusBelowDistance.le) Set.Subset.rfl
      obtain ⟨separator, threshold, ballBelow, imageAbove⟩ :=
        geometric_hahn_banach_open
          (convex_ball signature radius) Metric.isOpen_ball
          imageConvex ballDisjoint
      have signatureBelow : separator signature < threshold :=
        ballBelow signature (Metric.mem_ball_self radiusPositive)
      have separatorNeZero : separator ≠ 0 := by
        intro separatorZero
        rcases imageNonempty with ⟨realized, realizedMem⟩
        have thresholdNonpositive := imageAbove realized realizedMem
        simp only [separatorZero, zero_apply] at signatureBelow thresholdNonpositive
        linarith
      have separatorNormPositive : 0 < ‖separator‖ :=
        norm_pos_iff.mpr separatorNeZero
      have separatorNormBound :
          ‖separator‖ ≤
            (threshold - separator signature) / radius := by
        rw [← separator.sSup_unit_ball_eq_norm]
        apply csSup_le ((Metric.nonempty_ball.mpr zero_lt_one).image _)
        intro value valueMem
        rcases valueMem with ⟨direction, directionMem, rfl⟩
        have directionNorm : ‖direction‖ < 1 := by
          simpa [Metric.mem_ball, dist_eq_norm] using directionMem
        have plusMem :
            signature + radius • direction ∈
              Metric.ball signature radius := by
          rw [Metric.mem_ball, dist_eq_norm]
          simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_pos radiusPositive]
          nlinarith [norm_nonneg direction]
        have minusMem :
            signature - radius • direction ∈
              Metric.ball signature radius := by
          rw [Metric.mem_ball, dist_eq_norm]
          simp only [sub_sub_cancel_left, norm_neg, norm_smul,
            Real.norm_eq_abs, abs_of_pos radiusPositive]
          nlinarith [norm_nonneg direction]
        have plusBelow := ballBelow _ plusMem
        have minusBelow := ballBelow _ minusMem
        simp only [map_add, map_sub, map_smul, smul_eq_mul] at plusBelow minusBelow
        change |separator direction| ≤
          (threshold - separator signature) / radius
        rw [abs_le]
        constructor
        · rw [← neg_div]
          apply (div_le_iff₀ radiusPositive).2
          nlinarith
        · apply (le_div_iff₀ radiusPositive).2
          nlinarith
      have radiusTimesNorm :
          radius * ‖separator‖ ≤ threshold - separator signature := by
        calc
          radius * ‖separator‖ ≤
              radius * ((threshold - separator signature) / radius) :=
            mul_le_mul_of_nonneg_left separatorNormBound radiusPositive.le
          _ = threshold - separator signature := by
            field_simp [radiusPositive.ne']
      let witness : StrongDual ℝ E :=
        (-(‖separator‖⁻¹ : ℝ)) • separator
      have witnessNorm : ‖witness‖ = 1 := by
        simp [witness, norm_smul, separatorNormPositive.ne']
      have witnessSupport :
          sSup (witness '' image) ≤
            -(‖separator‖⁻¹ : ℝ) * threshold := by
        apply csSup_le (imageNonempty.image witness)
        intro value valueMem
        rcases valueMem with ⟨realized, realizedMem, rfl⟩
        simp only [witness, smul_apply, smul_eq_mul]
        exact mul_le_mul_of_nonpos_left (imageAbove realized realizedMem)
          (neg_nonpos.mpr (inv_nonneg.mpr separatorNormPositive.le))
      have radiusLeViolation :
          radius ≤ witness signature - sSup (witness '' image) := by
        have radiusLeGap :
            radius ≤
              (threshold - separator signature) / ‖separator‖ :=
          (le_div_iff₀ separatorNormPositive).2 radiusTimesNorm
        calc
          radius ≤
              (threshold - separator signature) / ‖separator‖ :=
            radiusLeGap
          _ = witness signature -
              (-(‖separator‖⁻¹ : ℝ) * threshold) := by
            rw [div_eq_mul_inv]
            simp only [witness, smul_apply, smul_eq_mul]
            ring
          _ ≤ witness signature - sSup (witness '' image) :=
            sub_le_sub_left witnessSupport _
      have violationMem :
          witness signature - sSup (witness '' image) ∈ violations :=
        ⟨witness, witnessNorm.le, rfl⟩
      exact radiusLeViolation.trans
        (le_csSup violationsBounded violationMem)
    · exact (not_lt.mp radiusPositive).trans
        (le_csSup violationsBounded zeroViolation)
  · exact csSup_le violationsNonempty
      (fun _ violationMem => violation_le_distance violationMem)

#print axioms closed_convex_distance_witness_duality

end D5.S3.Observer.MetricGeometryLaws.ClosedConvexDistanceWitnessDuality
