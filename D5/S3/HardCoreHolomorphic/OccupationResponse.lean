/- GID: D5/S3/HardCoreHolomorphic/OccupationResponse
   generality: G
   mirror-B: D5/B/S3/HardCoreHolomorphic/OccupationResponse
   mirror-E: none(waiver:actual-observable-to-holomorphic-response)
   anchors: []
   digest: Actual occupation moments identify the normalized grid logarithm's activity response. -/

import D5.S3.StatisticalMechanics.HardCore.GibbsOccupation
import D5.S3.HardCoreHolomorphic.NormalizedPartitionLog

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.HardCoreHolomorphic.OccupationResponse

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open D5.S3.StatisticalMechanics.HardCore.OccupationMoments
open D5.S3.StatisticalMechanics.HardCore.GibbsOccupation
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
open D5.S3.HardCoreHolomorphic.AdaptiveComplexNeighborhood
open D5.S3.HardCoreHolomorphic.FiniteGridZeroFree
open D5.S3.HardCoreHolomorphic.PartitionLogCocycle
open D5.S3.HardCoreHolomorphic.NormalizedPartitionLog

/-- Exact entire-plane occupation identity for the original square-grid sum.
No nonvanishing or probability interpretation is needed for this equation. -/
theorem grid_partition_occupation_identity (V : Finset Point) (z : ℂ) :
    z * deriv (fun w : ℂ => gridPartition V w) z =
      ∑ v ∈ V, (gridPartition V z - gridPartition (V.erase v) z) :=
  partition_euler_occupation squareGrid V z

/-- The normalized logarithm's scaled derivative is the actual first moment
normalized by the actual partition. The z=0 endpoint is included. -/
theorem normalized_log_first_moment (V : Finset Point) (z : ℂ) (hz : z ∈ ActivityTube) :
    z * deriv (normalizedLog V) z = moment squareGrid V 1 z / gridPartition V z := by
  rw [(normalized_log_hasDerivAt V z hz).deriv]
  unfold response
  rw [← mul_div_assoc]
  have he := euler_moment squareGrid V 0 z
  have hf : (moment squareGrid V 0 : ℂ → ℂ) =
      (fun w : ℂ => gridPartition V w) := by
    funext w
    exact moment_zero_order squareGrid V w
  rw [hf] at he
  simpa only [zero_add] using congrArg (fun t : ℂ => t / gridPartition V z) he

/-- The actual analytic response equals the sum of actual one-vertex occupied
ratios. General complex values are analytic quantities, not probabilities. -/
theorem normalized_log_occupation_identity (V : Finset Point) (z : ℂ) (hz : z ∈ ActivityTube) :
    z * deriv (normalizedLog V) z = ∑ v ∈ V, (1 - gridVacancy V v z) := by
  rw [normalized_log_first_moment V z hz, moment_one_eq_deletions, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  unfold gridVacancy
  field_simp [finite_grid_zero_free V z hz]

/-- A graph-size-linear bound on the complex scaled response, using the
previous actual marked-vacancy bound and preserving the same common tube. -/
theorem normalized_log_scaled_response_bound (V : Finset Point) (z : ℂ) (hz : z ∈ ActivityTube) :
    ‖z * deriv (normalizedLog V) z‖ ≤ 3 * (V.card : ℝ) := by
  rw [normalized_log_occupation_identity V z hz]
  calc
    _ ≤ ∑ v ∈ V, ‖(1 : ℂ) - gridVacancy V v z‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ V, (3 : ℝ) := by
      apply Finset.sum_le_sum
      intro v _
      have h := norm_sub_le (1 : ℂ) (gridVacancy V v z)
      have hb := finite_grid_vacancy_bound V v z hz
      norm_num only [norm_one] at h
      linarith
    _ = _ := by simp [mul_comm]

private theorem real_activity_mem (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 51 / 20) :
    (lam : ℂ) ∈ ActivityTube := by
  refine ⟨lam, hlam, ?_⟩
  simpa using D5.S3.HardCoreHolomorphic.TubeEstimates.width_arithmetic.2.1

/-- The real Gibbs mean is exactly the scaled derivative of the already-owned
normalized complex log at the same real activity. No derivative transport or
unspecified probabilistic model is assumed. -/
theorem real_gibbs_log_derivative (V : Finset Point) (lam : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 51 / 20) :
    ((meanOccupation squareGrid V lam : ℝ) : ℂ) =
      (lam : ℂ) * deriv (normalizedLog V) (lam : ℂ) := by
  rw [normalized_log_first_moment V (lam : ℂ) (real_activity_mem lam hlam)]
  simp [meanOccupation, moment, gridPartition, partition]

/-- A direct finite-PMF expectation statement at the analytic endpoint.
This binds the claimed physical observable to the actual sampled configurations. -/
theorem gibbs_expected_card_is_log_response (V : Finset Point) (lam : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 51 / 20) :
    ((∑ S ∈ configurations squareGrid V,
        (gibbsPMF squareGrid V lam hlam.1 S).toReal * (S.card : ℝ) : ℝ) : ℂ) =
      (lam : ℂ) * deriv (normalizedLog V) (lam : ℂ) := by
  rw [gibbs_expected_card squareGrid V lam hlam.1]
  exact real_gibbs_log_derivative V lam hlam

#print axioms grid_partition_occupation_identity
#print axioms normalized_log_first_moment
#print axioms normalized_log_occupation_identity
#print axioms normalized_log_scaled_response_bound
#print axioms real_gibbs_log_derivative
#print axioms gibbs_expected_card_is_log_response

end D5.S3.HardCoreHolomorphic.OccupationResponse
