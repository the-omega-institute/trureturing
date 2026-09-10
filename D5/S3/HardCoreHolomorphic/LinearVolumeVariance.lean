/- GID: D5/S3/HardCoreHolomorphic/LinearVolumeVariance
   generality: G
   mirror-B: D5/B/S3/HardCoreHolomorphic/LinearVolumeVariance
   mirror-E: none(waiver:actual-grid-Cauchy-fluctuation-bound)
   anchors: []
   digest: The common complex activity tube controls actual Gibbs variance linearly in volume. -/

import D5.S3.HardCoreHolomorphic.OccupationResponse
import Mathlib.Analysis.Complex.Liouville

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.HardCoreHolomorphic.LinearVolumeVariance

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open D5.S3.StatisticalMechanics.HardCore.OccupationMoments
open D5.S3.StatisticalMechanics.HardCore.GibbsOccupation
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
open D5.S3.HardCoreHolomorphic.TubeEstimates
open D5.S3.HardCoreHolomorphic.AdaptiveComplexNeighborhood
open D5.S3.HardCoreHolomorphic.FiniteGridZeroFree
open D5.S3.HardCoreHolomorphic.NormalizedPartitionLog
open D5.S3.HardCoreHolomorphic.OccupationResponse

/-- Analytic continuation of the actual mean particle number. The denominator
is the zeroth moment, already proved equal to the actual partition. -/
def complexMean (V : Finset Point) (z : ℂ) : ℂ :=
  moment squareGrid V 1 z / moment squareGrid V 0 z

/-- One explicit sufficient variance coefficient, with no numerical sharpness
claim. Its size comes from the inherited width epsilon = 10^-30. -/
def varianceConstant : ℝ := 16 * 10^30

private theorem real_mem_tube (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 51 / 20) :
    (lam : ℂ) ∈ ActivityTube := by
  refine ⟨lam, hlam, ?_⟩
  simpa using width_arithmetic.2.1

/-- The actual mean continuation is holomorphic on the inherited common tube.
Polynomial moments and the already-proved actual nonzero denominator suffice. -/
theorem complex_mean_differentiableAt (V : Finset Point) (z : ℂ)
    (hz : z ∈ ActivityTube) : DifferentiableAt ℂ (complexMean V) z := by
  have hn : moment squareGrid V 0 z ≠ 0 := by
    rw [moment_zero_order]
    exact finite_grid_zero_free V z hz
  exact (moment_hasDerivAt squareGrid V 1 z).differentiableAt.div
    (moment_hasDerivAt squareGrid V 0 z).differentiableAt hn

/-- Connect the same analytic mean to the existing normalized logarithm;
there is no division by activity and the origin remains included. -/
theorem complex_mean_eq_log_response (V : Finset Point) (z : ℂ)
    (hz : z ∈ ActivityTube) : complexMean V z = z * deriv (normalizedLog V) z := by
  simpa only [complexMean, moment_zero_order] using
    (normalized_log_first_moment V z hz).symm

/-- The actual mean continuation has the inherited graph-size-linear norm bound. -/
theorem complex_mean_norm_bound (V : Finset Point) (z : ℂ)
    (hz : z ∈ ActivityTube) : ‖complexMean V z‖ ≤ 3 * (V.card : ℝ) := by
  rw [complex_mean_eq_log_response V z hz]
  exact normalized_log_scaled_response_bound V z hz

/-- The closed Cauchy disk stays strictly inside the common activity tube,
including disks centered at either endpoint of the real interval. -/
theorem closed_cauchy_disk_subset (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 51 / 20) :
    Metric.closedBall (lam : ℂ) (epsilon / 2) ⊆ ActivityTube := by
  intro z hz
  refine ⟨lam, hlam, ?_⟩
  have hnorm : ‖z - (lam : ℂ)‖ ≤ epsilon / 2 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  exact hnorm.trans_lt (by linarith [width_arithmetic.2.1])

/-- Apply Mathlib's Cauchy derivative estimate to the actual mean. The disk,
its boundary bound, holomorphy and closed-disk continuity are all derived;
no supplied Cauchy estimate or derivative bound is a theorem premise. -/
theorem complex_mean_deriv_bound (V : Finset Point) (lam : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 51 / 20) :
    ‖deriv (complexMean V) (lam : ℂ)‖ ≤ 6 * (V.card : ℝ) / epsilon := by
  have hR : 0 < epsilon / 2 := by norm_num [epsilon]
  have hd : DifferentiableOn ℂ (complexMean V) ActivityTube :=
    fun z hz => (complex_mean_differentiableAt V z hz).differentiableWithinAt
  have hsub := closed_cauchy_disk_subset lam hlam
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (f := complexMean V) (c := (lam : ℂ)) (C := 3 * (V.card : ℝ)) hR
    (hd.diffContOnCl_ball hsub)
    (fun z hz => complex_mean_norm_bound V z (hsub
      (Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hz).le)))
  calc
    _ ≤ (3 * (V.card : ℝ)) / (epsilon / 2) := hc
    _ = _ := by field_simp [ne_of_gt width_arithmetic.2.1]; ring

/-- The complex derivative yields the actual real Gibbs variance. This uses
both fields' identical finite moments and the already-proved response identity;
no unproved interchange of real and complex derivatives is used. -/
theorem variance_eq_scaled_complex_deriv (V : Finset Point) (lam : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 51 / 20) :
    ((occupationVariance squareGrid V lam : ℝ) : ℂ) =
      (lam : ℂ) * deriv (complexMean V) (lam : ℂ) := by
  have hn : moment squareGrid V 0 (lam : ℂ) ≠ 0 := by
    rw [moment_zero_order]
    exact finite_grid_zero_free V (lam : ℂ) (real_mem_tube lam hlam)
  have hresponse := normalized_moment_response squareGrid V 1 (lam : ℂ) hn
  have hcast : ((occupationVariance squareGrid V lam : ℝ) : ℂ) =
      moment squareGrid V 2 (lam : ℂ) / moment squareGrid V 0 (lam : ℂ) -
        (moment squareGrid V 1 (lam : ℂ) / moment squareGrid V 0 (lam : ℂ)) ^ 2 := by
    rw [variance_eq_moments squareGrid V lam hlam.1]
    simp [meanOccupation, moment_zero_order, moment, partition]
  rw [hcast]
  unfold complexMean
  simpa only [Nat.reduceAdd, pow_two] using hresponse.symm

/-- The sharper intermediate bound retains the real activity factor. In
particular it vanishes at zero without a separate division-by-lambda step. -/
theorem grid_variance_linear_activity (V : Finset Point) (lam : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 51 / 20) :
    occupationVariance squareGrid V lam ≤ (6 * lam / epsilon) * (V.card : ℝ) := by
  have he := congrArg norm (variance_eq_scaled_complex_deriv V lam hlam)
  have hv := occupation_variance_nonneg squareGrid V lam hlam.1
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv,
    norm_mul, abs_of_nonneg hlam.1] at he
  calc
    _ = lam * ‖deriv (complexMean V) (lam : ℂ)‖ := he
    _ ≤ lam * (6 * (V.card : ℝ) / epsilon) :=
      mul_le_mul_of_nonneg_left (complex_mean_deriv_bound V lam hlam) hlam.1
    _ = _ := by ring

/-- Actual finite-square-grid occupation variance grows at most linearly in
volume, uniformly on the full closed interval [0,51/20]. The empty domain is
included. The large explicit constant is sufficient, not sharp. -/
theorem grid_variance_linear_volume (V : Finset Point) (lam : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 51 / 20) :
    0 ≤ occupationVariance squareGrid V lam ∧
      occupationVariance squareGrid V lam ≤ varianceConstant * (V.card : ℝ) := by
  refine ⟨occupation_variance_nonneg squareGrid V lam hlam.1, ?_⟩
  have hc : 6 * lam / epsilon ≤ varianceConstant := by
    norm_num [epsilon, varianceConstant]
    linarith [hlam.2]
  exact (grid_variance_linear_activity V lam hlam).trans
    (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _))

#print axioms complex_mean_deriv_bound
#print axioms variance_eq_scaled_complex_deriv
#print axioms grid_variance_linear_activity
#print axioms grid_variance_linear_volume

end D5.S3.HardCoreHolomorphic.LinearVolumeVariance
