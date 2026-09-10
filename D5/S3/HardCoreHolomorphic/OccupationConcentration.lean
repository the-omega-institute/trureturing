/- GID: D5/S3/HardCoreHolomorphic/OccupationConcentration
   generality: G
   mirror-B: D5/B/S3/HardCoreHolomorphic/OccupationConcentration
   mirror-E: none(waiver:actual-finite-Gibbs-density-concentration)
   anchors: []
   digest: Actual Gibbs density fluctuations obey a mean-square and deviation-probability bound. -/

import D5.S3.HardCoreHolomorphic.LinearVolumeVariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.HardCoreHolomorphic.OccupationConcentration

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open D5.S3.StatisticalMechanics.HardCore.GibbsOccupation
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
open D5.S3.HardCoreHolomorphic.LinearVolumeVariance

/-- Mean-square fluctuation of the actual occupation density. The weights are
point masses of the existing Gibbs PMF. Empty domains are excluded whenever
this expression is interpreted as a density. -/
def densityMeanSquare (V : Finset Point) (lam : ℝ) (hlam : 0 ≤ lam) : ℝ :=
  ∑ S ∈ configurations squareGrid V, (gibbsPMF squareGrid V lam hlam S).toReal *
    ((S.card : ℝ) / V.card - meanOccupation squareGrid V lam / V.card) ^ 2

/-- Rescaling the actual centered moment gives variance divided by volume
squared. No independent-site assumption is used. -/
theorem density_mean_square_eq (V : Finset Point) (lam : ℝ) (hlam : 0 ≤ lam) :
    densityMeanSquare V lam hlam = occupationVariance squareGrid V lam / (V.card : ℝ) ^ 2 := by
  unfold densityMeanSquare
  simp_rw [gibbs_pmf_toReal, ← sub_div, div_pow, ← mul_div_assoc]
  rw [← Finset.sum_div]
  rfl

/-- The density is mean-square concentrated around its own finite-volume
mean, with a volume-independent coefficient. This makes no assertion that
those means have a common infinite-volume limit. -/
theorem grid_density_mean_square_bound (V : Finset Point) (hV : V.Nonempty)
    (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 51 / 20) :
    densityMeanSquare V lam hlam.1 ≤ varianceConstant / (V.card : ℝ) := by
  have hn : 0 < (V.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hV
  rw [density_mean_square_eq]
  calc
    _ ≤ (varianceConstant * (V.card : ℝ)) / (V.card : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (grid_variance_linear_volume V lam hlam).2 (sq_nonneg _)
    _ = _ := by field_simp [ne_of_gt hn]

/-- An actual Gibbs event probability, written as the finite sum of point
masses. It is not a probability assigned to complex normalized weights. -/
def densityDeviationMass (V : Finset Point) (lam : ℝ) (hlam : 0 ≤ lam) (t : ℝ) : ℝ :=
  ∑ S ∈ configurations squareGrid V,
    if t ≤ |(S.card : ℝ) / V.card - meanOccupation squareGrid V lam / V.card| then
      (gibbsPMF squareGrid V lam hlam S).toReal else 0

/-- The event expression is a number between zero and one, by positivity
and normalization of the actual finite probability law. -/
theorem density_deviation_mass_bounds (V : Finset Point) (lam : ℝ)
    (hlam : 0 ≤ lam) (t : ℝ) :
    0 ≤ densityDeviationMass V lam hlam t ∧ densityDeviationMass V lam hlam t ≤ 1 := by
  have hp (S : Finset Point) : 0 ≤ (gibbsPMF squareGrid V lam hlam S).toReal :=
    ENNReal.toReal_nonneg
  have htotal : (∑ S ∈ configurations squareGrid V,
      (gibbsPMF squareGrid V lam hlam S).toReal) = 1 := by
    simp_rw [gibbs_pmf_toReal]
    exact gibbs_mass_sum squareGrid V lam hlam
  unfold densityDeviationMass
  constructor
  · apply Finset.sum_nonneg
    intro S _
    split_ifs <;> positivity
  · calc
      _ ≤ ∑ S ∈ configurations squareGrid V, (gibbsPMF squareGrid V lam hlam S).toReal := by
        apply Finset.sum_le_sum
        intro S _
        split_ifs
        · exact le_rfl
        · exact hp S
      _ = 1 := htotal

/-- Finite Chebyshev estimate on this exact Gibbs sample space. The event
threshold is positive; the density denominator is not used for division in
this proof, so the algebraic inequality also covers the empty domain. -/
theorem density_deviation_le_second_moment (V : Finset Point) (lam : ℝ)
    (hlam : 0 ≤ lam) (t : ℝ) (ht : 0 < t) :
    densityDeviationMass V lam hlam t ≤ densityMeanSquare V lam hlam / t ^ 2 := by
  have hs : t ^ 2 * densityDeviationMass V lam hlam t ≤ densityMeanSquare V lam hlam := by
    unfold densityDeviationMass densityMeanSquare
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro S _
    let d : ℝ := (S.card : ℝ) / V.card - meanOccupation squareGrid V lam / V.card
    have hp : 0 ≤ (gibbsPMF squareGrid V lam hlam S).toReal := ENNReal.toReal_nonneg
    by_cases hd : t ≤ |d|
    · rw [if_pos hd]
      have hsq : t ^ 2 ≤ d ^ 2 := by
        have hm := mul_le_mul hd hd ht.le (abs_nonneg d)
        simpa only [← pow_two, sq_abs] using hm
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsq hp
    · rw [if_neg hd, mul_zero]
      exact mul_nonneg hp (sq_nonneg _)
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  simpa only [mul_comm] using hs

/-- Finite-size concentration around the actual finite-volume mean. The
constant comes from the proved analytic variance bound, not a supplied
concentration hypothesis. It becomes O(1/volume) for any fixed threshold. -/
theorem grid_density_deviation_bound (V : Finset Point) (hV : V.Nonempty)
    (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 51 / 20) (t : ℝ) (ht : 0 < t) :
    densityDeviationMass V lam hlam.1 t ≤ varianceConstant / (t ^ 2 * (V.card : ℝ)) := by
  calc
    _ ≤ densityMeanSquare V lam hlam.1 / t ^ 2 :=
      density_deviation_le_second_moment V lam hlam.1 t ht
    _ ≤ (varianceConstant / (V.card : ℝ)) / t ^ 2 :=
      div_le_div_of_nonneg_right (grid_density_mean_square_bound V hV lam hlam) (sq_nonneg _)
    _ = _ := by rw [div_div]; congr 1; ring

#print axioms grid_density_mean_square_bound
#print axioms density_deviation_le_second_moment
#print axioms grid_density_deviation_bound

end D5.S3.HardCoreHolomorphic.OccupationConcentration
