/- GID: D5/S3/StatisticalMechanics/HardCore/GibbsOccupation
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/GibbsOccupation
   mirror-E: none(waiver:actual-finite-Gibbs-law-and-response)
   anchors: []
   utility: none
   digest: The actual independent-set Gibbs PMF realizes occupation moments and fluctuation response. -/

import D5.S3.StatisticalMechanics.HardCore.OccupationMoments
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.StatisticalMechanics.HardCore.GibbsOccupation

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open D5.S3.StatisticalMechanics.HardCore.OccupationMoments

variable {α : Type*} [DecidableEq α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

/-- Actual normalized Gibbs mass. Configurations outside the finite independent
family have zero mass. Its probability properties are proved for lambda >= 0. -/
def gibbsMass (V : Finset α) (lam : ℝ) (S : Finset α) : ℝ :=
  if S ∈ configurations G V then
    lam ^ S.card / partition G V (fun _ => lam) else 0

private theorem partition_pos (V : Finset α) (lam : ℝ) (hlam : 0 ≤ lam) :
    0 < partition G V (fun _ => lam) :=
  lt_of_lt_of_le zero_lt_one (one_le_partition G V (fun _ => lam) (fun _ _ => hlam))

/-- All actual masses are nonnegative, including the zero-activity endpoint. -/
theorem gibbs_mass_nonneg (V : Finset α) (lam : ℝ) (hlam : 0 ≤ lam) (S : Finset α) :
    0 ≤ gibbsMass G V lam S := by
  unfold gibbsMass
  split_ifs
  · exact div_nonneg (pow_nonneg hlam _) (partition_pos G V lam hlam).le
  · exact le_rfl

/-- Exact normalized raw moments, before imposing positivity or a probability
interpretation. The normalization denominator is the actual partition. -/
theorem mass_moment_eq (V : Finset α) (lam : ℝ) (k : ℕ) :
    (∑ S ∈ configurations G V, gibbsMass G V lam S * (S.card : ℝ) ^ k) =
      moment G V k lam / partition G V (fun _ => lam) := by
  rw [moment, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [gibbsMass, if_pos hS]
  ring

/-- The complete family of actual configurations has total probability one. -/
theorem gibbs_mass_sum (V : Finset α) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∑ S ∈ configurations G V, gibbsMass G V lam S) = 1 := by
  have h := mass_moment_eq G V lam 0
  simpa only [pow_zero, mul_one, moment_zero_order,
    div_self (ne_of_gt (partition_pos G V lam hlam))] using h

/-- The Gibbs law is a standard Mathlib PMF on actual finite vertex sets.
The ambient graph need not be finite. No external probability oracle is used. -/
def gibbsPMF (V : Finset α) (lam : ℝ) (hlam : 0 ≤ lam) : PMF (Finset α) :=
  PMF.ofFinset (fun S => ENNReal.ofReal (gibbsMass G V lam S)) (configurations G V)
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun S _ => gibbs_mass_nonneg G V lam hlam S),
        gibbs_mass_sum G V lam hlam]
      norm_num)
    (by intro S hS; simp [gibbsMass, hS])

/-- The real-valued point masses of the actual PMF equal the normalized weights. -/
theorem gibbs_pmf_toReal (V : Finset α) (lam : ℝ) (hlam : 0 ≤ lam) (S : Finset α) :
    (gibbsPMF G V lam hlam S).toReal = gibbsMass G V lam S := by
  simp only [gibbsPMF, PMF.ofFinset_apply,
    ENNReal.toReal_ofReal (gibbs_mass_nonneg G V lam hlam S)]

/-- Mean particle number, subsequently identified with the actual PMF sum. -/
def meanOccupation (V : Finset α) (lam : ℝ) : ℝ :=
  moment G V 1 lam / partition G V (fun _ => lam)

/-- The finite expectation of configuration cardinality under the actual PMF
is exactly the first normalized occupation moment. -/
theorem gibbs_expected_card (V : Finset α) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∑ S ∈ configurations G V, (gibbsPMF G V lam hlam S).toReal * (S.card : ℝ)) =
      meanOccupation G V lam := by
  simp_rw [gibbs_pmf_toReal]
  exact (by simpa only [pow_one, meanOccupation] using mass_moment_eq G V lam 1)

/-- The actual probability that a marked vertex is occupied equals one minus
the actual vacancy ratio. A vertex outside V has occupancy zero automatically. -/
theorem gibbs_vertex_occupied (V : Finset α) (v : α) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∑ S ∈ configurations G V,
      if v ∈ S then (gibbsPMF G V lam hlam S).toReal else 0) =
      1 - partition G (V.erase v) (fun _ => lam) / partition G V (fun _ => lam) := by
  have hsum : (∑ S ∈ configurations G V,
      if v ∈ S then (gibbsPMF G V lam hlam S).toReal else 0) =
      (∑ S ∈ configurations G V, if v ∈ S then lam ^ S.card else 0) /
        partition G V (fun _ => lam) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro S hS
    rw [gibbs_pmf_toReal]
    simp only [gibbsMass, if_pos hS]
    by_cases hv : v ∈ S <;> simp [hv]
  rw [hsum]
  have he := occupied_weight_add_erased G V v (fun _ => lam)
  simp only [Finset.prod_const] at he
  have he' := eq_sub_iff_add_eq.mpr he
  rw [he']
  field_simp [ne_of_gt (partition_pos G V lam hlam)]

/-- Expected occupation is the sum of actual one-vertex occupancies. No
independence among these Bernoulli indicators is assumed. -/
theorem mean_eq_sum_vacancies (V : Finset α) (lam : ℝ) (hlam : 0 ≤ lam) :
    meanOccupation G V lam =
      ∑ v ∈ V, (1 - partition G (V.erase v) (fun _ => lam) / partition G V (fun _ => lam)) := by
  rw [meanOccupation, moment_one_eq_deletions, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  field_simp [ne_of_gt (partition_pos G V lam hlam)]

/-- The mean lies between zero and the actual number of available vertices. -/
theorem mean_occupation_bounds (V : Finset α) (lam : ℝ) (hlam : 0 ≤ lam) :
    0 ≤ meanOccupation G V lam ∧ meanOccupation G V lam ≤ V.card := by
  have hm : meanOccupation G V lam =
      ∑ S ∈ configurations G V, gibbsMass G V lam S * (S.card : ℝ) := by
    simpa only [pow_one, meanOccupation] using (mass_moment_eq G V lam 1).symm
  rw [hm]
  refine ⟨Finset.sum_nonneg (fun S _ => mul_nonneg (gibbs_mass_nonneg G V lam hlam S)
    (Nat.cast_nonneg _)), ?_⟩
  calc
    _ ≤ ∑ S ∈ configurations G V, gibbsMass G V lam S * (V.card : ℝ) := by
      apply Finset.sum_le_sum
      intro S hS
      have hsub : S ⊆ V := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_le_card hsub)
        (gibbs_mass_nonneg G V lam hlam S)
    _ = V.card := by rw [← Finset.sum_mul, gibbs_mass_sum G V lam hlam, one_mul]

/-- Centered second moment under the same actual Gibbs weights. -/
def occupationVariance (V : Finset α) (lam : ℝ) : ℝ :=
  ∑ S ∈ configurations G V,
    gibbsMass G V lam S * ((S.card : ℝ) - meanOccupation G V lam) ^ 2

/-- The centered second moment equals the conventional finite PMF variance. -/
theorem gibbs_variance (V : Finset α) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∑ S ∈ configurations G V, (gibbsPMF G V lam hlam S).toReal *
      ((S.card : ℝ) - meanOccupation G V lam) ^ 2) = occupationVariance G V lam := by
  simp only [gibbs_pmf_toReal, occupationVariance]

/-- Expansion of the actual centered variance into its first two raw moments. -/
theorem variance_eq_moments (V : Finset α) (lam : ℝ) (hlam : 0 ≤ lam) :
    occupationVariance G V lam =
      moment G V 2 lam / partition G V (fun _ => lam) - (meanOccupation G V lam) ^ 2 := by
  have h0 := gibbs_mass_sum G V lam hlam
  have h1 := mass_moment_eq G V lam 1
  have h2 := mass_moment_eq G V lam 2
  simp only [pow_one] at h1
  change (∑ S ∈ configurations G V, gibbsMass G V lam S * (S.card : ℝ)) =
    meanOccupation G V lam at h1
  calc
    _ = (∑ S ∈ configurations G V, gibbsMass G V lam S * (S.card : ℝ) ^ 2) -
        2 * meanOccupation G V lam *
          (∑ S ∈ configurations G V, gibbsMass G V lam S * (S.card : ℝ)) +
        (meanOccupation G V lam) ^ 2 * (∑ S ∈ configurations G V, gibbsMass G V lam S) := by
      unfold occupationVariance
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = _ := by rw [h0, h1, h2]; ring

/-- Nonnegativity is proved from squared centered deviations and actual
nonnegative masses, not postulated from the derivative formula. -/
theorem occupation_variance_nonneg (V : Finset α) (lam : ℝ) (hlam : 0 ≤ lam) :
    0 ≤ occupationVariance G V lam :=
  Finset.sum_nonneg (fun S _ => mul_nonneg (gibbs_mass_nonneg G V lam hlam S) (sq_nonneg _))

/-- Exact fluctuation-response identity. The factor lambda preserves the
zero-activity endpoint and expresses differentiation in log activity. -/
theorem mean_occupation_fluctuation_response (V : Finset α) (lam : ℝ) (hlam : 0 ≤ lam) :
    lam * deriv (meanOccupation G V) lam = occupationVariance G V lam := by
  have hne : moment G V 0 lam ≠ 0 := by
    rw [moment_zero_order]
    exact ne_of_gt (partition_pos G V lam hlam)
  have h := normalized_moment_response G V 1 lam hne
  have hf : (fun t : ℝ => moment G V 1 t / moment G V 0 t) = meanOccupation G V := by
    funext t
    rw [moment_zero_order]
    rfl
  rw [hf] at h
  rw [variance_eq_moments G V lam hlam]
  simpa only [moment_zero_order, meanOccupation, pow_two] using h

/-- For positive activity the expected particle number has nonnegative
ordinary derivative, as a consequence of the proved fluctuation identity. -/
theorem mean_occupation_deriv_nonneg (V : Finset α) (lam : ℝ) (hlam : 0 < lam) :
    0 ≤ deriv (meanOccupation G V) lam := by
  have h := mean_occupation_fluctuation_response G V lam hlam.le
  have hn := occupation_variance_nonneg G V lam hlam.le
  by_contra hneg
  have hd : deriv (meanOccupation G V) lam < 0 := lt_of_not_ge hneg
  have hp := mul_neg_of_pos_of_neg hlam hd
  linarith

/-- The zero-activity mean and variance are both zero, with the empty
configuration still carrying unit mass. No limiting argument is needed. -/
theorem zero_activity_moments (V : Finset α) :
    meanOccupation G V 0 = 0 ∧ occupationVariance G V 0 = 0 := by
  have h1 : meanOccupation G V 0 = 0 := by
    simp only [meanOccupation, moment_succ_at_zero G V 0, zero_div]
  refine ⟨h1, ?_⟩
  rw [variance_eq_moments G V 0 (by norm_num), h1]
  have h2 : moment G V 2 (0 : ℝ) = 0 := moment_succ_at_zero G V 1
  rw [h2]
  norm_num

#print axioms gibbs_mass_sum
#print axioms gibbs_expected_card
#print axioms gibbs_vertex_occupied
#print axioms mean_occupation_fluctuation_response
#print axioms mean_occupation_deriv_nonneg

end D5.S3.StatisticalMechanics.HardCore.GibbsOccupation
