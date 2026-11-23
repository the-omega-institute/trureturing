/- GID: D5/S3/Fourier/Concentration/LocalizedCollisionBudgets
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/LocalizedCollisionBudgets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pair reach and Euclidean scale bound weighted collisions under shared offsets. -/

import D5.S3.Fourier.Concentration.UniformPerturbationEuclidean

/-! Weighted collision budgets for uniform perturbations with a bound depending on the
unperturbed frequency difference and the scales of the individual coordinates. -/

set_option autoImplicit false

noncomputable section

open Finset MeasureTheory Set
open D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations
open D5.S3.Fourier.Concentration.UniformPerturbationEuclidean
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment (tailCollisionMass)
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialFrequency monomialWeight)
open scoped ENNReal

namespace D5.S3.Fourier.Concentration.LocalizedCollisionBudgets

private def countDifference {J : Type*} (m n : J → ℕ) (j : J) : ℝ :=
  (m j : ℝ) - (n j : ℝ)

/-- Drop a pair if its closed collision band cannot be reached from the base spectrum. -/
def localizedPairBound {J : Type*} [Fintype J] (g radius : J → ℝ)
    (η : ℝ) (m n : J → ℕ) : ℝ≥0∞ :=
  if |monomialFrequency g m - monomialFrequency g n| ≤
      η + ∑ j, |countDifference m n j| * radius j then
    min (min 1 (ENNReal.ofReal (η / pairRadius radius m n)))
      (ENNReal.ofReal (Real.exp (1 / 2) * Real.sqrt (15 * Real.pi / 2) * η /
        Real.sqrt (∑ j, (countDifference m n j * radius j) ^ 2)))
  else 0

/-- The weighted sum of these bounds over ordered, distinct degree-vector pairs. -/
def localizedExcessBound {J : Type*} [Fintype J] [DecidableEq J] (g w radius : J → ℝ)
    (p : ℕ) (η : ℝ) : ℝ≥0∞ :=
  weightedPairBudget w p (localizedPairBound g radius η)

private theorem pair_event_measure_le_localized {J : Type*} [Fintype J] (g radius : J → ℝ)
    (hradius : ∀ j, 0 < radius j) {m n : J → ℕ} (hmn : m ≠ n) {η : ℝ} (hη : 0 ≤ η) :
    (Measure.pi fun j => intervalNoise (radius j))
      {x | |monomialFrequency (fun j => g j + x j) m -
        monomialFrequency (fun j => g j + x j) n| ≤ η} ≤
      localizedPairBound g radius η m n := by
  let μ (j : J) := intervalNoise (radius j)
  let a := countDifference m n
  let b := monomialFrequency g m - monomialFrequency g n
  let A := ∑ j, |a j| * radius j
  let W : Set (J → ℝ) := {x | |monomialFrequency (fun j => g j + x j) m -
    monomialFrequency (fun j => g j + x j) n| ≤ η}
  have (j : J) : IsProbabilityMeasure (μ j) := intervalNoise_probability (hradius j)
  have hdiff (x : J → ℝ) :
      monomialFrequency (fun j => g j + x j) m -
        monomialFrequency (fun j => g j + x j) n = (∑ j, a j * x j) + b := by
    dsimp [b, monomialFrequency]
    rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl (fun j _ => by dsimp [a, countDifference]; ring)
  have hW : W = {x | |(∑ j, a j * x j) + b| ≤ η} := by
    ext x
    exact (congrArg (fun z : ℝ => |z| ≤ η) (hdiff x)).to_iff
  change Measure.pi μ W ≤ _
  unfold localizedPairBound
  change Measure.pi μ W ≤ if |b| ≤ η + A then _ else _
  split_ifs with hreach
  · refine le_min (pair_event_measure_le g radius hradius hmn) ?_
    have hS : 0 < ∑ j, (a j * radius j) ^ 2 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hmn
      have hreal : (m i : ℝ) ≠ (n i : ℝ) := by exact_mod_cast hi
      have hai : a i ≠ 0 := sub_ne_zero.mpr hreal
      exact sum_pos' (fun j _ => sq_nonneg (a j * radius j))
        ⟨i, mem_univ i, sq_pos_of_ne_zero (mul_ne_zero hai (hradius i).ne')⟩
    rw [hW]
    exact (intervalNoise_pi_affine_le_euclidean radius a hradius b hη hS).trans (min_le_right _ _)
  · suffices hnull : Measure.pi μ W = 0 from hnull.le
    apply measure_eq_zero_iff_ae_notMem.mpr
    have hbox : ∀ᵐ x ∂Measure.pi μ, ∀ j, x j ∈ Icc (-radius j) (radius j) := by
      apply ae_all_iff.mpr
      intro j
      apply (Measure.tendsto_eval_ae_ae (i := j)).eventually
      exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _
    filter_upwards [hbox] with x hx hhit
    have hsum : |∑ j, a j * x j| ≤ A := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_le.mpr (hx j)) (abs_nonneg _)
    have hband : |(∑ j, a j * x j) + b| ≤ η := by
      rwa [hW] at hhit
    refine hreach ?_
    calc
      |b| = |((∑ j, a j * x j) + b) - (∑ j, a j * x j)| := by rw [add_sub_cancel_left]
      _ ≤ |(∑ j, a j * x j) + b| + |∑ j, a j * x j| := abs_sub _ _
      _ ≤ η + A := add_le_add hband hsum

/-- Select a single nearby spectrum for all the localized collision budgets. -/
theorem exists_continuous_common_nearby_localized_bounds {J K : Type*} [DecidableEq J]
    [Countable J] [Countable K] (g radius : J → ℝ) (hradius : ∀ j, 0 < radius j)
    (support : K → Finset J) (w : ∀ k, support k → ℝ) (hw : ∀ k j, 0 ≤ w k j)
    (p : K → ℕ) (η budget : K → ℝ) (hη : ∀ k, 0 ≤ η k) (hbudget : ∀ k, 0 < budget k)
    (htotal : (∑' k, localizedExcessBound (fun j : support k => g j) (w k)
      (fun j : support k => radius j) (p k) (η k) / ENNReal.ofReal (budget k)) ≤ 1) :
    ∃ g' : J → ℝ, (∀ j, |g' j - g j| ≤ radius j) ∧
      (∑' k, ENNReal.ofReal (tailCollisionMass (fun j : support k => g' j) (w k) (p k) (η k) -
        ∑ m ∈ piAntidiag univ (p k), monomialWeight (w k) m ^ 2) / ENNReal.ofReal (budget k)) ≤
        (∑' k, localizedExcessBound (fun j : support k => g j) (w k)
          (fun j : support k => radius j) (p k) (η k) / ENNReal.ofReal (budget k)) ∧
      ∀ k, tailCollisionMass (fun j : support k => g' j) (w k) (p k) (η k) ≤
        (∑ m ∈ piAntidiag univ (p k), monomialWeight (w k) m ^ 2) + budget k := by
  let bound (k : K) := localizedPairBound (fun j : support k => g j)
    (fun j : support k => radius j) (η k)
  apply exists_continuous_common_nearby_bounds_of_pair_probabilities
    g radius hradius support w hw p η budget hη hbudget bound ?_ htotal
  intro k m n hmn
  exact pair_event_measure_le_localized (fun j : support k => g j)
    (fun j : support k => radius j) (fun j => hradius j) hmn (hη k)

#print axioms exists_continuous_common_nearby_localized_bounds

end D5.S3.Fourier.Concentration.LocalizedCollisionBudgets
