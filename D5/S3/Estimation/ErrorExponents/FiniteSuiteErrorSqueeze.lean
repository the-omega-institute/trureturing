/- GID: D5/S3/Estimation/ErrorExponents/FiniteSuiteErrorSqueeze
   generality: G
   mirror-B: D5/B/S3/Estimation/ErrorExponents/FiniteSuiteErrorSqueeze
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite independent-suite Bayes error is squeezed by its affinity budget. -/

import D5.S3.Entropy.NamingWindow.GreenClassWindowHellinger
import D5.S3.Estimation.LeCamTight
import Mathlib.Tactic

/- Library-search audit trail (2026-08-26):
   * The current-tree search found the canonical independent joint law `windowLaw`
     and its frozen affinity product theorem `bhattacharyya_windowLaw`.
   * `LeCamTight.le_cam_two_point_sum_tight` supplies the attaining finite test,
     while the frozen Bhattacharyya and Hellinger comparisons supply the two bounds.
   * Body-shape searches found no existing finite minimum of equal-prior test risk
     and no negative sum of logarithmic coordinate affinities.
   * Pinned Mathlib searches found no statistical Bhattacharyya testing bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.ErrorExponents.FiniteSuiteErrorSqueeze

open D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy
open D5.S3.Entropy.NamingWindow.GreenClassWindowHellinger
open D5.S3.Estimation.LeCam
open D5.S3.Estimation.LeCamTight
open D5.S3.TotalVariation.Bhattacharyya
open D5.S3.TotalVariation.Hellinger
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker

/-- The equal-prior binary error of a concrete decision event. -/
noncomputable def equalPriorError {Outcome : Type*} [Fintype Outcome]
    (p q : Outcome → ℝ) (acceptSecond : Finset Outcome) : ℝ := by
  classical
  exact ((∑ z ∈ acceptSecond, p z) + ∑ z ∈ acceptSecondᶜ, q z) / 2

/-- The optimal equal-prior error over all decisions on an independent finite suite. -/
noncomputable def finiteSuiteOptimalError
    {Index Outcome : Type*} [Fintype Index] [DecidableEq Index] [Fintype Outcome]
    (p q : Index → Outcome → ℝ) : ℝ := by
  classical
  exact
    (Finset.univ.image (fun acceptSecond : Finset (Index → Outcome) =>
      equalPriorError (windowLaw p) (windowLaw q) acceptSecond)).min' (by simp)

/-- The negative logarithmic sum of the suite's coordinate affinities. -/
noncomputable def finiteSuiteBhattacharyyaBudget
    {Index Outcome : Type*} [Fintype Index] [Fintype Outcome]
    (p q : Index → Outcome → ℝ) : ℝ :=
  -∑ i, Real.log (bhattacharyya (p i) (q i))

private theorem finiteSuiteOptimalError_eq
    {Index Outcome : Type*} [Fintype Index] [DecidableEq Index] [Fintype Outcome]
    (p q : Index → Outcome → ℝ)
    (hp : ∀ i, (∀ a, 0 ≤ p i a) ∧ ∑ a, p i a = 1)
    (hq : ∀ i, (∀ a, 0 ≤ q i a) ∧ ∑ a, q i a = 1) :
    finiteSuiteOptimalError p q =
      (1 - totalVariation (windowLaw p) (windowLaw q)) / 2 := by
  classical
  have hpw : (∀ u, 0 ≤ windowLaw p u) ∧ ∑ u, windowLaw p u = 1 :=
    ⟨fun u => Finset.prod_nonneg fun i _ => (hp i).1 (u i),
      windowLaw_sum_eq_one p fun i => (hp i).2⟩
  have hqw : (∀ u, 0 ≤ windowLaw q u) ∧ ∑ u, windowLaw q u = 1 :=
    ⟨fun u => Finset.prod_nonneg fun i _ => (hq i).1 (u i),
      windowLaw_sum_eq_one q fun i => (hq i).2⟩
  unfold finiteSuiteOptimalError
  apply le_antisymm
  · apply Finset.min'_le
    apply Finset.mem_image.mpr
    let optimalEvent : Finset (Index → Outcome) :=
      Finset.univ.filter (fun z => windowLaw p z ≤ windowLaw q z)
    refine ⟨optimalEvent, Finset.mem_univ _, ?_⟩
    unfold equalPriorError
    rw [le_cam_two_point_sum_tight (windowLaw p) (windowLaw q)
      (hpw.2.trans hqw.2.symm) hqw.2]
  · apply Finset.le_min'
    intro risk hRisk
    rcases Finset.mem_image.mp hRisk with ⟨acceptSecond, _, rfl⟩
    have hLower := le_cam_two_point_sum (windowLaw p) (windowLaw q)
      acceptSecond (hpw.2.trans hqw.2.symm) hqw.2
    unfold equalPriorError
    linarith

/-- For independent finite coordinates with positive local affinities, the
optimal equal-prior error is bounded below and above by the suite's accumulated
Bhattacharyya evidence budget. -/
theorem finite_suite_error_squeeze
    {Index Outcome : Type*} [Fintype Index] [DecidableEq Index] [Fintype Outcome]
    (p q : Index → Outcome → ℝ)
    (hp : ∀ i, (∀ a, 0 ≤ p i a) ∧ ∑ a, p i a = 1)
    (hq : ∀ i, (∀ a, 0 ≤ q i a) ∧ ∑ a, q i a = 1)
    (hAffinityPositive : ∀ i, 0 < bhattacharyya (p i) (q i)) :
    (1 - Real.sqrt
        (1 - Real.exp (-2 * finiteSuiteBhattacharyyaBudget p q))) / 2 ≤
        finiteSuiteOptimalError p q ∧
      finiteSuiteOptimalError p q ≤
        Real.exp (-finiteSuiteBhattacharyyaBudget p q) / 2 := by
  classical
  have hpw : (∀ u, 0 ≤ windowLaw p u) ∧ ∑ u, windowLaw p u = 1 :=
    ⟨fun u => Finset.prod_nonneg fun i _ => (hp i).1 (u i),
      windowLaw_sum_eq_one p fun i => (hp i).2⟩
  have hqw : (∀ u, 0 ≤ windowLaw q u) ∧ ∑ u, windowLaw q u = 1 :=
    ⟨fun u => Finset.prod_nonneg fun i _ => (hq i).1 (u i),
      windowLaw_sum_eq_one q fun i => (hq i).2⟩
  have hAffinity :
      bhattacharyya (windowLaw p) (windowLaw q) =
        Real.exp (-finiteSuiteBhattacharyyaBudget p q) := by
    rw [bhattacharyya_windowLaw p q
      (fun i a => mul_nonneg ((hp i).1 a) ((hq i).1 a))]
    rw [finiteSuiteBhattacharyyaBudget, neg_neg, Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => (Real.exp_log (hAffinityPositive i)).symm
  have hAffinitySquare :
      Real.exp (-2 * finiteSuiteBhattacharyyaBudget p q) =
        bhattacharyya (windowLaw p) (windowLaw q) ^ 2 := by
    calc
      Real.exp (-2 * finiteSuiteBhattacharyyaBudget p q) =
          Real.exp (-finiteSuiteBhattacharyyaBudget p q) *
            Real.exp (-finiteSuiteBhattacharyyaBudget p q) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ = bhattacharyya (windowLaw p) (windowLaw q) ^ 2 := by
        rw [← hAffinity]
        ring
  have hOptimal := finiteSuiteOptimalError_eq p q hp hq
  have hVariationSquare :=
    total_variation_sq_le_one_sub_bhattacharyya_sq
      (windowLaw p) (windowLaw q) hpw hqw
  have hAffinityNonnegative :
      0 ≤ bhattacharyya (windowLaw p) (windowLaw q) := by
    rw [bhattacharyya]
    exact Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  have hAffinityAtMostOne :=
    bhattacharyya_le_one (windowLaw p) (windowLaw q) hpw hqw
  have hRadicand :
      0 ≤ 1 - bhattacharyya (windowLaw p) (windowLaw q) ^ 2 := by
    nlinarith
  have hVariation :
      totalVariation (windowLaw p) (windowLaw q) ≤
        Real.sqrt (1 - bhattacharyya (windowLaw p) (windowLaw q) ^ 2) := by
    apply (Real.le_sqrt (total_variation_nonneg _ _) hRadicand).2
    exact hVariationSquare
  have hHellinger :=
    hellinger_sq_div_two_le_total_variation (windowLaw p) (windowLaw q)
  have hHellingerIdentity :=
    hellinger_sq_eq_two_sub (windowLaw p) (windowLaw q) hpw hqw
  constructor
  · rw [hAffinitySquare, hOptimal]
    linarith
  · rw [hOptimal, ← hAffinity]
    rw [hHellingerIdentity] at hHellinger
    linarith

#print axioms finite_suite_error_squeeze

end D5.S3.Estimation.ErrorExponents.FiniteSuiteErrorSqueeze
