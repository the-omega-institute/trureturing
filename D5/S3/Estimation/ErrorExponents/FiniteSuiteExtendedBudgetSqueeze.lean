/- GID: D5/S3/Estimation/ErrorExponents/FiniteSuiteExtendedBudgetSqueeze
   generality: G
   mirror-B: D5/B/S3/Estimation/ErrorExponents/FiniteSuiteExtendedBudgetSqueeze
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite-suite Bayes error includes the zero-affinity infinite-budget endpoint. -/

import D5.S3.Estimation.ErrorExponents.FiniteSuiteErrorSqueeze
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Tactic

/- Library-search audit trail (2026-08-26):
   * The exact current-tree hit `FiniteSuiteErrorSqueeze` supplies the canonical
     `finiteSuiteOptimalError`; its theorem is not reused because its real-log budget
     requires a source-absent positivity premise.
   * Current-tree body-shape searches found no existing extended negative-log budget
     for `bhattacharyya (windowLaw p) (windowLaw q)` and no zero-aware real decay map.
     The sibling `ChernoffInformationZeroCriterion` establishes the canonical extended
     logarithm shape `-ENNReal.log (ENNReal.ofReal coefficient)`.
   * Pinned Mathlib has `ENNReal.log_zero`, `ENNReal.log_ofReal_of_pos`, and
     `Real.exp_log`, but no statistical Bhattacharyya testing-error squeeze.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.ErrorExponents.FiniteSuiteExtendedBudgetSqueeze

open D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy
open D5.S3.Estimation.ErrorExponents.FiniteSuiteErrorSqueeze
open D5.S3.Estimation.LeCam
open D5.S3.Estimation.LeCamTight
open D5.S3.TotalVariation.Bhattacharyya
open D5.S3.TotalVariation.Hellinger
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker

/-- The extended Bhattacharyya budget of the canonical finite joint law.
It is `top` exactly at zero joint affinity. -/
noncomputable def finiteSuiteExtendedBhattacharyyaBudget
    {Index Outcome : Type*} [Fintype Index] [DecidableEq Index] [Fintype Outcome]
    (p q : Index -> Outcome -> ℝ) : EReal := by
  classical
  exact -ENNReal.log
    (ENNReal.ofReal (bhattacharyya (windowLaw p) (windowLaw q)))

/-- The real decay represented by an extended evidence budget, with infinite
budget mapped to zero. -/
noncomputable def bhattacharyyaBudgetDecay (budget : EReal) : ℝ :=
  if budget = ⊤ then 0 else Real.exp (-budget.toReal)

private theorem finiteSuiteOptimalError_eq
    {Index Outcome : Type*} [Fintype Index] [DecidableEq Index] [Fintype Outcome]
    (p q : Index -> Outcome -> ℝ)
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
    let optimalEvent : Finset (Index -> Outcome) :=
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

private theorem budget_decay_eq_affinity
    {Index Outcome : Type*} [Fintype Index] [DecidableEq Index] [Fintype Outcome]
    (p q : Index -> Outcome -> ℝ) :
    bhattacharyyaBudgetDecay (finiteSuiteExtendedBhattacharyyaBudget p q) =
      bhattacharyya (windowLaw p) (windowLaw q) := by
  classical
  let rho := bhattacharyya (windowLaw p) (windowLaw q)
  change bhattacharyyaBudgetDecay (finiteSuiteExtendedBhattacharyyaBudget p q) = rho
  have hrhoNonnegative : 0 ≤ rho := by
    dsimp [rho]
    rw [bhattacharyya]
    exact Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  by_cases hrhoZero : rho = 0
  · simp [finiteSuiteExtendedBhattacharyyaBudget, bhattacharyyaBudgetDecay,
      rho, hrhoZero]
  · have hrhoPositive : 0 < rho := lt_of_le_of_ne hrhoNonnegative (Ne.symm hrhoZero)
    simp [finiteSuiteExtendedBhattacharyyaBudget, bhattacharyyaBudgetDecay,
      rho, ENNReal.log_ofReal_of_pos hrhoPositive,
      EReal.toReal_neg_eq, Real.exp_log hrhoPositive]

/-- The optimal equal-prior error of every finite independent suite obeys the
Bhattacharyya squeeze on an extended budget. No affinity-positivity premise is
needed: zero affinity gives infinite budget, zero decay, and zero optimal error. -/
theorem finite_suite_error_squeeze_extended
    {Index Outcome : Type*} [Fintype Index] [DecidableEq Index] [Fintype Outcome]
    (p q : Index -> Outcome -> ℝ)
    (hp : ∀ i, (∀ a, 0 ≤ p i a) ∧ ∑ a, p i a = 1)
    (hq : ∀ i, (∀ a, 0 ≤ q i a) ∧ ∑ a, q i a = 1) :
    (1 - Real.sqrt
        (1 - bhattacharyyaBudgetDecay
          (finiteSuiteExtendedBhattacharyyaBudget p q) ^ 2)) / 2 ≤
        finiteSuiteOptimalError p q ∧
      finiteSuiteOptimalError p q ≤
        bhattacharyyaBudgetDecay
          (finiteSuiteExtendedBhattacharyyaBudget p q) / 2 := by
  classical
  have hpw : (∀ u, 0 ≤ windowLaw p u) ∧ ∑ u, windowLaw p u = 1 :=
    ⟨fun u => Finset.prod_nonneg fun i _ => (hp i).1 (u i),
      windowLaw_sum_eq_one p fun i => (hp i).2⟩
  have hqw : (∀ u, 0 ≤ windowLaw q u) ∧ ∑ u, windowLaw q u = 1 :=
    ⟨fun u => Finset.prod_nonneg fun i _ => (hq i).1 (u i),
      windowLaw_sum_eq_one q fun i => (hq i).2⟩
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
  have hDecay := budget_decay_eq_affinity p q
  constructor
  · rw [hDecay, hOptimal]
    linarith
  · rw [hDecay, hOptimal]
    rw [hHellingerIdentity] at hHellinger
    linarith

#print axioms finiteSuiteExtendedBhattacharyyaBudget
#print axioms bhattacharyyaBudgetDecay
#print axioms finite_suite_error_squeeze_extended

end D5.S3.Estimation.ErrorExponents.FiniteSuiteExtendedBudgetSqueeze
