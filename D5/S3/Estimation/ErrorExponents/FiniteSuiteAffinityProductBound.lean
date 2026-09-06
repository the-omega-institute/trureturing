/- GID: D5/S3/Estimation/ErrorExponents/FiniteSuiteAffinityProductBound
   generality: G
   mirror-B: D5/B/S3/Estimation/ErrorExponents/FiniteSuiteAffinityProductBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Optimal equal-prior error of a finite independent suite is at most one half of the product of coordinate Bhattacharyya affinities, including zero-affinity endpoints. -/

import D5.S3.Estimation.ErrorExponents.FiniteSuiteExtendedBudgetSqueeze
import D5.S3.Entropy.NamingWindow.GreenClassWindowHellinger

/-!
# Finite-suite affinity product upper bound

The repository already owns the finite independent product law `windowLaw`,
exact Bhattacharyya multiplicativity for that product, and the zero-aware
extended-budget squeeze for the operational quantity `finiteSuiteOptimalError`.
This module exposes their direct composition:

`finiteSuiteOptimalError p q <= (prod_i BC(p_i,q_i)) / 2`.

Unlike the real-log budget theorem, no coordinate-affinity positivity premise
is required. A zero-affinity coordinate therefore correctly forces the upper
bound to zero. No new testing inequality, product law, or decision rule is
introduced here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.ErrorExponents.FiniteSuiteAffinityProductBound

open D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy
open D5.S3.Entropy.NamingWindow.GreenClassWindowHellinger
open D5.S3.Estimation.ErrorExponents.FiniteSuiteErrorSqueeze
open D5.S3.Estimation.ErrorExponents.FiniteSuiteExtendedBudgetSqueeze
open D5.S3.TotalVariation.Bhattacharyya

noncomputable section

/-- The zero-aware extended budget decays back to the exact joint
Bhattacharyya affinity. This public adapter exposes the identity needed by
later finite-suite clients without requiring positive coordinate affinities. -/
theorem finite_suite_budget_decay_eq_joint_affinity
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
  · have hrhoPositive : 0 < rho :=
      lt_of_le_of_ne hrhoNonnegative (Ne.symm hrhoZero)
    simp [finiteSuiteExtendedBhattacharyyaBudget, bhattacharyyaBudgetDecay,
      rho, ENNReal.log_ofReal_of_pos hrhoPositive,
      EReal.toReal_neg_eq, Real.exp_log hrhoPositive]

/-- Operational optimal equal-prior error is at most one half of the product
of the coordinate Bhattacharyya affinities. The statement includes the exact
zero-affinity endpoint. -/
theorem finite_suite_optimal_error_le_bhattacharyya_product
    {Index Outcome : Type*} [Fintype Index] [DecidableEq Index] [Fintype Outcome]
    (p q : Index -> Outcome -> ℝ)
    (hp : ∀ i, (∀ a, 0 ≤ p i a) ∧ ∑ a, p i a = 1)
    (hq : ∀ i, (∀ a, 0 ≤ q i a) ∧ ∑ a, q i a = 1) :
    finiteSuiteOptimalError p q ≤
      (∏ i, bhattacharyya (p i) (q i)) / 2 := by
  have hsqueeze := finite_suite_error_squeeze_extended p q hp hq
  have hdecay := finite_suite_budget_decay_eq_joint_affinity p q
  have hproduct :
      bhattacharyya (windowLaw p) (windowLaw q) =
        ∏ i, bhattacharyya (p i) (q i) :=
    bhattacharyya_windowLaw p q
      (fun i a => mul_nonneg ((hp i).1 a) ((hq i).1 a))
  rw [hdecay, hproduct] at hsqueeze
  exact hsqueeze.2

#print axioms finite_suite_budget_decay_eq_joint_affinity
#print axioms finite_suite_optimal_error_le_bhattacharyya_product

end
end D5.S3.Estimation.ErrorExponents.FiniteSuiteAffinityProductBound
