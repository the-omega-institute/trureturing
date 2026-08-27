/- GID: D5/S3/ConceptDynamics/DecisionValueScale/PublicGoodsDominanceWelfareContrast
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValueScale/PublicGoodsDominanceWelfareContrast
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Noncontribution strictly dominates while full contribution maximizes welfare. -/

import D5.S3.ConceptDynamics.DecisionValue.ContributionIncentiveThreshold
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/- Library-search audit trail (2026-08-27):
   * Exact family hits `contributionLevel`, `aggregateContribution`, and
     `compensatedUtility` construct the source action, total contribution, and
     individual payoff; they are imported rather than redeclared.
   * The owner's compensation-threshold theorem makes contribution dominant
     above a transfer threshold. It does not state zero-compensation
     noncontribution dominance, aggregate welfare, or the social contrast.
   * Repository searches found no exact theorem with all four public clauses.
     Pinned Mathlib provides finite subtype-sum partitioning and ordered finite
     sums, but no public-goods theorem. No new definition or abbreviation is
     introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

noncomputable section

namespace D5.S3.ConceptDynamics.DecisionValueScale.PublicGoodsDominanceWelfareContrast

open D5.S3.ConceptDynamics.DecisionValue.ContributionIncentiveThreshold

/-- Under `benefit > cost > benefit / n`, every agent strictly prefers
noncontribution for every profile. Nevertheless, the sum of those same
individual utilities equals `(benefit - cost)` times total contribution, is
maximized by unanimous contribution, and strictly exceeds unanimous
noncontribution there. -/
theorem public_goods_dominance_welfare_contrast
    (n : Nat) (hn : 2 <= n) (benefit cost : Real)
    (sociallyBeneficial : cost < benefit)
    (privatelyCostly : benefit / (n : Real) < cost) :
    (forall (agent : Fin n) (actions : Fin n -> Bool),
      compensatedUtility benefit cost 0 agent
          (Function.update actions agent true) <
        compensatedUtility benefit cost 0 agent
          (Function.update actions agent false)) ∧
    (forall actions : Fin n -> Bool,
      (∑ agent : Fin n,
          compensatedUtility benefit cost 0 agent actions) =
        (benefit - cost) *
          ∑ agent : Fin n, contributionLevel (actions agent)) ∧
    (forall actions : Fin n -> Bool,
      (∑ agent : Fin n,
          compensatedUtility benefit cost 0 agent actions) <=
        ∑ agent : Fin n,
          compensatedUtility benefit cost 0 agent (fun _ => true)) ∧
    ((∑ agent : Fin n,
        compensatedUtility benefit cost 0 agent (fun _ => false)) <
      ∑ agent : Fin n,
        compensatedUtility benefit cost 0 agent (fun _ => true)) := by
  classical
  have nPositive : 0 < n := lt_of_lt_of_le (by decide) hn
  have nRealNonzero : (n : Real) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt nPositive
  have nRealPositive : (0 : Real) < (n : Real) := by
    exact_mod_cast nPositive
  have aggregate_update (agent : Fin n) (actions : Fin n -> Bool)
      (action : Bool) :
      aggregateContribution agent (Function.update actions agent action) =
        contributionLevel action +
          ∑ other : {other : Fin n // other ≠ agent},
            contributionLevel (actions other) := by
    unfold aggregateContribution
    rw [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro other _
    simp [Function.update, other.property]
  have utility_difference (agent : Fin n) (actions : Fin n -> Bool) :
      compensatedUtility benefit cost 0 agent
            (Function.update actions agent true) -
          compensatedUtility benefit cost 0 agent
            (Function.update actions agent false) =
        benefit / (n : Real) - cost := by
    rw [compensatedUtility, compensatedUtility,
      aggregate_update, aggregate_update]
    simp [contributionLevel]
    ring
  have aggregate_eq_total (agent : Fin n) (actions : Fin n -> Bool) :
      aggregateContribution agent actions =
        ∑ other : Fin n, contributionLevel (actions other) := by
    have othersSum :
        (∑ other : {other : Fin n // other ≠ agent},
            contributionLevel (actions other)) =
          ∑ other ∈ Finset.univ.erase agent,
            contributionLevel (actions other) := by
      symm
      apply Finset.sum_subtype
      intro other
      simp
    unfold aggregateContribution
    rw [othersSum, add_comm]
    exact Finset.sum_erase_add Finset.univ
      (fun other => contributionLevel (actions other))
      (Finset.mem_univ agent)
  have welfare_formula (actions : Fin n -> Bool) :
      (∑ agent : Fin n,
          compensatedUtility benefit cost 0 agent actions) =
        (benefit - cost) *
          ∑ agent : Fin n, contributionLevel (actions agent) := by
    simp_rw [compensatedUtility, aggregate_eq_total]
    simp only [zero_mul, add_zero, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    rw [← mul_assoc, mul_div_cancel₀ benefit nRealNonzero]
    ring
  constructor
  · intro agent actions
    have difference := utility_difference agent actions
    linarith
  constructor
  · exact welfare_formula
  constructor
  · intro actions
    rw [welfare_formula, welfare_formula]
    have contributionCountBound :
        (∑ agent : Fin n, contributionLevel (actions agent)) <=
          ∑ _agent : Fin n, (1 : Real) := by
      apply Finset.sum_le_sum
      intro agent _
      cases actions agent <;> simp [contributionLevel]
    have coefficientNonnegative : 0 <= benefit - cost :=
      (sub_pos.mpr sociallyBeneficial).le
    simpa [contributionLevel] using
      mul_le_mul_of_nonneg_left contributionCountBound coefficientNonnegative
  · rw [welfare_formula, welfare_formula]
    simpa [contributionLevel] using
      mul_pos (sub_pos.mpr sociallyBeneficial) nRealPositive

#print axioms public_goods_dominance_welfare_contrast

end D5.S3.ConceptDynamics.DecisionValueScale.PublicGoodsDominanceWelfareContrast
