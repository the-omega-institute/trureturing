/- GID: D5/S3/ConceptDynamics/DecisionValue/ContributionIncentiveThreshold
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValue/ContributionIncentiveThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Binary contribution is dominant exactly at the source compensation threshold. -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/- Library-search audit trail (2026-08-21):
   * Repository searches found no exact contribution-compensation threshold or
     weak/strict strategy-dominance theorem. Adjacent incentive and analytic
     dominance modules concern different source objects.
   * Pinned Mathlib searches for `WeaklyDominant`, `StrictlyDominant`,
     `DominantStrategy`, and case variants were exact misses.
   * Generic finite-sum update support includes `Finset.sum_update_of_mem`, but
     no result packages the source payoff construction and all three clauses.
   * The proof uses pinned Mathlib's `linarith` and `ring` directly after
     calculating the payoff difference from the source utility.
   * `loogle` and `leansearch` executables are absent from PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

noncomputable section

namespace D5.S3.ConceptDynamics.DecisionValue.ContributionIncentiveThreshold

/-- The numerical level of one source action in the binary contribution
channel. -/
def contributionLevel (action : Bool) : Real :=
  if action then 1 else 0

/-- The source aggregate contribution, split into the selected agent's action
and the finite sum over all other agents. -/
def aggregateContribution {n : Nat} (agent : Fin n)
    (actions : Fin n -> Bool) : Real :=
  contributionLevel (actions agent) +
    ∑ other : {other : Fin n // other ≠ agent},
      contributionLevel (actions other)

/-- The source compensated utility: common benefit from every contribution,
minus the selected contributor's cost, plus that contributor's compensation. -/
def compensatedUtility {n : Nat} (benefit cost compensation : Real)
    (agent : Fin n) (actions : Fin n -> Bool) : Real :=
  benefit / (n : Real) * aggregateContribution agent actions -
    cost * contributionLevel (actions agent) +
    compensation * contributionLevel (actions agent)

/-- Contribution is weakly dominant when every agent weakly prefers its
contribution update for every binary action profile. -/
def contributionWeaklyDominant
    (n : Nat) (benefit cost compensation : Real) : Prop :=
  ∀ (agent : Fin n) (actions : Fin n -> Bool),
    compensatedUtility benefit cost compensation agent
        (Function.update actions agent false) ≤
      compensatedUtility benefit cost compensation agent
        (Function.update actions agent true)

/-- Contribution is strictly dominant when every agent strictly prefers its
contribution update for every binary action profile. -/
def contributionStrictlyDominant
    (n : Nat) (benefit cost compensation : Real) : Prop :=
  ∀ (agent : Fin n) (actions : Fin n -> Bool),
    compensatedUtility benefit cost compensation agent
        (Function.update actions agent false) <
      compensatedUtility benefit cost compensation agent
        (Function.update actions agent true)

private lemma aggregateContribution_update {n : Nat} (agent : Fin n)
    (actions : Fin n -> Bool) (action : Bool) :
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

private lemma compensatedUtility_contribution_difference {n : Nat}
    (benefit cost compensation : Real) (agent : Fin n)
    (actions : Fin n -> Bool) :
    compensatedUtility benefit cost compensation agent
          (Function.update actions agent true) -
        compensatedUtility benefit cost compensation agent
          (Function.update actions agent false) =
      benefit / (n : Real) - cost + compensation := by
  rw [compensatedUtility, compensatedUtility,
    aggregateContribution_update, aggregateContribution_update]
  simp [contributionLevel]
  ring

private lemma contributionWeaklyDominant_iff {n : Nat} (hn : 2 ≤ n)
    (benefit cost compensation : Real) :
    contributionWeaklyDominant n benefit cost compensation ↔
      cost - benefit / (n : Real) ≤ compensation := by
  constructor
  · intro hdominant
    let agent : Fin n := ⟨0, lt_of_lt_of_le (by decide) hn⟩
    have hpayoff := hdominant agent (fun _ => false)
    have hdifference := compensatedUtility_contribution_difference
      benefit cost compensation agent (fun _ => false)
    linarith
  · intro hthreshold agent actions
    have hdifference := compensatedUtility_contribution_difference
      benefit cost compensation agent actions
    linarith

private lemma contributionStrictlyDominant_iff {n : Nat} (hn : 2 ≤ n)
    (benefit cost compensation : Real) :
    contributionStrictlyDominant n benefit cost compensation ↔
      cost - benefit / (n : Real) < compensation := by
  constructor
  · intro hdominant
    let agent : Fin n := ⟨0, lt_of_lt_of_le (by decide) hn⟩
    have hpayoff := hdominant agent (fun _ => false)
    have hdifference := compensatedUtility_contribution_difference
      benefit cost compensation agent (fun _ => false)
    linarith
  · intro hthreshold agent actions
    have hdifference := compensatedUtility_contribution_difference
      benefit cost compensation agent actions
    linarith

/-- Under the source restrictions `n ≥ 2` and `b > c > b / n`, weak
dominance occurs exactly at the threshold, strict dominance occurs above it,
and the threshold is the least compensation inducing weak dominance. -/
theorem contribution_incentive_threshold
    (n : Nat) (hn : 2 ≤ n) (benefit cost compensation : Real)
    (sociallyBeneficial : cost < benefit)
    (privatelyCostly : benefit / (n : Real) < cost) :
    (contributionWeaklyDominant n benefit cost compensation ↔
      cost - benefit / (n : Real) ≤ compensation) ∧
    (cost - benefit / (n : Real) < compensation →
      contributionStrictlyDominant n benefit cost compensation) ∧
    IsLeast
      {candidate : Real |
        contributionWeaklyDominant n benefit cost candidate}
      (cost - benefit / (n : Real)) := by
  have _socialDirection : 0 < benefit - cost := sub_pos.mpr sociallyBeneficial
  have _privateGap : 0 < cost - benefit / (n : Real) := sub_pos.mpr privatelyCostly
  constructor
  · exact contributionWeaklyDominant_iff hn benefit cost compensation
  constructor
  · intro hstrict
    exact (contributionStrictlyDominant_iff hn benefit cost compensation).2 hstrict
  · constructor
    · exact (contributionWeaklyDominant_iff hn benefit cost
        (cost - benefit / (n : Real))).2 le_rfl
    · intro candidate hcandidate
      exact (contributionWeaklyDominant_iff hn benefit cost candidate).1 hcandidate

/-- The public source restrictions and the threshold have a concrete binary
two-agent model. -/
example : contributionWeaklyDominant 2 4 3 1 := by
  have hresult := contribution_incentive_threshold 2 (by norm_num) 4 3 1
    (by norm_num) (by norm_num)
  exact hresult.1.2 (by norm_num)

#print axioms contribution_incentive_threshold

end D5.S3.ConceptDynamics.DecisionValue.ContributionIncentiveThreshold
