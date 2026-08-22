/- GID: D5/S3/ConceptDynamics/DecisionValue/ThresholdPublicGoodDualEquilibria
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValue/ThresholdPublicGoodDualEquilibria
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove the two unanimous equilibria of an all-or-nothing public good. -/

import D5.S3.ConceptDynamics.DecisionValue.ContributionIncentiveThreshold

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.DecisionValue.ThresholdPublicGoodDualEquilibria

open D5.S3.ConceptDynamics.DecisionValue.ContributionIncentiveThreshold

/- Library-search audit trail (2026-08-22):
   * The frozen family declaration `contributionLevel` is an exact hit for the
     source's Boolean contribution action and is reused directly.
   * Repository searches found no all-or-nothing public-good equilibrium theorem.
   * Pinned Mathlib searches for `IsNash`, `NashEquilibrium`, and case variants
     found no game-theory predicate. `Fin.nontrivial_iff_two_le`, `exists_ne`,
     and `Function.update_self` supply the finite-agent deviation steps. -/

/-- The all-or-nothing public good succeeds exactly when every agent contributes. -/
def allContribute {n : Nat} (actions : Fin n -> Bool) : Prop :=
  ∀ agent, actions agent = true

/-- The source payoff: every agent receives the benefit exactly on success,
while each contributor pays the contribution cost in either outcome. -/
noncomputable def thresholdUtility {n : Nat} (benefit cost : Real)
    (agent : Fin n) (actions : Fin n -> Bool) : Real := by
  classical
  exact (if allContribute actions then benefit else 0) -
    cost * contributionLevel (actions agent)

/-- A profile is Nash-stable when no agent improves its source payoff by a
unilateral Boolean action update. -/
def nashStable {n : Nat} (benefit cost : Real)
    (actions : Fin n -> Bool) : Prop :=
  ∀ (agent : Fin n) (alternative : Bool),
    thresholdUtility benefit cost agent
        (Function.update actions agent alternative) ≤
      thresholdUtility benefit cost agent actions

/--
For at least two agents and source parameters `b > c > 0`, both unanimous
contribution and unanimous noncontribution are Nash-stable profiles.
-/
theorem threshold_public_good_dual_equilibria
    (n : Nat) (hn : 2 ≤ n) (benefit cost : Real)
    (hbenefit : cost < benefit) (hcost : 0 < cost) :
    nashStable benefit cost (fun _ : Fin n => true) ∧
      nashStable benefit cost (fun _ : Fin n => false) := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  constructor
  · intro agent alternative
    by_cases halternative : alternative = true
    · subst alternative
      simp [thresholdUtility, allContribute, contributionLevel]
    · have halternativeFalse : alternative = false :=
        Bool.eq_false_of_not_eq_true halternative
      subst alternative
      simp only [thresholdUtility, Function.update_self,
        contributionLevel, Bool.false_eq_true, ↓reduceIte]
      have hsuccess : allContribute (fun _ : Fin n => true) := by
        intro i
        rfl
      have hfailure : ¬ allContribute
          (Function.update (fun _ : Fin n => true) agent false) := by
        intro hall
        simpa using hall agent
      rw [if_pos hsuccess, if_neg hfailure]
      simp [hbenefit.le]
  · intro agent alternative
    by_cases halternative : alternative = false
    · subst alternative
      simp [thresholdUtility, allContribute, contributionLevel]
    · have halternativeTrue : alternative = true :=
        Bool.eq_true_of_not_eq_false halternative
      subst alternative
      obtain ⟨other, hother⟩ := exists_ne agent
      have hfailure : ¬ allContribute
          (Function.update (fun _ : Fin n => false) agent true) := by
        intro hall
        have hotherAction := hall other
        simp [Function.update, hother] at hotherAction
      have habstainFailure : ¬ allContribute (fun _ : Fin n => false) := by
        intro hall
        simpa using hall agent
      simp only [thresholdUtility, Function.update_self,
        contributionLevel, ↓reduceIte, Bool.false_eq_true]
      rw [if_neg hfailure, if_neg habstainFailure]
      linarith

#print axioms threshold_public_good_dual_equilibria

end D5.S3.ConceptDynamics.DecisionValue.ThresholdPublicGoodDualEquilibria
