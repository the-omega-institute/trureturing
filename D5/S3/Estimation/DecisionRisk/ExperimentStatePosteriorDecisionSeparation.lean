/- GID: D5/S3/Estimation/DecisionRisk/ExperimentStatePosteriorDecisionSeparation
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/ExperimentStatePosteriorDecisionSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The law quotient is state-side, while posterior Bayes decisions are evidence-side. -/

import D5.S3.Estimation.DecisionRisk.PosteriorUniversalSufficiency
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-24):
   * Exact family hits `posterior`, `conditionalRisk`, `conditionalBayesValue`, and
     `posterior_universal_sufficiency` are imported from
     `PosteriorUniversalSufficiency`; the value clause applies that theorem directly.
   * Exact pinned-Mathlib hits `Setoid.kerLift`, `Setoid.kerLift_injective`, and
     `Quotient.lift_comp_mk` give the canonical map from the quotient by a law's
     equality kernel, its injectivity, and its computation rule.
   * Repository searches found no theorem combining the canonical law quotient with
     posterior-determined optimizer sets. The optimizer clause follows by transporting
     every normalized conditional risk along posterior equality.
   * `loogle` and `leansearch` executables are absent from PATH on this lane. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped NNReal

noncomputable section

namespace D5.S3.Estimation.DecisionRisk.ExperimentStatePosteriorDecisionSeparation

open D5.S3.Estimation.DecisionRisk.PosteriorUniversalSufficiency

/-- The canonical quotient by equality of complete experiment laws determines the
law through its injective lifted map. Separately, on the evidence domain, equality
of target posteriors determines both the Bayes value and the complete set of
Bayes-optimal actions for every fixed real loss family. -/
theorem experiment_state_and_posterior_decision_separation
    {State Law Theta Evidence : Type*} [Fintype Theta]
    (law : State -> Law) (joint : Theta -> Evidence -> NNReal) :
    (Function.Injective (Setoid.kerLift law) ∧
      law = Setoid.kerLift law ∘
        (Quotient.mk'' : State -> Quotient (Setoid.ker law))) ∧
    ∀ {evidence evidence' : Evidence},
      posterior joint evidence = posterior joint evidence' ->
      ∀ (Action : Type) (loss : Theta -> Action -> Real),
        conditionalBayesValue joint evidence loss =
            conditionalBayesValue joint evidence' loss ∧
          {action | ∀ alternative,
              conditionalRisk joint evidence loss action <=
                conditionalRisk joint evidence loss alternative} =
            {action | ∀ alternative,
              conditionalRisk joint evidence' loss action <=
                conditionalRisk joint evidence' loss alternative} := by
  constructor
  · constructor
    · exact Setoid.kerLift_injective law
    · simpa only [Setoid.kerLift, Quotient.mk''_eq_mk] using
        (Quotient.lift_comp_mk law (fun _ _ equalLaw => equalLaw)).symm
  · intro evidence evidence' equalPosterior Action loss
    constructor
    · exact posterior_universal_sufficiency joint equalPosterior Action loss
    · have equalRisk :
          conditionalRisk joint evidence loss =
            conditionalRisk joint evidence' loss := by
        funext action
        apply Finset.sum_congr rfl
        intro theta _
        change (posterior joint evidence theta : Real) * loss theta action =
          (posterior joint evidence' theta : Real) * loss theta action
        rw [equalPosterior]
      rw [equalRisk]

/-- A noninjective Boolean law still has an injective canonical law-quotient map. -/
example :
    Function.Injective
      (Setoid.kerLift (fun state : Bool => state && state)) :=
  Setoid.kerLift_injective _

/-- Proportional evidence weights produce the same posterior, Bayes value, and
optimizer set for every action carrier and loss. -/
example :
    let joint : Bool -> Bool -> NNReal := fun theta evidence =>
      if evidence then if theta then 4 else 2 else if theta then 2 else 1
    ∀ (Action : Type) (loss : Bool -> Action -> Real),
      conditionalBayesValue joint false loss =
          conditionalBayesValue joint true loss ∧
        {action | ∀ alternative,
            conditionalRisk joint false loss action <=
              conditionalRisk joint false loss alternative} =
          {action | ∀ alternative,
            conditionalRisk joint true loss action <=
              conditionalRisk joint true loss alternative} := by
  dsimp only
  apply (experiment_state_and_posterior_decision_separation
    (fun state : Bool => state && state)
    (fun theta evidence : Bool =>
      if evidence then if theta then 4 else 2 else if theta then 2 else 1)).2
  funext theta
  cases theta <;> norm_num [posterior, historyMass]

#print axioms experiment_state_and_posterior_decision_separation

end D5.S3.Estimation.DecisionRisk.ExperimentStatePosteriorDecisionSeparation
