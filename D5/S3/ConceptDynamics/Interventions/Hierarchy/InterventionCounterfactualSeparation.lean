/- GID: D5/S3/ConceptDynamics/Interventions/Hierarchy/InterventionCounterfactualSeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interventions/Hierarchy/InterventionCounterfactualSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two Boolean structural causal models agree on every interventional marginal but disagree on an exogenous-unit counterfactual. -/

import Mathlib.Data.Bool.Basic

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'intervention_strictly_weaker_than_counterfactual' D5
     Golden/Frozen/accepted` returned no match.
   * The requested counterfactual/exogenous/potential-outcome repository search
     found only unrelated continued-fraction and fairness declarations, not two
     structural causal models with equal interventional marginals.
   * `ObservationInterventionSeparation.lean` is absent from this worktree and
     `origin/dev`, so no signature from that unmerged sister module is assumed.
   * Pinned Mathlib supplies Boolean negation and its elementary equations, but
     no causal-hierarchy declaration; the proof uses Boolean case analysis.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Interventions.Hierarchy.InterventionCounterfactualSeparation

/-- A deterministic Boolean structural causal model maps an exogenous unit and
an imposed treatment value to its outcome. -/
structure DeterministicBoolSCM where
  outcome : Bool -> Bool -> Bool

/-- The interventional layer records the outcome count under the uniform
two-point exogenous population for each treatment and outcome. -/
def Int (M : DeterministicBoolSCM) : Bool -> Bool -> Nat :=
  fun treatment result =>
    (if M.outcome false treatment = result then 1 else 0) +
      if M.outcome true treatment = result then 1 else 0

/-- The counterfactual layer retains the exogenous unit while replacing the
factual treatment by an alternate treatment. -/
def CF (M : DeterministicBoolSCM) : Bool -> Bool -> Bool -> Bool :=
  fun exogenous _factual alternate => M.outcome exogenous alternate

/-- Treatment has no effect: the outcome is the exogenous bit. -/
def noEffectModel : DeterministicBoolSCM :=
  ⟨fun exogenous _treatment => exogenous⟩

/-- Treatment `true` flips the exogenous bit while treatment `false` preserves it. -/
def flipEffectModel : DeterministicBoolSCM :=
  ⟨fun exogenous treatment => if treatment then !exogenous else exogenous⟩

/-- Equal interventional marginals do not determine unit-level counterfactuals. -/
theorem intervention_strictly_weaker_than_counterfactual :
    ∃ M N : DeterministicBoolSCM, Int M = Int N ∧ CF M ≠ CF N := by
  refine ⟨noEffectModel, flipEffectModel, ?_, ?_⟩
  · funext treatment result
    cases treatment <;> cases result <;> rfl
  · intro counterfactualsEqual
    have falseEqualsTrue : false = true := by
      simpa [CF, noEffectModel, flipEffectModel] using
        congrFun (congrFun (congrFun counterfactualsEqual false) false) true
    cases falseEqualsTrue

example : CF noEffectModel false false true = false := rfl

#print axioms intervention_strictly_weaker_than_counterfactual

end D5.S3.ConceptDynamics.Interventions.Hierarchy.InterventionCounterfactualSeparation
