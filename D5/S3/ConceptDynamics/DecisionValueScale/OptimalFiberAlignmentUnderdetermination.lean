/- GID: D5/S3/ConceptDynamics/DecisionValueScale/OptimalFiberAlignmentUnderdetermination
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValueScale/OptimalFiberAlignmentUnderdetermination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A proxy-optimal tie can preclude a principal-best selection guarantee. -/

import Mathlib.Data.Real.Basic

/- Library-search audit trail (2026-08-27):
   * Repository searches for proxy/principal objectives, optimal ties, maximizer
     guarantees, and objective-fiber underdetermination found no exact theorem.
   * `strict_monotone_factorization_preserves_argmax` is the adjacent positive
     factorization theorem; it neither assumes nor concludes an optimal tie with
     unequal principal values.
   * Body-shape searches for expanded maximizer predicates, `IsGreatest`, and
     `argmax` found no canonical D5 predicate to import, so the source condition
     remains public and expanded rather than becoming a sibling definition.
   * Pinned Mathlib's `le_antisymm` is applied to the two guarantee comparisons.
     No library theorem packages this proxy/principal obstruction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DecisionValueScale.OptimalFiberAlignmentUnderdetermination

/-- Two globally proxy-optimal states with different principal values show that
proxy maximization alone cannot make every selected proxy maximizer principal-best
among the proxy maximizers. -/
theorem proxy_optimal_tie_precludes_principal_guarantee
    {Z : Type*} (agentObjective principalObjective : Z -> Real)
    (first second : Z)
    (agentTie : agentObjective first = agentObjective second)
    (firstAgentOptimal : forall alternative,
      agentObjective alternative <= agentObjective first)
    (principalDisagrees : principalObjective first ≠ principalObjective second) :
    ¬ forall selected : Z,
      (forall alternative, agentObjective alternative <= agentObjective selected) ->
      forall alternative : Z,
        (forall candidate, agentObjective candidate <= agentObjective alternative) ->
        principalObjective alternative <= principalObjective selected := by
  intro guarantee
  have secondAgentOptimal : forall alternative,
      agentObjective alternative <= agentObjective second := by
    intro alternative
    calc
      agentObjective alternative <= agentObjective first :=
        firstAgentOptimal alternative
      _ = agentObjective second := agentTie
  have secondBelowFirst :=
    guarantee first firstAgentOptimal second secondAgentOptimal
  have firstBelowSecond :=
    guarantee second secondAgentOptimal first firstAgentOptimal
  exact principalDisagrees (le_antisymm firstBelowSecond secondBelowFirst)

#print axioms proxy_optimal_tie_precludes_principal_guarantee

end D5.S3.ConceptDynamics.DecisionValueScale.OptimalFiberAlignmentUnderdetermination
