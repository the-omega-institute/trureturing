/- GID: D5/S3/ConceptDynamics/InterventionsExchange/MarginalTransportCouplingGap
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InterventionsExchange/MarginalTransportCouplingGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal single-world intervention marginals can transport while cross-world agreement changes. -/

import D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-08-26):
   * Searches for stable/flip Boolean causal models, equal intervention
     marginals, coupling agreement, and `P(Y0 = Y1)` found the frozen
     `InterventionCounterfactualSeparation` family. Its public theorem concludes
     only that the complete counterfactual tables differ, not that the source's
     named agreement probability differs.
   * The frozen family supplies the canonical deterministic Boolean model,
     intervention-count table, no-effect model, and flip-effect model. They are
     imported rather than redeclared.
   * Body-shape searches for a uniform two-unit count of
     `outcome u false = outcome u true` found no existing D5 primitive.
   * Pinned Mathlib supplies exact rational arithmetic and Boolean case
     reduction, but no causal marginal-versus-coupling transport theorem.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InterventionsExchange.MarginalTransportCouplingGap

open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation

/-- Under the uniform two-unit exogenous population, the probability that the
two potential outcomes agree. -/
def couplingAgreementProbability (model : DeterministicBoolSCM) : ℚ :=
  ((if model.outcome false false = model.outcome false true then 1 else 0) +
      if model.outcome true false = model.outcome true true then 1 else 0) / 2

/-- The stable and flip models have identical single-world intervention
marginals, but transporting those marginals does not transport their
cross-world agreement probability. -/
theorem marginal_transport_does_not_determine_coupling :
    Int noEffectModel = Int flipEffectModel ∧
      couplingAgreementProbability noEffectModel ≠
        couplingAgreementProbability flipEffectModel := by
  constructor
  · funext treatment result
    cases treatment <;> cases result <;> rfl
  · norm_num [couplingAgreementProbability, noEffectModel, flipEffectModel]

#print axioms marginal_transport_does_not_determine_coupling

end D5.S3.ConceptDynamics.InterventionsExchange.MarginalTransportCouplingGap
