/- GID: D5/S3/ConceptDynamics/InterventionsExchange/StableFlipCounterfactualOpposition
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InterventionsExchange/StableFlipCounterfactualOpposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Same single-world laws, opposite potential-outcome couplings. -/

import D5.S3.ConceptDynamics.InterventionLaws.SingleWorldPerfectInterventionLaw
import D5.S3.ConceptDynamics.InterventionsExchange.MarginalTransportCouplingGap
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-08-26):
   * The frozen stable/flip family supplies `noEffectModel`, `flipEffectModel`,
     `CF`, `PerfectIntervention`, `endogenousLaw`, and the canonical
     `couplingAgreementProbability`; all are imported rather than redeclared.
   * `SingleWorldPerfectInterventionLaw` proves equality of every perfect
     single-world endogenous joint law. `MarginalTransportCouplingGap` proves
     only that the agreement probabilities differ. Neither theorem states the
     two probability-one clauses and both equivalence conclusions together.
   * Pinned Mathlib has no causal-model theorem for this pair. `norm_num`
     evaluates the two exact rational probabilities from the imported source
     construction. No `def` or `abbrev` is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InterventionsExchange.StableFlipCounterfactualOpposition

open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open D5.S3.ConceptDynamics.InterventionLaws.SingleWorldPerfectInterventionLaw
open D5.S3.ConceptDynamics.InterventionsExchange.MarginalTransportCouplingGap

/-- The stable model's two potential outcomes agree almost surely, whereas the
flip model's disagree almost surely. Nevertheless their complete perfect
single-world intervention profiles agree, while their unit-preserving
counterfactual profiles differ. -/
theorem stable_flip_intervention_equivalent_counterfactual_opposite :
    let stable := noEffectModel
    let flip := flipEffectModel
    couplingAgreementProbability stable = 1 ∧
      1 - couplingAgreementProbability flip = 1 ∧
      (∀ intervention : PerfectIntervention, ∀ result : Bool × Bool,
        endogenousLaw stable intervention result =
          endogenousLaw flip intervention result) ∧
      CF stable ≠ CF flip := by
  dsimp only
  constructor
  · norm_num [couplingAgreementProbability, noEffectModel]
  constructor
  · norm_num [couplingAgreementProbability, flipEffectModel]
  constructor
  · exact all_single_world_perfect_intervention_laws_agree.2
  · intro counterfactualsEqual
    have falseEqualsTrue : false = true := by
      simpa [CF, noEffectModel, flipEffectModel] using
        congrFun (congrFun (congrFun counterfactualsEqual false) false) true
    exact Bool.false_ne_true falseEqualsTrue

#print axioms stable_flip_intervention_equivalent_counterfactual_opposite

end D5.S3.ConceptDynamics.InterventionsExchange.StableFlipCounterfactualOpposition
