/- GID: D5/S3/ConceptDynamics/InterventionsExchange/SingleWorldInterventionLawAgreement
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InterventionsExchange/SingleWorldInterventionLawAgreement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Stable and flip Boolean models agree under every perfect single-world intervention. -/

import D5.S3.ConceptDynamics.InterventionLaws.SingleWorldPerfectInterventionLaw

/- Library-search audit trail (2026-08-26):
   * The frozen predecessor provides the exact Lean proof but was withdrawn for
     placement and Scribe binding defects. The redo mandate requires a fresh
     GID while leaving that module untouched.
   * The imported family is the single source of truth for `PerfectIntervention`,
     `endogenousLaw`, `noEffectModel`, and `flipEffectModel`; no local copy of
     any carrier, law, or source model is introduced.
   * Pinned Mathlib has no causal intervention-law declaration. The repository
     theorem is applied directly rather than reproving its finite counts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InterventionsExchange.SingleWorldInterventionLawAgreement

open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open D5.S3.ConceptDynamics.InterventionLaws.SingleWorldPerfectInterventionLaw

/-- With the stable and flip source models bound publicly, every imposed
treatment has the uniform Boolean outcome count in both models, and every
perfect intervention on either endogenous variable gives the same joint law. -/
theorem single_world_perfect_intervention_laws_agree :
    let S := noEffectModel
    let F := flipEffectModel
    (∀ treatment result : Bool,
      Int S treatment result = 1 ∧ Int F treatment result = 1) ∧
      ∀ intervention : PerfectIntervention, ∀ result : Bool × Bool,
        endogenousLaw S intervention result = endogenousLaw F intervention result := by
  exact all_single_world_perfect_intervention_laws_agree

#print axioms single_world_perfect_intervention_laws_agree

end D5.S3.ConceptDynamics.InterventionsExchange.SingleWorldInterventionLawAgreement
