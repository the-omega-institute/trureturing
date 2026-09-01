/- GID: D5/S3/Observer/AgencySelf/AgencySelfUniversalMinimality
   generality: G
   mirror-B: D5/B/S3/Observer/AgencySelf/AgencySelfUniversalMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Sufficient interfaces uniquely cover the agency-self quotient. -/

import D5.S3.ConceptDynamics.SufficiencyQuotient.StrategyProfileQuotientMinimality

/- Library-search audit trail (2026-09-01):
   * The exact repository hit `strategy_sufficient_self_universal_minimality`
     has the same effective-image domain, profile-kernel quotient, pointwise
     factorization, and uniqueness clause. Its existing receipts for atoms
     `bdeaff4a...` and `3bddcf73...` were read, so it is imported and applied
     directly rather than reproved.
   * Adjacent hits `interface_refinement_iff_kernel_inclusion` and
     `predictive_state_universal_minimality` land in realized ranges instead
     of the requested kernel quotient. `minimal_prediction_belief_state` is a
     stronger bundled source used by the exact repository theorem.
   * Pinned Mathlib provides `Set.rangeFactorization_surjective`,
     `Function.Surjective.injective_comp_right`, `Setoid.quotientKerEquivRange`,
     and `Function.FactorsThrough`; no separate proof is introduced here.
   * The ordered search stopped at the exact repository declaration, so no
     third-party dependency or local quotient construction is needed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.AgencySelf.AgencySelfUniversalMinimality

open D5.S3.ConceptDynamics.SufficiencyQuotient.StrategyProfileQuotientMinimality

universe uHistory uIntervention uInteraction uInterface

/-- If a history interface determines the complete future-interaction profile,
it induces a unique map from its effective image to the quotient of histories
by equality of that profile. -/
theorem agency_self_universal_minimality
    {History : Type uHistory} {Intervention : Type uIntervention}
    {Interaction : Type uInteraction} {Interface : Type uInterface}
    (interactionProfile : History -> Intervention -> PMF Interaction)
    (historyInterface : History -> Interface)
    (decoder : Interface -> Intervention -> PMF Interaction)
    (sufficient : interactionProfile = decoder ∘ historyInterface) :
    ∃! factor : Set.range historyInterface -> Quotient (Setoid.ker interactionProfile),
      ∀ history,
        Quotient.mk (Setoid.ker interactionProfile) history =
          factor (Set.rangeFactorization historyInterface history) := by
  exact strategy_sufficient_self_universal_minimality
    interactionProfile historyInterface decoder sufficient

#print axioms agency_self_universal_minimality

end D5.S3.Observer.AgencySelf.AgencySelfUniversalMinimality
