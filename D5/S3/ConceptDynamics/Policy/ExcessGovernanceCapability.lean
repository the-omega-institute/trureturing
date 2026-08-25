/- GID: D5/S3/ConceptDynamics/Policy/ExcessGovernanceCapability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Policy/ExcessGovernanceCapability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Higher information adds policy power beyond a target-sufficient lower readout. -/

import D5.S3.ConceptDynamics.Policy.StrictPolicyPowerGrowth
import D5.S3.ConceptDynamics.Refinement.RefinementTransitivity

/- Library-search audit trail (2026-08-25):
   * Exact repository hit `refinement_transitive` composes lower-level target
     sufficiency with the higher readout and is applied directly.
   * Exact repository hit `policy_capability_monotone` proves inclusion of the
     lower policy capability in the higher capability and is applied directly.
   * Exact repository hit `strict_policy_power_growth` constructs a higher-only
     policy from one extra distinction and proves that every lower policy misses
     that distinction; both public halves are reused directly.
   * Repository and pinned-Mathlib searches found no single theorem combining
     target sufficiency with strict policy-capability growth. Pinned Mathlib's
     `Set.range_comp_subset_range` is already used by the imported canonical
     monotonicity theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Policy.ExcessGovernanceCapability

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.PolicyCapabilityMonotonicity
open D5.S3.ConceptDynamics.Policy.StrictPolicyPowerGrowth
open D5.S3.ConceptDynamics.Refinement.RefinementTransitivity

/-- A lower governance readout can already suffice for a target while a higher
readout preserves that sufficiency and strictly enlarges implementable policy
power by separating a pair that every lower policy must identify. -/
theorem excess_governance_capability_without_target_need
    {State TargetValue LowerValue HigherValue Action : Type*}
    (target : Concept State TargetValue)
    (lower : Concept State LowerValue)
    (higher : Concept State HigherValue)
    (left right : State)
    (targetAlreadySufficient : Refines target lower)
    (higherRefinesLower : Refines lower higher)
    (extraDistinction : lower left = lower right ∧ higher left ≠ higher right)
    (distinctActions : ∃ action₀ action₁ : Action, action₀ ≠ action₁) :
    Refines target higher ∧
      policyCapability lower Action ⊆ policyCapability higher Action ∧
      (∃ policy : State -> Action,
        policy ∈ policyCapability higher Action ∧
          policy ∉ policyCapability lower Action ∧
            distinguishesAt policy left right) ∧
      ∀ policy : State -> Action,
        policy ∈ policyCapability lower Action →
          ¬distinguishesAt policy left right := by
  refine ⟨refinement_transitive target lower higher higherRefinesLower
    targetAlreadySufficient, ?_⟩
  refine ⟨policy_capability_monotone lower higher higherRefinesLower, ?_⟩
  exact strict_policy_power_growth lower higher left right
    extraDistinction.1 extraDistinction.2 distinctActions

#print axioms excess_governance_capability_without_target_need

end D5.S3.ConceptDynamics.Policy.ExcessGovernanceCapability
