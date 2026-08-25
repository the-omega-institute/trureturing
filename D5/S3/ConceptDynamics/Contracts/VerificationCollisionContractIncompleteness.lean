/- GID: D5/S3/ConceptDynamics/Contracts/VerificationCollisionContractIncompleteness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Contracts/VerificationCollisionContractIncompleteness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A verification collision that separates obligations blocks exact contracts. -/

import D5.S0.Rewriting.Quotients.InformedDisclosureDefect

/- Library-search audit trail (2026-08-25):
   * Exact repository support hit `informed_disclosure_defect`; its second
     conclusion is the arbitrary-carrier no-factorization obstruction and is
     applied directly. Its first decision-rule clause is additional, so the
     existing theorem is not an exact bind-only statement for this atom.
   * `FutureObligationIncompleteness` and `EmergencyEvidenceNecessity` restrict
     the obligation carrier to `Bool` and add independently named clauses.
     `TargetRecoveryCriterion` requires an inhabited state carrier and packages
     a four-way criterion rather than this supplied collision theorem.
   * Body-shape searches for an obligation map factoring through a verification
     map found no exact theorem on the source carrier.
   * Pinned Mathlib's `congrArg` is already applied by the imported theorem; no
     library declaration packages the contract interpretation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Contracts.VerificationCollisionContractIncompleteness

open D5.S0.Rewriting.Quotients.InformedDisclosureDefect

/-- If two states have the same verifiable readout but different ideal
obligations, no contract depending only on that readout can implement the
obligation map exactly. -/
theorem verification_collision_contract_incomplete
    {State Verification Obligation : Type*}
    (verification : State -> Verification)
    (obligation : State -> Obligation)
    {x y : State}
    (sameVerification : verification x = verification y)
    (differentObligation : obligation x ≠ obligation y) :
    ¬∃ contract : Verification -> Obligation,
      obligation = contract ∘ verification := by
  exact (informed_disclosure_defect (Decision := Unit)
    verification obligation sameVerification differentObligation).2

#print axioms verification_collision_contract_incomplete

end D5.S3.ConceptDynamics.Contracts.VerificationCollisionContractIncompleteness
