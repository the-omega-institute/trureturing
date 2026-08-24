/- GID: D5/S3/ConceptDynamics/Identity/StrictIdentityBranchImpossibility
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Identity/StrictIdentityBranchImpossibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two distinct objects cannot both be strictly identical to one object. -/

import Mathlib.Logic.Basic

/- Library-search audit trail (2026-08-25):
   * Repository searches for the three-object statement, strict identity, and
     branching identity found no exact theorem. The nearby
     `MemoryInheritanceNotIdentity` module concerns right uniqueness of a
     relation and is not the same statement.
   * Pinned Mathlib searches for equality/conjunction incompatibility found no
     full-statement declaration. The proof therefore uses the core equality
     operations `Eq.trans` and `Eq.symm` directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Identity.StrictIdentityBranchImpossibility

/-- If two objects are distinct, they cannot both be strictly identical to a
third object. -/
theorem strict_identity_branch_impossible
    {Carrier : Type*} {x y z : Carrier} (hyz : y ≠ z) :
    ¬ (y = x ∧ z = x) := by
  intro identities
  exact hyz (identities.1.trans identities.2.symm)

#print axioms strict_identity_branch_impossible

end D5.S3.ConceptDynamics.Identity.StrictIdentityBranchImpossibility
