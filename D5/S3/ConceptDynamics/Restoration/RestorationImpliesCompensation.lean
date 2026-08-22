/- GID: D5/S3/ConceptDynamics/Restoration/RestorationImpliesCompensation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Restoration/RestorationImpliesCompensation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identity restoration preserves every value determined by identity. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-22):
   * Repository searches for identity restoration, value compensation, and
     restoration through refinement found no existing statement of this theorem.
   * Exact repository hits `ConceptFiberDecomposition.Concept` and
     `ConceptJoinUniversal.Refines` are the canonical concept carrier and
     factor-map refinement relation; both are imported and used directly.
   * Exact core hit `congrArg` transports restored identity equality through the
     refinement factor. Pinned Mathlib and repository searches found no thinner
     named theorem for this source-specific composition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Restoration.RestorationImpliesCompensation

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- If identity determines value, restoring identity after harm also restores
the value or function recorded by the coarser concept. -/
theorem identity_restoration_implies_value_compensation
    {X IdentityValue FunctionalValue : Type*}
    (identity : Concept X IdentityValue)
    (value : Concept X FunctionalValue)
    (harm repair : X -> X)
    (valueDeterminedByIdentity : Refines value identity)
    (identityRestored :
      forall x, identity (repair (harm x)) = identity x) :
    forall x, value (repair (harm x)) = value x := by
  rcases valueDeterminedByIdentity with ⟨factor, factorization⟩
  intro x
  calc
    value (repair (harm x)) = factor (identity (repair (harm x))) :=
      congrFun factorization (repair (harm x))
    _ = factor (identity x) := congrArg factor (identityRestored x)
    _ = value x := (congrFun factorization x).symm

/-- Identity restoration and value compensation can both hold on a nontrivial
state carrier. -/
example :
    let identity : Concept Bool Bool := id
    let value : Concept Bool Bool := id
    let harm : Bool -> Bool := Bool.not
    let repair : Bool -> Bool := Bool.not
    (Refines value identity) /\
      (forall x, identity (repair (harm x)) = identity x) /\
      (forall x, value (repair (harm x)) = value x) := by
  dsimp
  exact ⟨⟨id, rfl⟩, (by intro x; cases x <;> rfl),
    (by intro x; cases x <;> rfl)⟩

#print axioms identity_restoration_implies_value_compensation

end D5.S3.ConceptDynamics.Restoration.RestorationImpliesCompensation
