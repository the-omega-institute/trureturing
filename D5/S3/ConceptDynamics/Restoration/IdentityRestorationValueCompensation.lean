/- GID: D5/S3/ConceptDynamics/Restoration/IdentityRestorationValueCompensation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Restoration/IdentityRestorationValueCompensation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identity restoration preserves determined value, but not conversely. -/

import D5.S3.ConceptDynamics.Restoration.RestorationImpliesCompensation

/- Library-search audit trail (2026-08-26):
   * Exact repository hit
     `RestorationImpliesCompensation.identity_restoration_implies_value_compensation`
     supplies the forward implication and is applied directly below.
   * That frozen theorem has no public countermodel to the converse, so it is not
     an exact whole-theorem bind target for the present two-clause statement.
   * Exact family hits `Concept` and `Refines` are imported rather than redeclared.
     Searches by the restoration-composition body shape found no additional family
     primitive needed by the explicit Bool countermodel.
   * Pinned Mathlib and repository searches found no theorem packaging both the
     source-specific forward implication and its shared converse countermodel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Restoration.IdentityRestorationValueCompensation

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Restoration.RestorationImpliesCompensation

/-- Identity restoration after harm preserves every value determined by identity.
The converse fails on an explicit two-state carrier: swapping the two identities
preserves their common Unit-valued function but does not restore identity. -/
theorem identity_restoration_implies_value_compensation_and_converse_countermodel :
    (forall {X IdentityValue FunctionalValue : Type*}
      (identity : Concept X IdentityValue)
      (value : Concept X FunctionalValue)
      (harm repair : X -> X),
      Refines value identity ->
      (forall x, identity (repair (harm x)) = identity x) ->
      forall x, value (repair (harm x)) = value x) /\
    (let identity : Concept Bool Bool := id
      let value : Concept Bool Unit := fun _ => ()
      let harm : Bool -> Bool := Bool.not
      let repair : Bool -> Bool := id
      Refines value identity /\
        (forall x, value (repair (harm x)) = value x) /\
        Not (forall x, identity (repair (harm x)) = identity x)) := by
  constructor
  · intro X IdentityValue FunctionalValue identity value harm repair
      valueDeterminedByIdentity identityRestored
    exact identity_restoration_implies_value_compensation identity value harm repair
      valueDeterminedByIdentity identityRestored
  · dsimp
    refine ⟨⟨fun _ => (), rfl⟩, ?_, ?_⟩
    · intro x
      rfl
    · intro restored
      apply Bool.false_ne_true
      simpa using (restored false).symm

#print axioms identity_restoration_implies_value_compensation_and_converse_countermodel

end D5.S3.ConceptDynamics.Restoration.IdentityRestorationValueCompensation
