/- GID: D5/S3/ConceptDynamics/InstitutionalCapture/PublicUnlinkabilityAccountabilityIncompatibility
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InstitutionalCapture/PublicUnlinkabilityAccountabilityIncompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nontrivial identity prevents simultaneous unlinkability and accountability. -/

/- Library-search audit trail (2026-08-22):
   * Exact repository hits `Concept` and `Refines` are the canonical concept readout and
     factorization primitives; they are imported through the existing obstruction theorem.
   * Exact repository hit `commonCoreRelation` constructs the canonical common coarsening from
     the two source kernels, and `common_core_obstructs_complete_forgetting` proves the abstract
     nontrivial-core obstruction. Both are imported and the latter is applied directly below.
   * Searches for public unlinkability, complete accountability, and their conjunction found no
     existing declaration stating this identity/transcript incompatibility. No additional
     Mathlib theorem is needed. -/

import D5.S3.ConceptDynamics.Interventions.CommonCoreForgettingObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InstitutionalCapture
namespace PublicUnlinkabilityAccountabilityIncompatibility

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Interventions.CommonCoreForgettingObstruction

/-- A nonconstant identity readout cannot simultaneously have trivial common public information
with a transcript and factor through that transcript. -/
theorem public_unlinkability_accountability_incompatible
    {X PublicInfo IdentityInfo : Type*}
    (publicTranscript : Concept X PublicInfo)
    (identity : Concept X IdentityInfo)
    (identityNontrivial : exists x y, identity x ≠ identity y) :
    Not (commonCoreRelation publicTranscript identity = ⊤ /\
      Refines identity publicTranscript) := by
  intro simultaneous
  have identityCoreNontrivial : commonCoreRelation identity identity ≠ ⊤ := by
    intro identityCoreTrivial
    rcases identityNontrivial with ⟨x, y, hxy⟩
    apply hxy
    have related : commonCoreRelation identity identity x y := by
      rw [identityCoreTrivial]
      trivial
    rw [commonCoreRelation, sup_idem] at related
    exact related
  exact (common_core_obstructs_complete_forgetting
    identity identity publicTranscript identityCoreNontrivial)
      ⟨simultaneous.2, simultaneous.1⟩

/- The nontrivial-identity hypothesis is inhabited on a two-state carrier, where the identity
readout also factors through the public transcript. -/
example :
    let publicTranscript : Concept Bool Bool := id
    let identity : Concept Bool Bool := id
    (exists x y, identity x ≠ identity y) /\
      Not (commonCoreRelation publicTranscript identity = ⊤ /\
        Refines identity publicTranscript) := by
  dsimp
  have identityNontrivial : exists x y : Bool, x ≠ y :=
    ⟨false, true, Bool.false_ne_true⟩
  exact ⟨identityNontrivial,
    public_unlinkability_accountability_incompatible id id identityNontrivial⟩

#print axioms public_unlinkability_accountability_incompatible

end PublicUnlinkabilityAccountabilityIncompatibility
end D5.S3.ConceptDynamics.InstitutionalCapture
