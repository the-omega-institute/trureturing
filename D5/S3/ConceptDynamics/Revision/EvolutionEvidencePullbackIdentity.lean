/- GID: D5/S3/ConceptDynamics/Revision/EvolutionEvidencePullbackIdentity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Revision/EvolutionEvidencePullbackIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Direct-image evolution after pulled-back evidence equals future conditioning. -/

import Mathlib.Data.Set.Image

/- Library-search audit trail (2026-08-26):
   * Repository searches for image/preimage identities found the adjacent invariant-evidence
     theorem in `EvolutionConditioningNoncommutation`, but no D5 declaration with the source's
     unconditional two-carrier statement.
   * The body-shape search for `Set.image` with an intersection and preimage found no D5
     primitive to import or redeclare.
   * Pinned Mathlib provides the exact theorem `Set.image_inter_preimage` in
     `Mathlib.Data.Set.Image`; the public wrapper below applies it directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Revision.EvolutionEvidencePullbackIdentity

/-- Evolve the currently admitted states after pulling future evidence back to the
current carrier; the result is exactly the evolved states satisfying that evidence. -/
theorem evolution_evidence_pullback_identity
    {X Y : Type*} (evolution : X -> Y) (admitted : Set X) (futureEvidence : Set Y) :
    evolution '' (admitted ∩ evolution ⁻¹' futureEvidence) =
      evolution '' admitted ∩ futureEvidence := by
  exact Set.image_inter_preimage evolution admitted futureEvidence

#print axioms evolution_evidence_pullback_identity

end D5.S3.ConceptDynamics.Revision.EvolutionEvidencePullbackIdentity
