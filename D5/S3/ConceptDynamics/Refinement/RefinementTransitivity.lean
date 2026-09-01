/- GID: D5/S3/ConceptDynamics/Refinement/RefinementTransitivity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Refinement/RefinementTransitivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factorization witnesses compose, so observation refinement is transitive. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-21):
   * Repository census found the canonical `Refines` definition in
     `ConceptJoinUniversal`; no named transitivity theorem or atom receipt exists.
   * The source defines refinement by factorization, so no external theorem is needed.
   * The proof imports and composes the canonical witnesses directly; it does not
     redeclare a sibling relation or carrier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Refinement.RefinementTransitivity

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- Refinement witnesses compose through the intermediate readout carrier. -/
theorem refinement_transitive
    {X B B' B'' : Type _}
    (q : Concept X B) (q' : Concept X B') (q'' : Concept X B'') :
    Refines q' q'' -> Refines q q' -> Refines q q'' := by
  rintro ⟨r, hr⟩ ⟨p, hp⟩
  refine ⟨p ∘ r, ?_⟩
  rw [hp, hr]
  unfold Function.comp
  rfl

#print axioms refinement_transitive

end D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
