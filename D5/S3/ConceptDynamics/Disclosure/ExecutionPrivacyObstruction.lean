/- GID: D5/S3/ConceptDynamics/Disclosure/ExecutionPrivacyObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Disclosure/ExecutionPrivacyObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonpublic target-sensitive core obstructs exact execution without new leakage. -/

import D5.S3.ConceptDynamics.Disclosure.ExactTargetForcedLeak

/- Library-search audit trail (2026-08-25):
   * Exact family hits `Concept`, `Refines`, `conceptJoin`, `IsConceptMeet`,
     `StructurallyNoNewLeak`, and
     `forced_leak_preexists_of_structurally_no_new_leak` represent every source
     object and are imported directly.
   * Repository searches found the positive forced-leak theorem but no existing
     declaration stating the source's execution/privacy impossibility.
   * Pinned Mathlib has no theorem about these canonical factorization-meet
     objects; the proof is the direct contradiction supplied by the family hit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Disclosure.ExecutionPrivacyObstruction

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Disclosure.ExactTargetForcedLeak

universe u v

/-- If the target-sensitive meet is not already below the public-sensitive
meet, an added audit readout cannot both realize the target exactly and leave
the sensitive common part unchanged. -/
theorem execution_privacy_obstruction
    {X : Type u} {P L S E K Before After : Type v}
    (publicConcept : Concept X P)
    (added : Concept X L)
    (sensitive : Concept X S)
    (target : Concept X E)
    (forcedPart : Concept X K)
    (before : Concept X Before)
    (after : Concept X After)
    (forcedPartIsMeet : IsConceptMeet target sensitive forcedPart)
    (notPreexisting : ¬Refines forcedPart before) :
    ¬(Refines target (conceptJoin publicConcept added) ∧
      StructurallyNoNewLeak publicConcept added sensitive before after) := by
  rintro ⟨targetRealized, noNewLeak⟩
  exact notPreexisting <|
    forced_leak_preexists_of_structurally_no_new_leak
      publicConcept added sensitive target forcedPart before after
      targetRealized forcedPartIsMeet noNewLeak

#print axioms execution_privacy_obstruction

end D5.S3.ConceptDynamics.Disclosure.ExecutionPrivacyObstruction
