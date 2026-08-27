/- GID: D5/S3/ConceptDynamics/Disclosure/ExactTargetLeakConsequences
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Disclosure/ExactTargetLeakConsequences
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact realization forces its sensitive part and obstructs zero new leakage. -/

import D5.S3.ConceptDynamics.Disclosure.ExecutionPrivacyObstruction

/- Library-search audit trail (2026-08-27):
   * Exact D5 hit `exact_target_forced_leak` supplies the forced refinement of
     the target-sensitive meet into the augmented-public sensitive meet.
   * Exact D5 hit `execution_privacy_obstruction` supplies the conditional
     impossibility of exact realization together with structural no-new-leak.
   * Body-shape searches confirmed that `IsConceptMeet`, `conceptJoin`,
     `Refines`, and `StructurallyNoNewLeak` are the canonical family primitives.
     No pinned Mathlib theorem combines these concept-factorization clauses;
     `loogle` and `leansearch` were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Disclosure.ExactTargetLeakConsequences

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Disclosure.ExactTargetForcedLeak
open D5.S3.ConceptDynamics.Disclosure.ExecutionPrivacyObstruction

universe u v

/-- Exact target realization forces its target-sensitive common part into the
post-addition sensitive leak. If that forced part was not already present in a
candidate prior sensitive common part, structural no-new-leak is impossible. -/
theorem exact_target_leak_consequences
    {X : Type u} {P M S E K L : Type v}
    (publicConcept : Concept X P) (added : Concept X M) (sensitive : Concept X S)
    (target : Concept X E) (forcedPart : Concept X K) (leak : Concept X L)
    (targetRealized : Refines target (conceptJoin publicConcept added))
    (forcedPartIsMeet : IsConceptMeet target sensitive forcedPart)
    (leakIsMeet : IsConceptMeet (conceptJoin publicConcept added) sensitive leak) :
    Refines forcedPart leak ∧
      ∀ {Before : Type v} (before : Concept X Before),
        ¬Refines forcedPart before ->
          ¬StructurallyNoNewLeak publicConcept added sensitive before leak := by
  constructor
  · exact exact_target_forced_leak publicConcept added sensitive target forcedPart leak
      targetRealized forcedPartIsMeet leakIsMeet
  · intro Before before notPreexisting noNewLeak
    exact execution_privacy_obstruction
      publicConcept added sensitive target forcedPart before leak
      forcedPartIsMeet notPreexisting ⟨targetRealized, noNewLeak⟩

#print axioms exact_target_leak_consequences

end D5.S3.ConceptDynamics.Disclosure.ExactTargetLeakConsequences
