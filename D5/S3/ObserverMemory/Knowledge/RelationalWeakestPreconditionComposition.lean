/- GID: D5/S3/ObserverMemory/Knowledge/RelationalWeakestPreconditionComposition
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Knowledge/RelationalWeakestPreconditionComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Universal weakest preconditions compose in reverse process order. -/

import D5.S3.ObserverMemory.Knowledge.RelationalPreconditionAdjunction

/- Library-search audit trail (2026-08-27):
   * The current D5 tree supplies the canonical source primitive
     `RelationalPreconditionAdjunction.universalWeakestPrecondition`; no D5
     theorem states its law for relational composition.
   * The body-shape search for relational core composition found the exact
     pinned-Mathlib theorem `SetRel.core_comp`, which is applied directly.
   * No new relation, predicate transformer, definition, or abbreviation is
     introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Knowledge.RelationalWeakestPreconditionComposition

open D5.S3.ObserverMemory.Knowledge.RelationalPreconditionAdjunction
open scoped SetRel

/-- To guarantee a target after two relational stages, first propagate the
target through the second stage and then through the first. -/
theorem universal_weakest_precondition_composition
    {X Y Z : Type*} (first : SetRel X Y) (second : SetRel Y Z)
    (target : Set Z) :
    universalWeakestPrecondition (first ○ second) target =
      universalWeakestPrecondition first
        (universalWeakestPrecondition second target) := by
  simpa only [universalWeakestPrecondition] using
    (SetRel.core_comp first second target)

#print axioms universal_weakest_precondition_composition

end D5.S3.ObserverMemory.Knowledge.RelationalWeakestPreconditionComposition
