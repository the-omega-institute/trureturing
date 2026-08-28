/- GID: D5/S3/ObserverMemory/Knowledge/RelationalStrongestPostconditionComposition
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Knowledge/RelationalStrongestPostconditionComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Relational strongest postconditions compose in forward process order. -/

import D5.S3.ObserverMemory.Knowledge.RelationalPreconditionAdjunction

/- Library-search audit trail (2026-08-27):
   * The current D5 tree supplies the canonical source primitive
     `RelationalPreconditionAdjunction.relationalStrongestPostcondition`; no D5
     theorem states its law for relational composition.
   * The body-shape search for relational image composition found the exact
     pinned-Mathlib theorem `SetRel.image_comp`, which is applied directly.
   * No new relation, predicate transformer, definition, or abbreviation is
     introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Knowledge.RelationalStrongestPostconditionComposition

open D5.S3.ObserverMemory.Knowledge.RelationalPreconditionAdjunction
open scoped SetRel

/-- The strongest-postcondition transformer for a two-stage relation is the
forward composition of the transformers for its two stages. -/
theorem relational_strongest_postcondition_composition
    {X Y Z : Type*} (first : SetRel X Y) (second : SetRel Y Z) :
    relationalStrongestPostcondition (first ○ second) =
      relationalStrongestPostcondition second ∘
        relationalStrongestPostcondition first := by
  funext source
  simpa only [relationalStrongestPostcondition, Function.comp_apply] using
    (SetRel.image_comp first second source)

#print axioms relational_strongest_postcondition_composition

end D5.S3.ObserverMemory.Knowledge.RelationalStrongestPostconditionComposition
