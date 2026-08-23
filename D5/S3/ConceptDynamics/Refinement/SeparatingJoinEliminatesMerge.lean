/- GID: D5/S3/ConceptDynamics/Refinement/SeparatingJoinEliminatesMerge
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Refinement/SeparatingJoinEliminatesMerge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A separating readout removes the corresponding merge from the product refinement. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-23):
   * Exact frozen family hits `ConceptFiberDecomposition.Concept` and
     `ConceptJoinUniversal.conceptJoin` construct the source's concept readouts and
     canonical product refinement; they are imported rather than redeclared.
   * Repository and active frozen-ledger searches found no theorem exposing the specified
     point-pair separation after adjoining a distinguishing concept.
   * Exact pinned-Mathlib hit `Prod.mk.injEq` reduces equality in the product readout to
     equality of both component readouts and is applied directly below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Refinement.SeparatingJoinEliminatesMerge

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- If the added concept distinguishes two states, their product refinement coordinates
are distinct, so that concrete merge is absent from the refined concept. -/
theorem separating_join_eliminates_merge
    {X C D : Type*} (current : Concept X C) (separating : Concept X D) (x y : X)
    (separated : Ne (separating x) (separating y)) :
    Ne (conceptJoin current separating x) (conceptJoin current separating y) := by
  intro joinedEquality
  change (current x, separating x) = (current y, separating y) at joinedEquality
  simp only [Prod.mk.injEq] at joinedEquality
  exact separated joinedEquality.2

/-- The second Boolean coordinate separates states even when the current readout is constant. -/
example :
    Ne (conceptJoin (fun _ : Bool => ()) (id : Concept Bool Bool) false)
      (conceptJoin (fun _ : Bool => ()) (id : Concept Bool Bool) true) := by
  apply separating_join_eliminates_merge
  exact Bool.false_ne_true

/-- Without a separating coordinate, a constant product readout still merges the pair. -/
example :
    conceptJoin (fun _ : Bool => ()) (fun _ : Bool => ()) false =
      conceptJoin (fun _ : Bool => ()) (fun _ : Bool => ()) true := rfl

#print axioms separating_join_eliminates_merge

end D5.S3.ConceptDynamics.Refinement.SeparatingJoinEliminatesMerge
