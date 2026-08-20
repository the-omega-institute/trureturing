/- GID: D5/S3/ObserverMemory/Knowledge/StrongestPostconditionAdjunction
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Knowledge/StrongestPostconditionAdjunction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Strongest postconditions and weakest preconditions form an image-preimage adjunction. -/

import D5.S3.ObserverMemory.Knowledge.WeakestPrecondition
import Mathlib.Data.Set.Lattice.Image

/- Library-search audit trail (2026-08-21):
   * Repository searches for `sp_wp_adjunction`, strongest-postcondition names,
     and the image/preimage inclusion shape found no covering D5 declaration.
   * Exact pinned-Mathlib hit: `Set.image_preimage` packages the full
     `GaloisConnection` between direct image and inverse image; its defining
     theorem is `Set.image_subset_iff`. The proof below only specializes it.
   * The frozen `WeakestPrecondition.weakestPrecondition` supplies the source's
     previously defined `wp` side rather than introducing a second definition. -/

namespace D5.S3.ObserverMemory.Knowledge.StrongestPostconditionAdjunction

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The strongest postcondition of `P` under `process` is its direct image. -/
def strongestPostcondition {X Y : Type*} (process : X -> Y) (P : Set X) : Set Y :=
  process '' P

/-- Direct image and inverse image give the strongest-postcondition /
weakest-precondition adjunction. -/
theorem sp_wp_adjunction {X Y : Type*} (process : X -> Y)
    (P : Set X) (Q : Set Y) :
    strongestPostcondition process P ⊆ Q ↔
      P ⊆ WeakestPrecondition.weakestPrecondition process Q := by
  change process '' P ≤ Q ↔ P ≤ process ⁻¹' Q
  exact Set.image_preimage P Q

/-- The concrete state domain used below is inhabited. -/
example : Fin 2 := 0

/-- Identity on a two-state space witnesses the quantified process and both
predicate domains in the adjunction. -/
example :
    strongestPostcondition (id : Fin 2 -> Fin 2) Set.univ ⊆ Set.univ ↔
      Set.univ ⊆ WeakestPrecondition.weakestPrecondition
        (id : Fin 2 -> Fin 2) Set.univ := by
  exact sp_wp_adjunction (id : Fin 2 -> Fin 2) Set.univ Set.univ

#print axioms sp_wp_adjunction

end D5.S3.ObserverMemory.Knowledge.StrongestPostconditionAdjunction
