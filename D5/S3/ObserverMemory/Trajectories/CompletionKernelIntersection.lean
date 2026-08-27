/- GID: D5/S3/ObserverMemory/Trajectories/CompletionKernelIntersection
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/CompletionKernelIntersection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The behavior-completion kernel is the intersection of all iterated kernel pullbacks. -/

import D5.S3.ObserverMemory.Prediction.ItineraryCompletion
import D5.S3.Observer.Separation.FiniteFutureCongruence

/- Library-search audit trail (2026-08-27):
   * Exact family hit `completeItinerary` supplies the canonical behavior
     completion constructed from the update and current readout.
   * Supporting family hit `infinite_relation_as_intersection` identifies the
     all-future relation with finite-horizon intersections, but does not state
     the kernel of the canonical completion or the individual iterated
     pullbacks required here.
   * Pinned-Mathlib supplies `Setoid.ker`, `Set.mem_iInter`, `Set.mem_preimage`,
     and `Prod.map`; repository and Mathlib searches found no exact theorem
     packaging this completion-kernel equality. -/

namespace D5.S3.ObserverMemory.Trajectories.CompletionKernelIntersection

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Two states have the same complete future itinerary exactly when every
paired finite iterate lies in the equality kernel of the current readout. -/
theorem completion_kernel_eq_iterated_pullback_intersection
    {X B : Type*} (F : X -> X) (q : X -> B) :
    {pair : X × X |
      Setoid.ker (completeItinerary F q) pair.1 pair.2} =
      ⋂ n : Nat,
        (Prod.map (F^[n]) (F^[n])) ⁻¹'
          {pair : X × X | Setoid.ker q pair.1 pair.2} := by
  ext pair
  simp only [Set.mem_setOf_eq, Setoid.ker_def, Set.mem_iInter,
    Set.mem_preimage]
  change
    (completeItinerary F q pair.1 = completeItinerary F q pair.2) ↔
      ∀ n : Nat, q ((F^[n]) pair.1) = q ((F^[n]) pair.2)
  constructor
  · intro h n
    exact congrFun h n
  · intro h
    funext n
    exact h n

#print axioms completion_kernel_eq_iterated_pullback_intersection

end D5.S3.ObserverMemory.Trajectories.CompletionKernelIntersection
