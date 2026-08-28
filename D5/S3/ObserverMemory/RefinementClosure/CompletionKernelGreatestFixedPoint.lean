/- GID: D5/S3/ObserverMemory/RefinementClosure/CompletionKernelGreatestFixedPoint
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/RefinementClosure/CompletionKernelGreatestFixedPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The completed observation kernel is the greatest forward-invariant kernel relation. -/

import D5.S3.Observer.Separation.FiniteFutureCongruence
import D5.S3.ObserverMemory.Prediction.ItineraryCompletion

/- Library-search audit trail (2026-08-27):
   * Exact repository component hits `infinite_relation_eq_gfp`,
     `infinite_relation_below_kernel`, `infinite_relation_invariant`, and
     `relation_le_infinite` supply the four source clauses on the general
     relation carrier. The finite all-in-one theorem is not an exact hit
     because it adds a `Fintype` restriction and unrelated finite clauses.
   * Exact family hit `completeItinerary` is the canonical behavior-completion
     primitive. Its kernel is bridged publicly to the existing infinite-future
     relation rather than redeclared as a new definition.
   * Pinned Mathlib provides `OrderHom.gfp`, but no theorem combines the
     completed-readout kernel with containment, invariance, and maximality. -/

namespace D5.S3.ObserverMemory.RefinementClosure.CompletionKernelGreatestFixedPoint

open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The kernel of the complete future readout is the greatest fixed point of
the one-step kernel refinement operator. Equivalently, it lies in the current
readout kernel, is forward invariant, and contains every relation with those
two properties. -/
theorem completion_kernel_is_greatest_fixed_point
    {Y O : Type*} (tau : Y -> Y) (q : Y -> O) :
    let completedKernel : StateRelation Y :=
      {pair | Setoid.ker (completeItinerary tau q) pair.1 pair.2}
    (completedKernel = (refinementOperator tau q).gfp) ∧
      (completedKernel ≤ observationKernel q) ∧
      (∀ pair, pair ∈ completedKernel ->
        (tau pair.1, tau pair.2) ∈ completedKernel) ∧
      ∀ relation : StateRelation Y,
        relation ≤ observationKernel q ->
        (∀ pair, pair ∈ relation ->
          (tau pair.1, tau pair.2) ∈ relation) ->
        relation ≤ completedKernel := by
  dsimp only
  have completed_kernel_eq :
      {pair | Setoid.ker (completeItinerary tau q) pair.1 pair.2} =
        infiniteFutureRelation tau q := by
    ext pair
    change
      completeItinerary tau q pair.1 = completeItinerary tau q pair.2 ↔
        ∀ k, observedAt tau q k pair.1 = observedAt tau q k pair.2
    constructor
    · intro h k
      simpa [completeItinerary, observedAt] using congrFun h k
    · intro h
      funext k
      simpa [completeItinerary, observedAt] using h k
  rw [completed_kernel_eq]
  exact ⟨infinite_relation_eq_gfp tau q,
    infinite_relation_below_kernel tau q,
    infinite_relation_invariant tau q,
    relation_le_infinite tau q⟩

#print axioms completion_kernel_is_greatest_fixed_point

end D5.S3.ObserverMemory.RefinementClosure.CompletionKernelGreatestFixedPoint
