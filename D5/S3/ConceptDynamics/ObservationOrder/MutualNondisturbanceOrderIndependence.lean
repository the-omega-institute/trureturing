/- GID: D5/S3/ConceptDynamics/ObservationOrder/MutualNondisturbanceOrderIndependence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationOrder/MutualNondisturbanceOrderIndependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nondisturbance removes order effects; commuting updates preserve final state. -/

import D5.S3.ConceptDynamics.ObservationOrder.PureReadoutOrderIndependence

/- Library-search audit trail (2026-08-27):
   * The imported family module owns the canonical `Concept`, `forwardJoint`, and
     `reverseJoint` constructions, which are reused directly below.
   * Its frozen theorem covers only identity updates and omits the source's general
     mutual-nondisturbance premises and further final-state clause.
   * Repository searches found no theorem combining both source clauses.
   * Pinned Mathlib has the generic `Prod.ext` and function-congruence primitives,
     but no exact product-valued observation-order theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationOrder.MutualNondisturbanceOrderIndependence

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ObservationOrder.PureReadoutOrderIndependence

/-- If each instrument's update preserves the other instrument's readout, the
two ordered joint readouts agree. If the updates also commute, the complete
joint-readout-and-final-state executions agree at every initial state. -/
theorem mutual_nondisturbance_order_independence
    {X C D : Type*}
    (observeC : Concept X C)
    (observeD : Concept X D)
    (updateC updateD : X -> X)
    (observeDAfterC : observeD ∘ updateC = observeD)
    (observeCAfterD : observeC ∘ updateD = observeC) :
    forwardJoint observeC observeD updateC =
        reverseJoint observeC observeD updateD ∧
      ((updateD ∘ updateC = updateC ∘ updateD) ->
        ∀ state,
          (forwardJoint observeC observeD updateC state,
              updateD (updateC state)) =
            (reverseJoint observeC observeD updateD state,
              updateC (updateD state))) := by
  have jointReadoutsAgree :
      forwardJoint observeC observeD updateC =
        reverseJoint observeC observeD updateD := by
    funext state
    change
      (observeC state, observeD (updateC state)) =
        (observeC (updateD state), observeD state)
    apply Prod.ext
    · exact (congrFun observeCAfterD state).symm
    · exact congrFun observeDAfterC state
  refine ⟨jointReadoutsAgree, ?_⟩
  intro updatesCommute state
  apply Prod.ext
  · exact congrFun jointReadoutsAgree state
  · exact congrFun updatesCommute state

/-- Constant readouts with nonidentity Boolean updates realize all public
hypotheses, including the additional update-commutation premise. -/
example :
    let observeC : Concept Bool Unit := fun _ => ()
    let observeD : Concept Bool Unit := fun _ => ()
    forwardJoint observeC observeD not = reverseJoint observeC observeD not ∧
      (((not ∘ not) = (not ∘ not)) ->
        ∀ state,
          (forwardJoint observeC observeD not state, not (not state)) =
            (reverseJoint observeC observeD not state, not (not state))) := by
  dsimp
  apply mutual_nondisturbance_order_independence
  · rfl
  · rfl

#print axioms mutual_nondisturbance_order_independence

end D5.S3.ConceptDynamics.ObservationOrder.MutualNondisturbanceOrderIndependence
