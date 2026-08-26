/- GID: D5/S3/ConceptDynamics/DagSemantics/CycleCollapseProjection
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/CycleCollapseProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Cyclic realization paths collapse to one logical node under an antisymmetric monotone projection. -/

import Mathlib.Logic.Relation
import Mathlib.Order.Defs.PartialOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagSemantics.CycleCollapseProjection

/-- A projection maps every realization edge to the logical preorder. -/
def EdgeMonotoneProjection
    {Real Logical : Type*}
    (realEdge : Real → Real → Prop)
    (logicalOrder : Logical → Logical → Prop)
    (projection : Real → Logical) : Prop :=
  ∀ ⦃first second : Real⦄,
    realEdge first second → logicalOrder (projection first) (projection second)

/-- Edge monotonicity propagates along realization reachability. -/
theorem projected_reachable
    {Real Logical : Type*}
    {realEdge : Real → Real → Prop}
    {logicalOrder : Logical → Logical → Prop}
    [Std.Refl logicalOrder] [IsTrans Logical logicalOrder]
    {projection : Real → Logical}
    (edgeMonotone : EdgeMonotoneProjection realEdge logicalOrder projection)
    {first last : Real}
    (path : Relation.ReflTransGen realEdge first last) :
    logicalOrder (projection first) (projection last) := by
  induction path with
  | refl => exact refl _
  | tail _ edgeStep inductionHypothesis =>
      exact IsTrans.trans _ _ _ inductionHypothesis (edgeMonotone edgeStep)

/-- Mutual realization reachability projects to equality in an antisymmetric logical order. -/
theorem projection_eq_of_mutual_reachable
    {Real Logical : Type*}
    {realEdge : Real → Real → Prop}
    {logicalOrder : Logical → Logical → Prop}
    [Std.Refl logicalOrder] [IsTrans Logical logicalOrder]
    (antisymmetric :
      ∀ ⦃first second : Logical⦄,
        logicalOrder first second → logicalOrder second first → first = second)
    {projection : Real → Logical}
    (edgeMonotone : EdgeMonotoneProjection realEdge logicalOrder projection)
    {first second : Real}
    (forward : Relation.ReflTransGen realEdge first second)
    (backward : Relation.ReflTransGen realEdge second first) :
    projection first = projection second :=
  antisymmetric
    (projected_reachable edgeMonotone forward)
    (projected_reachable edgeMonotone backward)

/-- A cycle may exist in the realization layer only inside one logical equivalence class. -/
theorem cycle_segment_collapses_in_partialOrder
    {Real Logical : Type*} [PartialOrder Logical]
    {realEdge : Real → Real → Prop}
    {projection : Real → Logical}
    (edgeMonotone :
      EdgeMonotoneProjection realEdge (fun first second => first ≤ second) projection)
    {first second : Real}
    (forward : Relation.ReflTransGen realEdge first second)
    (backward : Relation.ReflTransGen realEdge second first) :
    projection first = projection second := by
  exact projection_eq_of_mutual_reachable
    (fun first second forwardOrder backwardOrder => le_antisymm forwardOrder backwardOrder)
    edgeMonotone forward backward

/-- If the logical projection is injective, mutual reachability forces equality already in the realization layer. -/
theorem eq_of_mutual_reachable_of_injective
    {Real Logical : Type*} [PartialOrder Logical]
    {realEdge : Real → Real → Prop}
    {projection : Real → Logical}
    (projectionInjective : Function.Injective projection)
    (edgeMonotone :
      EdgeMonotoneProjection realEdge (fun first second => first ≤ second) projection)
    {first second : Real}
    (forward : Relation.ReflTransGen realEdge first second)
    (backward : Relation.ReflTransGen realEdge second first) :
    first = second :=
  projectionInjective
    (cycle_segment_collapses_in_partialOrder edgeMonotone forward backward)

#print axioms projection_eq_of_mutual_reachable
#print axioms cycle_segment_collapses_in_partialOrder

end D5.S3.ConceptDynamics.DagSemantics.CycleCollapseProjection
