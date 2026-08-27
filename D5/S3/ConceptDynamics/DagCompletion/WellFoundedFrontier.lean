/- GID: D5/S3/ConceptDynamics/DagCompletion/WellFoundedFrontier
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagCompletion/WellFoundedFrontier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every nonempty pending set has an executable node under a well-founded prerequisite relation. -/

import D5.S3.ConceptDynamics.DagSemantics.ExecutableFrontier
import Mathlib.Order.WellFounded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagCompletion.WellFoundedFrontier

open D5.S3.ConceptDynamics.DagSemantics.ExecutableFrontier

/-- A well-founded prerequisite relation gives every nonempty pending set a ready member. -/
theorem exists_ready_of_wellFounded
    {V : Type*} {edge : V → V → Prop}
    (wellFounded : WellFounded edge)
    {pending : Set V} (pendingNonempty : pending.Nonempty) :
    ∃ node ∈ pending, ReadyOver edge pendingᶜ node := by
  obtain ⟨node, nodeInPending, minimal⟩ :=
    wellFounded.has_min pending pendingNonempty
  refine ⟨node, nodeInPending, ?_⟩
  intro prerequisite dependency
  change prerequisite ∉ pending
  intro prerequisiteInPending
  exact minimal prerequisite prerequisiteInPending dependency

/-- Hence the executable frontier over the completed complement is nonempty. -/
theorem complement_frontier_nonempty_of_wellFounded
    {V : Type*} {edge : V → V → Prop}
    (wellFounded : WellFounded edge)
    {pending : Set V} (pendingNonempty : pending.Nonempty) :
    (executableFrontier edge pendingᶜ pending).Nonempty := by
  obtain ⟨node, nodeInPending, ready⟩ :=
    exists_ready_of_wellFounded wellFounded pendingNonempty
  exact ⟨node, nodeInPending, ready⟩

/-- If a pending set has no executable node, it must be empty. -/
theorem pending_empty_of_frontier_empty
    {V : Type*} {edge : V → V → Prop}
    (wellFounded : WellFounded edge)
    {pending : Set V}
    (frontierEmpty : executableFrontier edge pendingᶜ pending = ∅) :
    pending = ∅ := by
  apply Set.Subset.antisymm
  · intro node nodeInPending
    have pendingNonempty : pending.Nonempty := ⟨node, nodeInPending⟩
    obtain ⟨frontierNode, frontierNodeIn⟩ :=
      complement_frontier_nonempty_of_wellFounded wellFounded pendingNonempty
    rw [frontierEmpty] at frontierNodeIn
    exact frontierNodeIn
  · exact Set.empty_subset pending

/-- A dependency deadlock in a nonempty pending set certifies non-well-foundedness. -/
theorem deadlock_implies_not_wellFounded
    {V : Type*} {edge : V → V → Prop}
    {pending : Set V} (pendingNonempty : pending.Nonempty)
    (frontierEmpty : executableFrontier edge pendingᶜ pending = ∅) :
    ¬ WellFounded edge := by
  intro wellFounded
  obtain ⟨frontierNode, frontierNodeIn⟩ :=
    complement_frontier_nonempty_of_wellFounded wellFounded pendingNonempty
  rw [frontierEmpty] at frontierNodeIn
  exact frontierNodeIn

#print axioms complement_frontier_nonempty_of_wellFounded
#print axioms deadlock_implies_not_wellFounded

end D5.S3.ConceptDynamics.DagCompletion.WellFoundedFrontier
