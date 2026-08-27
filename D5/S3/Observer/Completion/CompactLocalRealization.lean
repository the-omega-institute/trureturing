/- GID: D5/S3/Observer/Completion/CompactLocalRealization
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/CompactLocalRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compactness turns finite local realizability of closed records into a global record. -/

import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Completion.CompactLocalRealization

theorem compact_local_realization
    {X Context Record : Type*} [TopologicalSpace X] [CompactSpace X]
    (beta : Context → X → Record) (target : Context → Record)
    (closed : ∀ context, IsClosed {x | beta context x = target context})
    (finite_realizable : ∀ contexts : Finset Context,
      ∃ x, ∀ context ∈ contexts, beta context x = target context) :
    ∃ x, ∀ context, beta context x = target context := by
  have finite_intersections :
      ∀ contexts : Finset Context,
        (⋂ context ∈ contexts, {x | beta context x = target context}).Nonempty := by
    intro contexts
    obtain ⟨x, hx⟩ := finite_realizable contexts
    refine ⟨x, ?_⟩
    simp only [Set.mem_iInter]
    intro context hcontext
    exact hx context hcontext
  have all_intersection :
      (⋂ context, {x | beta context x = target context}).Nonempty :=
    CompactSpace.iInter_nonempty closed finite_intersections
  obtain ⟨x, hx⟩ := all_intersection
  refine ⟨x, ?_⟩
  exact Set.mem_iInter.mp hx

#print axioms compact_local_realization

end D5.S3.Observer.Completion.CompactLocalRealization
