/- GID: D5/S3/Combinatorics/Graph/Walks/ActualRestoredBoundaryRecovery
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualRestoredBoundaryRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recover Whole Actual Boundary Pieces from Retained Routes. -/
import D5.S3.Combinatorics.Graph.Walks.ActualPathRecoveryPrefix

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualRestoredBoundaryRecovery

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualPathRecoveryPrefix

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- A retained simple path cannot pass internally through an endpoint of
an actual removed cycle edge: its two internal neighbours would already
exhaust the two source-cycle neighbours. -/
theorem actual_missing_cycle_edge_forces_path_endpoint
    {base a b x y : V} (c : G.Walk base base) (hc : c.IsHamiltonianCycle)
    (p : G.Walk a b) (hp : p.IsPath) (hx : x ∈ p.support)
    (hkeep : ∀ e ∈ p.edges, e ∈ c.edges)
    (hcut : s(x, y) ∈ c.edges) (hmissing : s(x, y) ∉ p.edges) :
    x = a ∨ x = b := by
  letI : Finite V := hc.finite
  obtain ⟨i, hi, hil⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  by_cases hi0 : i = 0
  · left
    simpa only [hi0, SimpleGraph.Walk.getVert_zero] using hi.symm
  · by_cases hie : i = p.length
    · right
      simpa only [hie, SimpleGraph.Walk.getVert_length] using hi.symm
    · have hilt : i < p.length := by omega
      have hpdegree : (p.toSubgraph.neighborSet x).ncard = 2 := by
        rw [← hi]
        exact hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt
      have hcdegree : (c.toSubgraph.neighborSet x).ncard = 2 :=
        hc.isCycle.ncard_neighborSet_toSubgraph_eq_two
          (c.fst_mem_support_of_mem_edges hcut)
      have hsub : p.toSubgraph.neighborSet x ⊆ c.toSubgraph.neighborSet x := by
        intro z hz
        exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr
          (hkeep _ (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp hz))
      have heq : p.toSubgraph.neighborSet x = c.toSubgraph.neighborSet x :=
        Set.eq_of_subset_of_ncard_le hsub (by rw [hcdegree, hpdegree])
      have hyc : y ∈ c.toSubgraph.neighborSet x :=
        SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr hcut
      have hyp : y ∈ p.toSubgraph.neighborSet x := heq.symm ▸ hyc
      exact (hmissing (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp hyp)).elim

/-- A previous-joint route uses only edges retained after restoration.
Its start roots it in an actual restored slice. Its finish is incident to
one actual still-deleted edge and differs from its start, which earns the
other endpoint and literal full support/edge recovery. -/
theorem actual_restored_joint_route_recovers_whole_piece
    {base : V} (c : G.Walk base base) (hc : c.IsHamiltonianCycle)
    (E : Finset (Sym2 V)) (pieces : List (Piece G))
    (hn : (pieces.flatMap fun z => z.walk.support).Nodup)
    (hinv : ∀ e, e ∈ (pieces.flatMap fun z => z.walk.edges) ↔
      e ∈ c.edges ∧ e ∉ E)
    (p : Piece G) (hp : p ∈ pieces) (hpath : p.walk.IsPath)
    {b y : V} (q : G.Walk p.start b) (hq : q.IsPath)
    (hkeep : ∀ e ∈ q.edges, e ∈ (pieces.flatMap fun z => z.walk.edges))
    (hneq : b ≠ p.start) (hcut : s(b, y) ∈ E) (hactual : s(b, y) ∈ c.edges) :
    p.finish = b ∧ p.walk.support = q.support ∧ p.walk.edges = q.edges := by
  obtain ⟨tail, hpref, htail⟩ :=
    actual_restored_partition_joint_prefix pieces hn p hp hpath q hq hkeep
  have hb : b ∈ p.walk.support := by
    rw [hpref]
    exact SimpleGraph.Walk.support_subset_support_append_left q tail q.end_mem_support
  have hparent : ∀ e ∈ p.walk.edges, e ∈ c.edges := by
    intro e he
    exact ((hinv e).mp (List.mem_flatMap.mpr ⟨p, hp, he⟩)).1
  have hmissing : s(b, y) ∉ p.walk.edges := by
    intro he
    exact ((hinv _).mp (List.mem_flatMap.mpr ⟨p, hp, he⟩)).2 hcut
  have hfinish : b = p.finish := by
    rcases actual_missing_cycle_edge_forces_path_endpoint c hc p.walk hpath hb
      hparent hactual hmissing with hstart | hfinish
    · exact (hneq hstart).elim
    · exact hfinish
  subst b
  have hnil : tail = SimpleGraph.Walk.nil :=
    SimpleGraph.Walk.isPath_iff_eq_nil.mp htail
  rw [hnil, SimpleGraph.Walk.append_nil] at hpref
  exact ⟨rfl, congrArg (fun w => w.support) hpref, congrArg (fun w => w.edges) hpref⟩

#print axioms actual_missing_cycle_edge_forces_path_endpoint
#print axioms actual_restored_joint_route_recovers_whole_piece

end D5.S3.Combinatorics.Graph.Walks.ActualRestoredBoundaryRecovery
