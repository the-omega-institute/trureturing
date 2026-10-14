/- UNCOMPILED snippet for NativeJ2SurvivingEdges after its actual slice model.
These helpers use actual support disjointness and actual edge inventory.
Neither connectedness nor component coverage is an input.
-/

private theorem partition_piece_full_component {V : Type*} [DecidableEq V]
    {G : SimpleGraph V}
    (pieces : List (D5.S3.Combinatorics.Graph.Walks.EdgeSlicing.Piece G))
    (hn : (pieces.flatMap fun z => z.walk.support).Nodup)
    (hedges : ∀ x y, G.Adj x y → s(x, y) ∈ (pieces.flatMap fun z => z.walk.edges))
    (p : D5.S3.Combinatorics.Graph.Walks.EdgeSlicing.Piece G) (hp : p ∈ pieces) :
    (∀ x, x ∈ p.walk.support ↔ G.Reachable p.start x) ∧
      ∀ x y, G.Adj x y ∧ G.Reachable p.start x ↔ s(x, y) ∈ p.walk.edges := by
  letI : Std.Symm (fun p q : D5.S3.Combinatorics.Graph.Walks.EdgeSlicing.Piece G =>
      List.Disjoint p.walk.support q.walk.support) := ⟨fun _ _ h => h.symm⟩
  have hd := (List.nodup_flatMap.mp hn).2
  have hsaturated : ∀ x y, x ∈ p.walk.support → G.Adj x y → p.walk.toSubgraph.Adj x y := by
    intro x y hx hxy
    obtain ⟨q, hq, he⟩ := List.mem_flatMap.mp (hedges x y hxy)
    have hqx := q.walk.fst_mem_support_of_mem_edges he
    have hqp : q = p := by
      by_contra hne
      exact List.disjoint_left.mp (hd.forall hq hp hne) hqx hx
    subst q
    exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr he
  have hvertices : ∀ x, x ∈ p.walk.support ↔ G.Reachable p.start x := by
    intro x
    constructor
    · intro hx
      exact (p.walk.takeUntil x hx).reachable
    · intro hx
      exact p.walk.mem_verts_toSubgraph.mp
        (hx.mem_subgraphVerts (H := p.walk.toSubgraph)
          (fun y hy z hyz => hsaturated y z (p.walk.mem_verts_toSubgraph.mp hy) hyz)
          p.walk.start_mem_verts_toSubgraph)
  refine ⟨hvertices, ?_⟩
  intro x y
  constructor
  · rintro ⟨hxy, hx⟩
    exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp
      (hsaturated x y ((hvertices x).mpr hx) hxy)
  · intro he
    have hs := SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr he
    exact ⟨hs.adj_sub, (hvertices x).mp
      (SimpleGraph.Walk.mem_support_of_adj_toSubgraph hs)⟩

/-- A graph leaf cannot occur strictly inside an actual simple path. -/
private theorem leaf_in_path_is_endpoint {V : Type*} [DecidableEq V] [Finite V]
    {G : SimpleGraph V} {a b x : V} (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∈ p.support) (hleaf : (G.neighborSet x).Subsingleton) :
    x = a ∨ x = b := by
  obtain ⟨i, hi, hib⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  by_cases hi0 : i = 0
  · left
    simpa only [hi0, SimpleGraph.Walk.getVert_zero] using hi.symm
  · by_cases hil : i = p.length
    · right
      simpa only [hil, SimpleGraph.Walk.getVert_length] using hi.symm
    · have hilt : i < p.length := by omega
      have htwo := hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt
      have hs : p.toSubgraph.neighborSet (p.getVert i) ⊆ G.neighborSet (p.getVert i) :=
        fun _ h => h.adj_sub
      have hle := Set.ncard_le_ncard hs
      have hone : (G.neighborSet (p.getVert i)).ncard ≤ 1 := by
        rw [hi]
        exact Set.ncard_le_one_iff_subsingleton.mpr hleaf
      omega

#print axioms partition_piece_full_component
#print axioms leaf_in_path_is_endpoint
