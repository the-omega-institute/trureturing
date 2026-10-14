/- GID: D5/S3/Combinatorics/Graph/Walks/ActualPartitionTransport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualPartitionTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Map the same cycle, pieces and cuts through an injective graph homomorphism. -/
import D5.S3.Combinatorics.Graph.Walks.EdgeSlicing

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing

universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- Map a piece as data, including its literal endpoints and walk. -/
def mapPiece (f : G →g H) (p : Piece G) : Piece H :=
  ⟨f p.start, f p.finish, p.walk.map f⟩

private theorem mapped_supports (f : G →g H) (pieces : List (Piece G)) :
    ((pieces.map (mapPiece f)).flatMap fun p => p.walk.support) =
      (pieces.flatMap fun p => p.walk.support).map f := by
  induction pieces with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.flatMap_cons, mapPiece,
      SimpleGraph.Walk.support_map, List.map_append, ih]

private theorem mapped_edges (f : G →g H) (pieces : List (Piece G)) :
    ((pieces.map (mapPiece f)).flatMap fun p => p.walk.edges) =
      (pieces.flatMap fun p => p.walk.edges).map (Sym2.map f) := by
  induction pieces with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.flatMap_cons, mapPiece,
      SimpleGraph.Walk.edges_map, List.map_append, ih]

private theorem map_filtered_complement {α : Type*} {β : Type*}
    [DecidableEq α] [DecidableEq β] (f : α → β) (hf : Function.Injective f)
    (whole : List α) (cuts : Finset α) :
    (whole.filter fun e => decide (e ∉ cuts)).map f =
      (whole.map f).filter fun e => decide (e ∉ cuts.image f) := by
  classical
  have hmem (e : α) : f e ∈ cuts.image f ↔ e ∈ cuts := by
    constructor
    · intro he
      obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp he
      exact (hf hxe) ▸ hx
    · intro he
      exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  induction whole with
  | nil => rfl
  | cons e es ih =>
    by_cases he : e ∈ cuts
    · simp only [List.filter_cons, List.map_cons, he, (hmem e).mpr he,
        not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, ih]
    · have hfe : f e ∉ cuts.image f := fun h => he ((hmem e).mp h)
      simp only [List.filter_cons, List.map_cons, he, hfe, not_false_eq_true,
        decide_true, ↓reduceIte, ih]

/-- The target partition is the image of these particular source pieces
and this particular cycle. Injectivity, rather than a new partition
certificate, earns every target support and uncut-edge fact. -/
theorem actual_cycle_partition_map (f : G →g H) (hf : Function.Injective f)
    {a : V} (c : G.Walk a a) (hc : c.IsCycle)
    (pieces : List (Piece G)) (cuts : Finset (Sym2 V))
    (hsupport : (pieces.flatMap fun p => p.walk.support).Perm c.support.tail)
    (hedges : (pieces.flatMap fun p => p.walk.edges).Perm
      (c.edges.filter fun e => decide (e ∉ cuts)))
    (hcuts : ∀ e ∈ cuts, e ∈ c.edges) :
    let mapped := pieces.map (mapPiece f)
    (c.map f).IsCycle ∧
      (∀ p ∈ mapped, p.walk.IsPath) ∧
      (mapped.flatMap fun p => p.walk.support).Perm (c.map f).support.tail ∧
      (mapped.flatMap fun p => p.walk.edges).Perm
        ((c.map f).edges.filter fun e => decide (e ∉ cuts.image (Sym2.map f))) ∧
      (∀ e ∈ cuts.image (Sym2.map f), e ∈ (c.map f).edges) := by
  classical
  dsimp only
  have hcycle : (c.map f).IsCycle :=
    (SimpleGraph.Walk.isCycle_map_iff_of_injective hf).mpr hc
  have hsupport' : ((pieces.map (mapPiece f)).flatMap fun p => p.walk.support).Perm
      (c.map f).support.tail := by
    rw [mapped_supports, SimpleGraph.Walk.support_map, ← List.map_tail]
    exact hsupport.map f
  have hn : ((pieces.map (mapPiece f)).flatMap fun p => p.walk.support).Nodup :=
    hsupport'.nodup_iff.mpr hcycle.support_nodup
  refine ⟨hcycle, ?_, hsupport', ?_, ?_⟩
  · intro p hp
    exact SimpleGraph.Walk.IsPath.mk' ((List.nodup_flatMap.mp hn).1 p hp)
  · rw [mapped_edges, SimpleGraph.Walk.edges_map,
      ← map_filtered_complement (Sym2.map f) (Sym2.map.injective hf)]
    exact hedges.map (Sym2.map f)
  · intro e he
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp he
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨x, hcuts x hx, hxe⟩

#print axioms actual_cycle_partition_map

end D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport
