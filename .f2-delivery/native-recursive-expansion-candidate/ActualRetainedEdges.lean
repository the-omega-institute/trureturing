/- GID: D5/S3/Combinatorics/Graph/Walks/ActualRetainedEdges
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualRetainedEdges
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Closing an actual piece chain preserves every retained child edge. -/
import D5.S3.Combinatorics.Graph.Walks.PathRingSplicing

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualRetainedEdges

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing

universe u
variable {V : Type u} {G : SimpleGraph V}

theorem actual_chain_keeps_piece_edges (p : Piece G) (ps : List (Piece G))
    (z : Piece G) (hz : z ∈ p :: ps) (e : Sym2 V) (he : e ∈ z.walk.edges) :
    e ∈ chainEdges p ps := by
  induction ps generalizing p with
  | nil =>
    simp only [List.mem_singleton] at hz
    subst z
    exact he
  | cons q qs ih =>
    simp only [List.mem_cons] at hz
    simp only [chainEdges, List.mem_append, List.mem_cons]
    rcases hz with rfl | hq | hqs
    · exact Or.inl he
    · exact Or.inr (Or.inr (ih q (by simp only [List.mem_cons]; exact Or.inl hq)))
    · exact Or.inr (Or.inr (ih q (List.mem_cons_of_mem q hqs)))

/-- The support-independent literal parent inventory preserves all
retained child edges, in either orientation of the closing construction. -/
theorem actual_closed_route_keeps_piece_edges
    (p : Piece G) (ps : List (Piece G)) {a : V} (c : G.Walk a a)
    (hclose : c.edges = s(a, finish p ps) :: (chainEdges p ps).reverse)
    (z : Piece G) (hz : z ∈ p :: ps) (e : Sym2 V) (he : e ∈ z.walk.edges) :
    e ∈ c.edges := by
  rw [hclose, List.mem_cons]
  exact Or.inr (List.mem_reverse.mpr (actual_chain_keeps_piece_edges p ps z hz e he))

#print axioms actual_chain_keeps_piece_edges
#print axioms actual_closed_route_keeps_piece_edges

end D5.S3.Combinatorics.Graph.Walks.ActualRetainedEdges
