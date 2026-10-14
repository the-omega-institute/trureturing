/- UNCOMPILED generic helper for the actual J-state propagation.
   A retained edge incident to an actual piece vertex belongs to that same
   piece. Two such retained edges at its start therefore give its literal
   two-edge prefix. Neither a degree bound nor a path prefix is assumed. -/
import D5.S3.Combinatorics.Graph.Walks.EdgeSlicing

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualPiecePrefix

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- Disjoint actual supports assign every retained edge to its unique
actual piece. This is an ownership consequence of the partition itself. -/
theorem actual_partition_incident_edge_owner
    (pieces : List (Piece G))
    (hn : (pieces.flatMap fun z => z.walk.support).Nodup)
    (p : Piece G) (hp : p ∈ pieces) {x y : V}
    (hx : x ∈ p.walk.support)
    (he : s(x, y) ∈ pieces.flatMap (fun z => z.walk.edges)) :
    s(x, y) ∈ p.walk.edges := by
  letI : Std.Symm (fun p q : Piece G => List.Disjoint p.walk.support q.walk.support) :=
    ⟨fun _ _ h => h.symm⟩
  have hd := (List.nodup_flatMap.mp hn).2
  obtain ⟨q, hq, heq⟩ := List.mem_flatMap.mp he
  have hqx := q.walk.fst_mem_support_of_mem_edges heq
  have hqp : q = p := by
    by_contra hne
    exact List.disjoint_left.mp (hd.forall hq hp hne) hqx hx
  exact hqp ▸ heq

/-- A simple actual path containing two successive edges at its start
must traverse them as its actual prefix. The second edge's other endpoint
is distinct from the start, ruling out the same undirected edge twice. -/
theorem actual_two_retained_edges_force_prefix {a b x y : V}
    (p : G.Walk a b) (hp : p.IsPath)
    (hax : s(a, x) ∈ p.edges) (hxy : s(x, y) ∈ p.edges) (hya : y ≠ a) :
    ∃ (h₀ : G.Adj a x) (h₁ : G.Adj x y) (q : G.Walk y b),
      p = (q.cons h₁).cons h₀ ∧ q.IsPath ∧
      p.support = a :: x :: q.support ∧
      p.edges = s(a, x) :: s(x, y) :: q.edges := by
  have hx : x = p.snd := hp.eq_snd_of_mem_edges hax
  cases p with
  | nil => simp only [SimpleGraph.Walk.edges_nil, List.not_mem_nil] at hax
  | @cons a z b h₀ p =>
    have hxz : x = z := by simpa only [SimpleGraph.Walk.snd_cons] using hx
    subst x
    have hfirst : s(z, y) ≠ s(a, z) := by
      intro he
      rcases Sym2.eq_iff.mp he with ⟨he₀, _⟩ | ⟨_, he₁⟩
      · exact h₀.ne he₀.symm
      · exact hya he₁
    have heq : s(z, y) ∈ p.edges := by
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hxy
      exact hxy.resolve_left hfirst
    have hq := hp.of_cons
    have hy : y = p.snd := hq.eq_snd_of_mem_edges heq
    cases p with
    | nil => simp only [SimpleGraph.Walk.edges_nil, List.not_mem_nil] at heq
    | @cons z w b h₁ q =>
      have hyw : y = w := by simpa only [SimpleGraph.Walk.snd_cons] using hy
      subst y
      exact ⟨h₀, h₁, q, rfl, hq.of_cons, rfl, rfl⟩

/-- Global retained-edge membership is enough to obtain both local edges,
then the actual prefix, at a selected actual partition piece's start. -/
theorem actual_piece_prefix_from_retained_inventory
    (pieces : List (Piece G))
    (hn : (pieces.flatMap fun z => z.walk.support).Nodup)
    (p : Piece G) (hp : p ∈ pieces) (hpath : p.walk.IsPath)
    {x y : V}
    (h₀ : s(p.start, x) ∈ pieces.flatMap (fun z => z.walk.edges))
    (h₁ : s(x, y) ∈ pieces.flatMap (fun z => z.walk.edges)) (hy : y ≠ p.start) :
    ∃ (hstart : G.Adj p.start x) (hnext : G.Adj x y) (q : G.Walk y p.finish),
      p.walk = (q.cons hnext).cons hstart ∧ q.IsPath ∧
      p.walk.support = p.start :: x :: q.support ∧
      p.walk.edges = s(p.start, x) :: s(x, y) :: q.edges := by
  have he₀ := actual_partition_incident_edge_owner pieces hn p hp
    p.walk.start_mem_support h₀
  have hx := p.walk.snd_mem_support_of_mem_edges he₀
  have he₁ := actual_partition_incident_edge_owner pieces hn p hp hx h₁
  exact actual_two_retained_edges_force_prefix p.walk hpath he₀ he₁ hy

/-- At a piece's finish the same argument yields a literal reversed prefix.
This is the suffix needed when a restored route reaches an old left port. -/
theorem actual_piece_suffix_from_retained_inventory
    (pieces : List (Piece G))
    (hn : (pieces.flatMap fun z => z.walk.support).Nodup)
    (p : Piece G) (hp : p ∈ pieces) (hpath : p.walk.IsPath)
    {x y : V}
    (h₀ : s(p.finish, x) ∈ pieces.flatMap (fun z => z.walk.edges))
    (h₁ : s(x, y) ∈ pieces.flatMap (fun z => z.walk.edges)) (hy : y ≠ p.finish) :
    ∃ (hfinish : G.Adj p.finish x) (hnext : G.Adj x y) (q : G.Walk y p.start),
      p.walk.reverse = (q.cons hnext).cons hfinish ∧ q.IsPath ∧
      p.walk.support.reverse = p.finish :: x :: q.support ∧
      p.walk.edges.reverse = s(p.finish, x) :: s(x, y) :: q.edges := by
  have he₀ := actual_partition_incident_edge_owner pieces hn p hp
    p.walk.end_mem_support h₀
  have hx := p.walk.snd_mem_support_of_mem_edges he₀
  have he₁ := actual_partition_incident_edge_owner pieces hn p hp hx h₁
  obtain ⟨ha, hb, q, hq, hpathq, hs, he⟩ :=
    actual_two_retained_edges_force_prefix p.walk.reverse hpath.reverse
      (by simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using he₀)
      (by simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using he₁) hy
  refine ⟨ha, hb, q, hq, hpathq, ?_, ?_⟩
  · simpa only [SimpleGraph.Walk.support_reverse] using hs
  · simpa only [SimpleGraph.Walk.edges_reverse] using he

#print axioms actual_partition_incident_edge_owner
#print axioms actual_two_retained_edges_force_prefix
#print axioms actual_piece_prefix_from_retained_inventory
#print axioms actual_piece_suffix_from_retained_inventory

end D5.S3.Combinatorics.Graph.Walks.ActualPiecePrefix
