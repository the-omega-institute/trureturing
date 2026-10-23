/- GID: D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualPiecePrefix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two retained edges at an actual simple path start force a literal prefix whose second-edge cut preserves every vertex and exactly the uncut edges. -/
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
    clear hx
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
      clear hy
      subst y
      exact ⟨h₀, h₁, q, rfl, hq.of_cons, rfl, rfl⟩

/-- Removing the actual second edge of that forced prefix leaves precisely
the one-edge first piece and the whole actual remainder, with no vertex or
uncut edge lost. This is the P split used by the joint-state update. -/
theorem actual_second_edge_cut_of_prefix {a b x y : V}
    (p : G.Walk a b) (hp : p.IsPath)
    (hax : s(a, x) ∈ p.edges) (hxy : s(x, y) ∈ p.edges) (hya : y ≠ a) :
    ∃ p₀ : G.Walk a x, ∃ p₁ : G.Walk y b,
      p₀.IsPath ∧ p₁.IsPath ∧ p₀.length = 1 ∧
      p₀.support ++ p₁.support = p.support ∧
      p₀.edges ++ [s(x, y)] ++ p₁.edges = p.edges ∧
      p₀.edges ++ p₁.edges = p.edges.filter (fun e => decide (e ≠ s(x, y))) := by
  obtain ⟨h₀, h₁, q, heq, hq, _, _⟩ :=
    actual_two_retained_edges_force_prefix p hp hax hxy hya
  have hcut : s(a, x) ≠ s(x, y) := by
    intro he
    rcases Sym2.eq_iff.mp he with ⟨he₀, _⟩ | ⟨he₀, _⟩
    · exact h₀.ne he₀
    · exact hya he₀.symm
  have hqcut : s(x, y) ∉ q.edges := by
    have hn := hp.isTrail.edges_nodup
    rw [heq] at hn
    simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hn
    exact hn.2.1
  have hf : q.edges.filter (fun e => decide (e ≠ s(x, y))) = q.edges := by
    apply List.filter_eq_self.mpr
    intro e he
    apply decide_eq_true
    intro h
    exact hqcut (h ▸ he)
  let first : G.Walk a x := SimpleGraph.Walk.cons h₀ .nil
  refine ⟨first, q, ?_, hq, rfl, ?_, ?_, ?_⟩
  · exact SimpleGraph.Walk.IsPath.nil.cons (by
      simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using h₀.ne)
  · rw [heq]
    rfl
  · rw [heq]
    rfl
  · rw [heq]
    simp only [first, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.filter_cons, hcut, ne_eq, not_false_eq_true, decide_true,
      not_true_eq_false, decide_false, ↓reduceIte, hf,
      List.singleton_append, Bool.false_eq_true]

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

/-- The forced reversed prefix records the forward occurrence of its
second edge. Its position is computed from the actual whole path length,
rather than accepted as an edge-order certificate. -/
theorem actual_retained_suffix_cut_position {a b x y : V}
    (p : G.Walk a b) (hp : p.IsPath)
    (hbx : s(b, x) ∈ p.edges) (hxy : s(x, y) ∈ p.edges) (hyb : y ≠ b) :
    ∃ i : ℕ, i < p.length ∧ p.getVert i = y ∧ p.getVert (i + 1) = x := by
  obtain ⟨h₀, h₁, q, heq, _, _, _⟩ := actual_two_retained_edges_force_prefix
    p.reverse hp.reverse
    (by simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hbx)
    (by simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hxy) hyb
  have hlength : 2 ≤ p.length := by
    have he := congrArg SimpleGraph.Walk.length heq
    simp only [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_cons] at he
    omega
  have hfirst : p.getVert (p.length - 1) = x := by
    have h : p.reverse.getVert 1 = x := by rw [heq]; rfl
    simpa only [SimpleGraph.Walk.getVert_reverse] using h
  have hsecond : p.getVert (p.length - 2) = y := by
    have h : p.reverse.getVert 2 = y := by
      rw [heq]
      change q.getVert 0 = y
      exact SimpleGraph.Walk.getVert_zero q
    simpa only [SimpleGraph.Walk.getVert_reverse] using h
  refine ⟨p.length - 2, by omega, hsecond, ?_⟩
  rw [show p.length - 2 + 1 = p.length - 1 by omega]
  exact hfirst

#print axioms actual_partition_incident_edge_owner
#print axioms actual_two_retained_edges_force_prefix
#print axioms actual_second_edge_cut_of_prefix
#print axioms actual_piece_prefix_from_retained_inventory
#print axioms actual_piece_suffix_from_retained_inventory
#print axioms actual_retained_suffix_cut_position

end D5.S3.Combinatorics.Graph.Walks.ActualPiecePrefix
