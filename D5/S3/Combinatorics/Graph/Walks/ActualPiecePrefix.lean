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

#print axioms actual_two_retained_edges_force_prefix
#print axioms actual_second_edge_cut_of_prefix

end D5.S3.Combinatorics.Graph.Walks.ActualPiecePrefix
