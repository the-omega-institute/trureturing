/- UNCOMPILED path recovery helper.
   Restoring the other marked order retains every old joint-piece edge.
   An old joint path starting at a new single-order boundary endpoint is
   therefore a literal prefix of that actual boundary path. This earns
   internal cut occurrence from the previous joint state. -/
import D5.S3.Combinatorics.Graph.Walks.ActualPiecePrefix

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualPathRecoveryPrefix

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualPiecePrefix

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- A rooted actual walk whose edges are in a disjoint path partition
stays in the starting piece. Global retained inventory thus implies local
edge inclusion without taking component ownership as a premise. -/
theorem actual_partition_rooted_walk_edges
    (pieces : List (Piece G))
    (hn : (pieces.flatMap fun z => z.walk.support).Nodup)
    (p : Piece G) (hp : p ∈ pieces) {a b : V} (q : G.Walk a b)
    (ha : a ∈ p.walk.support)
    (hkeep : ∀ e ∈ q.edges, e ∈ pieces.flatMap (fun z => z.walk.edges)) :
    ∀ e ∈ q.edges, e ∈ p.walk.edges := by
  revert ha hkeep
  induction q with
  | nil =>
    intro _ _
    simp only [SimpleGraph.Walk.edges_nil, List.not_mem_nil, false_implies, implies_true]
  | @cons a x b h q ih =>
    intro ha hkeep
    have hhead : s(a, x) ∈ p.walk.edges :=
      actual_partition_incident_edge_owner pieces hn p hp ha
        (hkeep _ (by simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]; exact Or.inl rfl))
    have hx : x ∈ p.walk.support := p.walk.snd_mem_support_of_mem_edges hhead
    have htail := ih hx (fun e he => hkeep e
      (by simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]; exact Or.inr he))
    intro e he
    simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact hhead
    · exact htail e he

/-- Sharing the start and retaining all actual edges of a simple path
forces it to be a literal prefix of another simple path. Undirected edge
inclusion cannot reverse an interior piece at the common starting point. -/
theorem actual_rooted_path_is_prefix {a b c : V}
    (q : G.Walk a b) (hq : q.IsPath) (p : G.Walk a c) (hp : p.IsPath)
    (hkeep : ∀ e ∈ q.edges, e ∈ p.edges) :
    ∃ tail : G.Walk b c, p = q.append tail ∧ tail.IsPath := by
  revert hq p
  induction q generalizing c with
  | nil =>
    intro _ p hp _
    exact ⟨p, by simp only [SimpleGraph.Walk.nil_append], hp⟩
  | @cons a x b h q ih =>
    intro hq p hp hkeep
    have hhead : s(a, x) ∈ p.edges := hkeep _
      (by simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]; exact Or.inl rfl)
    have hx : x = p.snd := hp.eq_snd_of_mem_edges hhead
    cases p with
    | nil => simp only [SimpleGraph.Walk.edges_nil, List.not_mem_nil] at hhead
    | @cons a y c h' p =>
      have hxy : x = y := by simpa only [SimpleGraph.Walk.snd_cons] using hx
      subst y
      have hsub : ∀ e ∈ q.edges, e ∈ p.edges := by
        intro e he
        have hnot : e ≠ s(a, x) := by
          intro heq
          have haq : a ∈ q.support := q.fst_mem_support_of_mem_edges (heq ▸ he)
          exact ((SimpleGraph.Walk.cons_isPath_iff h q).mp hq).2 haq
        have hmem := hkeep e (by
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]; exact Or.inr he)
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hmem
        exact hmem.resolve_left hnot
      obtain ⟨tail, he, ht⟩ := ih hq.of_cons p hp.of_cons hsub
      refine ⟨tail, ?_, ht⟩
      rw [he]
      rfl

/-- Apply the previous joint path directly to the single-order actual
pieces obtained by restoring the other marks. Its retained global edges
earn the local ownership and hence its actual prefix position. -/
theorem actual_restored_partition_joint_prefix
    (pieces : List (Piece G))
    (hn : (pieces.flatMap fun z => z.walk.support).Nodup)
    (p : Piece G) (hp : p ∈ pieces) (hpath : p.walk.IsPath)
    {b : V} (q : G.Walk p.start b) (hq : q.IsPath)
    (hkeep : ∀ e ∈ q.edges, e ∈ pieces.flatMap (fun z => z.walk.edges)) :
    ∃ tail : G.Walk b p.finish, p.walk = q.append tail ∧ tail.IsPath := by
  have hlocal := actual_partition_rooted_walk_edges pieces hn p hp q
    p.walk.start_mem_support hkeep
  exact actual_rooted_path_is_prefix q hq p.walk hpath hlocal

/-- In particular, the oriented cut just before an old joint path's
finish occurs on the same forward single-order boundary path. Its actual
position is earned from the forced joint suffix and literal recovery. -/
theorem actual_restored_joint_cut_position
    (pieces : List (Piece G))
    (hn : (pieces.flatMap fun z => z.walk.support).Nodup)
    (p : Piece G) (hp : p ∈ pieces) (hpath : p.walk.IsPath)
    {b x y : V} (q : G.Walk p.start b) (hq : q.IsPath)
    (hkeep : ∀ e ∈ q.edges, e ∈ pieces.flatMap (fun z => z.walk.edges))
    (hbx : s(b, x) ∈ q.edges) (hxy : s(x, y) ∈ q.edges) (hyb : y ≠ b) :
    ∃ i : ℕ, i < p.walk.length ∧
      p.walk.getVert i = y ∧ p.walk.getVert (i + 1) = x := by
  obtain ⟨tail, hpref, _⟩ := actual_restored_partition_joint_prefix
    pieces hn p hp hpath q hq hkeep
  obtain ⟨i, hi, hy, hx⟩ := actual_retained_suffix_cut_position q hq hbx hxy hyb
  refine ⟨i, ?_, ?_, ?_⟩
  · rw [hpref, SimpleGraph.Walk.length_append]
    omega
  · rw [hpref, SimpleGraph.Walk.getVert_append', if_pos (by omega)]
    exact hy
  · rw [hpref, SimpleGraph.Walk.getVert_append', if_pos (by omega)]
    exact hx

#print axioms actual_partition_rooted_walk_edges
#print axioms actual_rooted_path_is_prefix
#print axioms actual_restored_partition_joint_prefix
#print axioms actual_restored_joint_cut_position

end D5.S3.Combinatorics.Graph.Walks.ActualPathRecoveryPrefix
