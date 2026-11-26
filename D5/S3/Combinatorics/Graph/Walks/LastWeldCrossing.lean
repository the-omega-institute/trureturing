/- GID: D5/S3/Combinatorics/Graph/Walks/LastWeldCrossing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/LastWeldCrossing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The last weld crossing of meeting paths leaves a shortest walk in the fixed forest. -/

import D5.S3.Combinatorics.Graph.Walks.LeafNonbacktrackingComponent
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.LastWeldCrossing

open SimpleGraph
open D5.S3.Combinatorics.Graph.Walks.LeafNonbacktrackingComponent

variable {V : Type*} {G : SimpleGraph V}

private theorem path_of_nonbacktracking (h : G.IsAcyclic) {a b : V}
    (p : G.Walk a b) (hp : Nonbacktracking p) : p.IsPath := by
  apply (h.isPath_iff_isChain p).mpr
  rw [List.isChain_iff_getElem]
  intro i hi
  have hi₂ : i + 2 ≤ p.length := by
    rw [Walk.length_edges] at hi
    omega
  rw [Walk.getElem_edges, Walk.getElem_edges]
  intro he
  rcases Sym2.eq_iff.mp he with ⟨he₁, _⟩ | ⟨he₁, _⟩
  · exact (p.adj_getVert_succ (by omega : i < p.length)).ne he₁
  · exact hp i hi₂ he₁

private theorem tree_suffix_distance (h : G.IsAcyclic) {a b : V}
    (p : G.Walk a b) (hp : Nonbacktracking p) :
    p.IsPath ∧ p.length = G.dist a b := by
  have hPath := path_of_nonbacktracking h p hp
  obtain ⟨q, hq⟩ := p.reachable.exists_walk_length_eq_dist
  have hSame : p = q :=
    congrArg Subtype.val ((h.subsingleton_path a b).elim
      ⟨p, hPath⟩ ⟨q, q.isPath_of_length_eq_dist hq⟩)
  exact ⟨hPath, hSame ▸ hq⟩

private theorem weld_edge_of_nonempty_closed_suffix {H W : SimpleGraph V} (h : H.IsAcyclic)
    {a : V} (p : (H ⊔ W).Walk a a) (hp : Nonbacktracking p) (hn : 0 < p.length) :
    ∃ edge ∈ p.edges, edge ∈ W.edgeSet ∧ edge ∉ H.edgeSet := by
  classical
  by_contra hNo
  push Not at hNo
  have hEdges : ∀ edge ∈ p.edges, edge ∈ H.edgeSet := by
    intro edge he
    rcases (by
      simpa only [edgeSet_sup, Set.mem_union] using p.edges_subset_edgeSet he :
        edge ∈ H.edgeSet ∨ edge ∈ W.edgeSet) with hH | hW
    · exact hH
    · exact hNo edge he hW
  let q := p.transfer H hEdges
  have hLen : q.length = p.length := p.length_transfer hEdges
  have hSupport : q.support = p.support := p.support_transfer hEdges
  have hNB : Nonbacktracking q := by
    intro i hi
    have hi' : i + 2 ≤ p.length := hLen ▸ hi
    have he (j : ℕ) (hj : j ≤ q.length) :
        q.getVert j = p.getVert j := by
      rw [Walk.getVert_eq_support_getElem q hj,
        Walk.getVert_eq_support_getElem p (hLen ▸ hj)]
      simp only [hSupport]
    rw [he i (by omega), he (i + 2) hi]
    exact hp i hi'
  have hDist := (tree_suffix_distance h q hNB).2
  rw [SimpleGraph.dist_self, hLen] at hDist
  omega

private theorem nonbacktracking_of_chain {a b : V} (p : G.Walk a b)
    (h : p.edges.IsChain (· ≠ ·)) : Nonbacktracking p := by
  intro i hi he
  have hlt : i + 1 < p.edges.length := by
    rw [Walk.length_edges]
    omega
  have hne := List.isChain_iff_getElem.mp h i hlt
  rw [Walk.getElem_edges, Walk.getElem_edges] at hne
  apply hne
  rw [he]
  exact Sym2.eq_swap

/-- The last crossing outside the fixed forest leaves a shortest forest tail. -/
private theorem last_weld_then_tree_distance {H W : SimpleGraph V} (h : H.IsAcyclic)
    {a b : V} (p : (H ⊔ W).Walk a b) (hp : Nonbacktracking p)
    (hCross : ∃ e ∈ p.edges, e ∉ H.edgeSet) :
    ∃ j < p.length,
      W.Adj (p.getVert j) (p.getVert (j + 1)) ∧
      ¬ H.Adj (p.getVert j) (p.getVert (j + 1)) ∧
      ∃ q : H.Walk (p.getVert (j + 1)) b, q.IsPath ∧
        q.support = (p.drop (j + 1)).support ∧
        q.length = p.length - (j + 1) ∧ q.length = H.dist (p.getVert (j + 1)) b := by
  classical
  let isCrossing := fun i => i < p.length ∧ ¬ H.Adj (p.getVert i) (p.getVert (i + 1))
  have hCrossing : ∃ i ≤ p.length, isCrossing i := by
    obtain ⟨e, he, hOutside⟩ := hCross
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
    rw [p.getElem_edges] at hOutside
    rw [Walk.length_edges] at hi
    exact ⟨i, hi.le, hi, by simpa only [mem_edgeSet] using hOutside⟩
  obtain ⟨i, hi, hiCross⟩ := hCrossing
  let j := Nat.findGreatest isCrossing p.length
  have hj : isCrossing j := Nat.findGreatest_spec hi hiCross
  have hW : W.Adj (p.getVert j) (p.getVert (j + 1)) :=
    (p.adj_getVert_succ hj.1).resolve_left hj.2
  let tail := p.drop (j + 1)
  have hFixed : ∀ e ∈ tail.edges, e ∈ H.edgeSet := by
    intro e he
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp he
    have hk' : k < p.length - (j + 1) := by
      simpa only [Walk.length_edges, tail, Walk.drop_length] using hk
    have hlt : j + 1 + k < p.length := by omega
    have hLate := Nat.findGreatest_is_greatest (P := isCrossing)
      (show j < j + 1 + k by omega) hlt.le
    rw [tail.getElem_edges]
    simp only [tail, Walk.drop_getVert, mem_edgeSet]
    exact not_not.mp (fun hn => hLate ⟨hlt, by simpa only [Nat.add_assoc] using hn⟩)
  let q := tail.transfer H hFixed
  have hSupport : q.support = tail.support := tail.support_transfer hFixed
  have hLen : q.length = p.length - (j + 1) := by
    rw [tail.length_transfer hFixed]
    exact p.drop_length (j + 1)
  have hTailLen : q.length = tail.length := tail.length_transfer hFixed
  have hNB : Nonbacktracking q := by
    intro k hk
    have hVert (m : ℕ) (hm : m ≤ q.length) :
        q.getVert m = tail.getVert m := by
      rw [q.getVert_eq_support_getElem hm, tail.getVert_eq_support_getElem (hTailLen ▸ hm)]
      simp only [hSupport]
    rw [hVert k (by omega), hVert (k + 2) hk]
    simp only [tail, Walk.drop_getVert]
    simpa only [Nat.add_assoc] using hp (j + 1 + k) (by omega)
  obtain ⟨hPath, hDist⟩ := tree_suffix_distance h q hNB
  exact ⟨j, hj.1, hW, hj.2, q, hPath, hSupport, hLen, hDist⟩

/-- Two paths with distinct final edges enclose a weld crossing. After the last such
crossing in their concatenation, the remaining forest walk has minimum length. -/
theorem meeting_arms_last_weld {H W : SimpleGraph V} (hForest : H.IsAcyclic)
    {a b : V} (p q : (H ⊔ W).Walk a b)
    (hp : p.IsPath) (hq : q.IsPath)
    (hJoin : ∀ e ∈ p.edges.getLast?, ∀ f ∈ q.edges.getLast?, e ≠ f)
    (hLen : 0 < p.length + q.length) :
    let closed := p.append q.reverse
    ∃ j < closed.length,
      W.Adj (closed.getVert j) (closed.getVert (j + 1)) ∧
      ¬ H.Adj (closed.getVert j) (closed.getVert (j + 1)) ∧
      ∃ tail : H.Walk (closed.getVert (j + 1)) a, tail.IsPath ∧
        tail.support = (closed.drop (j + 1)).support ∧
        tail.length = closed.length - (j + 1) ∧
        tail.length = H.dist (closed.getVert (j + 1)) a := by
  intro closed
  have hChain : closed.edges.IsChain (· ≠ ·) := by
    change (p.append q.reverse).edges.IsChain (· ≠ ·)
    rw [Walk.edges_append]
    refine hp.isTrail.edges_nodup.isChain.append hq.reverse.isTrail.edges_nodup.isChain ?_
    simpa only [Walk.edges_reverse, List.head?_reverse] using hJoin
  have hNB := nonbacktracking_of_chain closed hChain
  have hPositive : 0 < closed.length := by
    simpa only [closed, Walk.length_append, Walk.length_reverse] using hLen
  obtain ⟨e, he, _, hOutside⟩ :=
    weld_edge_of_nonempty_closed_suffix hForest closed hNB hPositive
  exact last_weld_then_tree_distance hForest closed hNB ⟨e, he, hOutside⟩

end D5.S3.Combinatorics.Graph.Walks.LastWeldCrossing
