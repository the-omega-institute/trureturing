/- GID: D5/S3/Combinatorics/Graph/LeafNonbacktrackingComponent
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LeafNonbacktrackingComponent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hamiltonian, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph]
   utility: none
   digest: Nonbacktracking leaf walks in finite degree-two graphs earn simplicity and exhaust their actual path components. -/
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-! A finite degree-two graph turns an actual nonbacktracking leaf-to-leaf
walk into the entire path component. No path or coverage is assumed. -/
namespace D5.S3.Combinatorics.Graph.LeafNonbacktrackingComponent

open SimpleGraph

universe u
variable {V : Type u} [DecidableEq V] [Finite V] {G : SimpleGraph V}

/-- Consecutive actual edges never immediately return to the preceding vertex. -/
def Nonbacktracking {a b : V} (p : G.Walk a b) : Prop :=
  ∀ i, i + 2 ≤ p.length → p.getVert i ≠ p.getVert (i + 2)

private theorem prefix_adj_saturated {a b x y : V} {p : G.Walk a b}
    (hdegree : ∀ z, (G.neighborSet z).ncard ≤ 2)
    (ha : (G.neighborSet a).Subsingleton) (hp : p.IsPath)
    (hx : x ∈ p.support) (hxb : x ≠ b) (hxy : G.Adj x y) :
    p.toSubgraph.Adj x y := by
  by_cases hxa : x = a
  · subst x
    have hnil : ¬p.Nil := by
      intro h
      cases h
      exact hxb rfl
    have he : y = p.snd := ha hxy (p.adj_snd hnil)
    rw [he]
    exact p.toSubgraph_adj_snd hnil
  · obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    have hi0 : i ≠ 0 := by
      intro h
      subst i
      simp only [Walk.getVert_zero] at hi
      exact hxa hi.symm
    have hib : i < p.length := by
      by_contra h
      have he : i = p.length := by omega
      subst i
      simp only [Walk.getVert_length] at hi
      exact hxb hi.symm
    have hcard : (p.toSubgraph.neighborSet x).ncard = 2 := by
      rw [← hi]
      exact hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hib
    have he : p.toSubgraph.neighborSet x = G.neighborSet x :=
      Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset x)
        (by rw [hcard]; exact hdegree x)
    change y ∈ p.toSubgraph.neighborSet x
    rw [he]
    exact hxy

private theorem path_extend {a b c : V} {p : G.Walk a b}
    (hdegree : ∀ z, (G.neighborSet z).ncard ≤ 2)
    (ha : (G.neighborSet a).Subsingleton) (hp : p.IsPath)
    (hbc : G.Adj b c) (hnb : ¬p.Nil → p.penultimate ≠ c) :
    (p.concat hbc).IsPath := by
  apply hp.concat ?_ hbc
  intro hc
  by_cases hnil : p.Nil
  · cases hnil
    simp only [Walk.support_nil, List.mem_singleton] at hc
    exact hbc.ne hc.symm
  · have hsub : p.toSubgraph.Adj c b :=
      prefix_adj_saturated hdegree ha hp hc hbc.ne.symm hbc.symm
    have he : c = p.penultimate := hp.eq_penultimate_of_mem_edges
      (Walk.adj_toSubgraph_iff_mem_edges.mp hsub.symm)
    exact hnb hnil he.symm

private theorem path_by_length (n : ℕ) {a b : V} (p : G.Walk a b)
    (hlen : p.length = n)
    (hdegree : ∀ z, (G.neighborSet z).ncard ≤ 2)
    (ha : (G.neighborSet a).Subsingleton) (hnb : Nonbacktracking p) :
    p.IsPath := by
  induction n using Nat.strong_induction_on generalizing a b p with
  | h n ih =>
    by_cases hnil : p.Nil
    · cases hnil
      exact Walk.IsPath.nil
    · have hpos : 0 < p.length := Walk.not_nil_iff_lt_length.mp hnil
      have hlt : p.dropLast.length < n := by
        rw [Walk.length_dropLast]
        omega
      have hnbq : Nonbacktracking p.dropLast := by
        intro i hi
        have hil : i + 2 < p.length := by rw [Walk.length_dropLast] at hi; omega
        rw [Walk.getVert_dropLast (by omega : i < p.length),
          Walk.getVert_dropLast hil]
        exact hnb i (by omega)
      have hq : p.dropLast.IsPath :=
        ih p.dropLast.length hlt p.dropLast rfl ha hnbq
      have hnblast : ¬p.dropLast.Nil → p.dropLast.penultimate ≠ b := by
        intro hqnil
        have hqpos := Walk.not_nil_iff_lt_length.mp hqnil
        rw [Walk.length_dropLast] at hqpos
        have htwo : 2 ≤ p.length := by omega
        have hne := hnb (p.length - 2) (by omega)
        have he : p.dropLast.penultimate = p.getVert (p.length - 2) := by
          change p.dropLast.getVert (p.dropLast.length - 1) = _
          rw [Walk.length_dropLast, Nat.sub_sub]
          simpa using (Walk.getVert_dropLast
            (p := p) (n := p.length - 2) (by omega))
        rw [he]
        convert hne using 1 <;> simp [show p.length - 2 + 2 = p.length by omega]
      have he := path_extend hdegree ha hq (p.adj_penultimate hnil) hnblast
      rwa [Walk.concat_dropLast] at he

/-- Starting at a leaf prevents every repetition in a degree-two graph;
only immediate backtracking, rather than simplicity, is excluded beforehand. -/
theorem nonbacktracking_leaf_isPath {a b : V} (p : G.Walk a b)
    (hdegree : ∀ z, (G.neighborSet z).ncard ≤ 2)
    (ha : (G.neighborSet a).Subsingleton) (hnb : Nonbacktracking p) :
    p.IsPath :=
  path_by_length p.length p rfl hdegree ha hnb

omit [DecidableEq V] [Finite V] in
private theorem leaf_ncard {x y : V} (h : (G.neighborSet x).Subsingleton)
    (hxy : G.Adj x y) : (G.neighborSet x).ncard = 1 := by
  apply Set.ncard_eq_one.mpr
  refine ⟨y, ?_⟩
  ext z
  exact ⟨fun hz => Set.mem_singleton_iff.mpr (h hz hxy),
    fun hz => (Set.mem_singleton_iff.mp hz) ▸ hxy⟩

/-- A nonempty actual leaf-to-leaf walk without immediate backtracking is
the complete simple path component, including its exact actual edge inventory.
Edges in other disconnected components are not included. -/
theorem nonbacktracking_leaf_full_component {a b : V} (p : G.Walk a b)
    (hdegree : ∀ z, (G.neighborSet z).ncard ≤ 2)
    (ha : (G.neighborSet a).Subsingleton)
    (hb : (G.neighborSet b).Subsingleton)
    (hnil : ¬p.Nil) (hnb : Nonbacktracking p) :
    p.IsPath ∧ a ≠ b ∧
      (G.neighborSet a).ncard = 1 ∧ (G.neighborSet b).ncard = 1 ∧
      (∀ x, x ∈ p.support ↔ G.Reachable a x) ∧
      (∀ x y, G.Adj x y ∧ G.Reachable a x ↔ s(x,y) ∈ p.edges) := by
  have hp := nonbacktracking_leaf_isPath p hdegree ha hnb
  have hsaturated : ∀ x y, x ∈ p.support → G.Adj x y → p.toSubgraph.Adj x y := by
    intro x y hx hxy
    by_cases hxb : x = b
    · subst x
      have he : y = p.penultimate := hb hxy (p.adj_penultimate hnil).symm
      rw [he]
      exact (p.toSubgraph_adj_penultimate hnil).symm
    · exact prefix_adj_saturated hdegree ha hp hx hxb hxy
  have hsupport : ∀ x, x ∈ p.support ↔ G.Reachable a x := by
    intro x
    refine ⟨fun hx => (p.takeUntil x hx).reachable, ?_⟩
    intro hx
    exact p.mem_verts_toSubgraph.mp
      (hx.mem_subgraphVerts (H := p.toSubgraph)
        (fun y hy z hyz => hsaturated y z (p.mem_verts_toSubgraph.mp hy) hyz)
        p.start_mem_verts_toSubgraph)
  refine ⟨hp, ?_, leaf_ncard ha (p.adj_snd hnil),
    leaf_ncard hb (p.adj_penultimate hnil).symm, hsupport, ?_⟩
  · intro he
    exact hnil (hp.nil_iff_eq.mpr he)
  · intro x y
    constructor
    · rintro ⟨hxy, hx⟩
      exact Walk.adj_toSubgraph_iff_mem_edges.mp
        (hsaturated x y ((hsupport x).mpr hx) hxy)
    · intro he
      have hsub := Walk.adj_toSubgraph_iff_mem_edges.mpr he
      exact ⟨hsub.adj_sub, (hsupport x).mp
        (Walk.mem_support_of_adj_toSubgraph hsub)⟩

#print axioms nonbacktracking_leaf_isPath
#print axioms nonbacktracking_leaf_full_component

end D5.S3.Combinatorics.Graph.LeafNonbacktrackingComponent
