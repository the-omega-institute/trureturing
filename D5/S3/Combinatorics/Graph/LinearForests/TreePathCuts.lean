/- GID: D5/S3/Combinatorics/Graph/LinearForests/TreePathCuts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/TreePathCuts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: A spine cut in a tree leaves a path of residual components. -/

/-
admission_basis: escape-witness
proof_shape: content (componentGraph_path)
escape_witness: projecting a simple walk to exactly the retained cut edges gives
a spanning trail in the acyclic residual component graph.
Direct frozen dependencies: none. The graph and walk imports are pinned Mathlib.
Escape audit issue: https://github.com/the-omega-institute/trureturing/issues/34504
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import OmegaBuild.Commands

/-!
# Cuts carried by one path in a tree

An edge of a forest separates its endpoints when deleted. Contracting
the components left by a cut on a simple path yields a path of components.
The original cut edges give its adjacency.
The degree lemmas are used to identify the individual components as paths.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OneJoinedPathTrees

noncomputable section

open SimpleGraph
open scoped Sym2

universe u
variable {V : Type u} {G : SimpleGraph V}


/-- Cardinal degree, expressed without choosing a decidable adjacency relation. -/
def degree (G : SimpleGraph V) (x : V) : ℕ := (G.neighborSet x).ncard

/-- The number of edges of the cut incident to a vertex. -/
def cutIncidence (G : SimpleGraph V) (C : Set (Sym2 V)) (x : V) : ℕ :=
  (C ∩ G.incidenceSet x).ncard

theorem degree_eq_residual_add_incidence [Finite V] (C : Set (Sym2 V)) (x : V) :
    degree G x = degree (G.deleteEdges C) x + cutIncidence G C x := by
  classical
  let := Fintype.ofFinite V
  have h : (G.deleteEdges C).incidenceSet x = G.incidenceSet x \ (C ∩ G.incidenceSet x) := by
    ext e
    induction e using Sym2.inductionOn with
    | hf y z =>
      simp only [mk'_mem_incidenceSet_iff, deleteEdges_adj, Set.mem_sdiff, Set.mem_inter_iff]
      tauto
  unfold degree cutIncidence
  rw [ncard_neighborSet, ncard_neighborSet, ← ncard_incidenceSet, ← ncard_incidenceSet, h]
  exact (Set.ncard_sdiff_add_ncard_of_subset Set.inter_subset_right).symm

theorem residual_eq_degree_sub_incidence [Finite V] (C : Set (Sym2 V)) (x : V) :
    degree (G.deleteEdges C) x = degree G x - cutIncidence G C x := by
  have := degree_eq_residual_add_incidence (G := G) C x
  omega

/-- The cut is carried by the edge list of an actual simple walk in the input graph. -/
def OnSpine (G : SimpleGraph V) (C : Set (Sym2 V)) : Prop :=
  ∃ a b, ∃ p : G.Walk a b, p.IsPath ∧ ∀ e ∈ C, e ∈ p.edges

theorem OnSpine.subset_edgeSet {C : Set (Sym2 V)} (h : OnSpine G C) :
    C ⊆ G.edgeSet := by
  obtain ⟨a, b, p, _, hp⟩ := h
  exact fun e he => p.edges_subset_edgeSet (hp e he)

/-- A spanning simple walk gives the standard path graph in an acyclic graph. -/
private theorem path_iso_of_support {a b : V} (hG : G.IsAcyclic)
    (p : G.Walk a b) (hp : p.IsPath) (hs : ∀ v, v ∈ p.support) :
    Nonempty (pathGraph (p.length + 1) ≃g G) := by
  classical
  let F : SimpleGraph V := p.toSubgraph.spanningCoe
  have hle : F ≤ G := fun _ _ h => h.adj_sub
  let f : p.toSubgraph.coe ≃g F :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, p.mem_verts_toSubgraph.mpr (hs x)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  have hc : F.Connected :=
    f.connected_iff.mp (hp.pathGraphIsoToSubgraph.connected_iff.mp (connected_pathGraph_add_one _))
  have ht : G.IsTree := ⟨hc.mono hle, hG⟩
  have he : F = G := le_antisymm hle ((isTree_iff_minimal_connected.mp ht).2 hc hle)
  have iso := hp.pathGraphIsoToSubgraph.trans f
  rw [he] at iso
  exact ⟨iso⟩

private theorem support_of_closed {a b : V} (hG : G.Connected) (p : G.Walk a b)
    (hcl : ∀ x ∈ p.support, ∀ y, G.Adj x y → y ∈ p.support) :
    ∀ v, v ∈ p.support := by
  have propagate : ∀ {x y} (r : G.Walk x y), x ∈ p.support → y ∈ p.support := by
    intro x y r
    induction r with
    | nil => exact id
    | @cons x z y h r ih => exact fun hx => ih (hcl x hx z h)
  intro v
  obtain ⟨q⟩ := hG a v
  exact propagate q p.start_mem_support

theorem pathGraph_degree_le_two {n : ℕ} (x : Fin n) :
    degree (pathGraph n) x ≤ 2 := by
  let S : Set ℕ := {x.val - 1, x.val + 1}
  have hb : S.ncard = 2 := Set.ncard_pair (by omega)
  rw [← hb]
  apply Set.ncard_le_ncard_of_injOn Fin.val
  · intro y hy
    change (pathGraph n).Adj x y at hy
    change y.val = x.val - 1 ∨ y.val = x.val + 1
    rcases pathGraph_adj.mp hy with hy | hy
    · exact Or.inr hy.symm
    · exact Or.inl (by omega)
  · exact Fin.val_injective.injOn

theorem degree_iso {W : Type*} (H : SimpleGraph W) (e : G ≃g H) (x : V) :
    degree H (e x) = degree G x := by
  symm
  apply Set.ncard_congr (fun y _ => e y)
  · intro y hy
    exact e.map_rel_iff.mpr hy
  · exact fun _ _ _ _ h => e.injective h
  · intro y hy
    exact ⟨e.symm y, e.map_rel_iff.mp (by simpa using hy), e.apply_symm_apply y⟩

theorem path_of_degree_le_two [Finite V] (hG : G.IsTree)
    (hd : ∀ x, degree G x ≤ 2) : ∃ n, Nonempty (pathGraph (n + 1) ≃g G) := by
  classical
  let := Fintype.ofFinite V
  let S := (Finset.range (Fintype.card V)).filter
    (fun k => ∃ x y, ∃ p : G.Walk x y, p.IsPath ∧ p.length = k)
  obtain ⟨a⟩ := hG.connected.nonempty
  have h0 : 0 ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Fintype.card_pos_iff.mpr ⟨a⟩),
      a, a, Walk.nil, Walk.IsPath.nil, rfl⟩
  obtain ⟨k, hk, hmax⟩ := S.exists_max_image id ⟨0, h0⟩
  obtain ⟨x, y, p, hp, rfl⟩ := (Finset.mem_filter.mp hk).2
  have maximal {v w : V} (q : G.Walk v w) (hq : q.IsPath) : q.length ≤ p.length :=
    hmax _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hq.length_lt, v, w, q, hq, rfl⟩)
  refine ⟨p.length, path_iso_of_support hG.isAcyclic p hp (support_of_closed hG.connected p ?_)⟩
  intro v hv w h
  by_contra hn
  obtain ⟨j, rfl, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  by_cases hfirst : j = 0
  · subst j
    rw [Walk.getVert_zero] at h
    have hm := maximal (.cons h.symm p) (hp.cons hn)
    simp at hm
  by_cases hlast : j = p.length
  · subst j
    rw [Walk.getVert_length] at h
    have hm := maximal (p.concat h) (hp.concat hn h)
    simp at hm
  have hprev : G.Adj (p.getVert j) (p.getVert (j - 1)) := by
    have hadj := p.adj_getVert_succ (i := j - 1) (by omega)
    rwa [show j - 1 + 1 = j by omega, adj_comm] at hadj
  have hnext := p.adj_getVert_succ (i := j) (by omega)
  have hpn : p.getVert (j - 1) ≠ p.getVert (j + 1) := by
    intro he
    have := hp.getVert_injOn (by change j - 1 ≤ p.length; omega)
      (by change j + 1 ≤ p.length; omega) he
    omega
  have hpw : p.getVert (j - 1) ≠ w := fun he => hn (he ▸ p.getVert_mem_support _)
  have hnw : p.getVert (j + 1) ≠ w := fun he => hn (he ▸ p.getVert_mem_support _)
  let N : Set V := {p.getVert (j - 1), p.getVert (j + 1)}
  have hcard : (insert w N).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair hpn]
    simp [N, Ne.symm hpw, Ne.symm hnw]
  have hle : (insert w N).ncard ≤ degree G (p.getVert j) := by
    apply Set.ncard_le_ncard
    · simp only [N, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨h, hprev, hnext⟩
    · exact Set.toFinite _
  have := hd (p.getVert j)
  omega

abbrev Components (G : SimpleGraph V) (C : Set (Sym2 V)) :=
  (G.deleteEdges C).ConnectedComponent

abbrev component (G : SimpleGraph V) (C : Set (Sym2 V)) : V → Components G C :=
  (G.deleteEdges C).connectedComponentMk

theorem cut_separates (hG : G.IsAcyclic) {C : Set (Sym2 V)} {x y : V}
    (hxy : G.Adj x y) (hc : s(x, y) ∈ C) :
    component G C x ≠ component G C y := by
  intro he
  have bridge := isAcyclic_iff_forall_adj_isBridge.mp hG hxy
  apply isBridge_iff.mp bridge
  apply Reachable.mono _ (ConnectedComponent.exact he)
  intro a b hab
  obtain ⟨hab, hn⟩ := deleteEdges_adj.mp hab
  refine deleteEdges_adj.mpr ⟨hab, ?_⟩
  exact fun h => hn (Set.mem_singleton_iff.mp h ▸ hc)

theorem same_component_of_uncut {C : Set (Sym2 V)} {x y : V}
    (hxy : G.Adj x y) (hc : s(x, y) ∉ C) :
    component G C x = component G C y :=
  ConnectedComponent.connectedComponentMk_eq_of_adj (deleteEdges_adj.mpr ⟨hxy, hc⟩)

def componentGraph (G : SimpleGraph V) (C : Set (Sym2 V)) :
    SimpleGraph (Components G C) where
  Adj A B := A ≠ B ∧ ∃ x y, G.Adj x y ∧ s(x, y) ∈ C ∧
    component G C x = A ∧ component G C y = B
  symm := ⟨by
    rintro A B ⟨hne, x, y, hxy, hc, hx, hy⟩
    exact ⟨hne.symm, y, x, hxy.symm, by rwa [Sym2.eq_swap], hy, hx⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem componentGraph_adj (hG : G.IsAcyclic) {C : Set (Sym2 V)} {x y : V}
    (hxy : G.Adj x y) (hc : s(x, y) ∈ C) :
    (componentGraph G C).Adj (component G C x) (component G C y) :=
  ⟨cut_separates hG hxy hc, x, y, hxy, hc, rfl, rfl⟩

/-- The residual components refine the components after deleting any single cut edge. -/
private theorem singleDeletion_le {C : Set (Sym2 V)} {e : Sym2 V} (he : e ∈ C) :
    G.deleteEdges C ≤ G.deleteEdges {e} := by
  intro x y h
  obtain ⟨hxy, hn⟩ := deleteEdges_adj.mp h
  exact deleteEdges_adj.mpr ⟨hxy, fun h => hn (Set.mem_singleton_iff.mp h ▸ he)⟩

theorem cutEndpoints_unique (hG : G.IsAcyclic) {C : Set (Sym2 V)} {x y x' y' : V}
    (hxy : G.Adj x y) (hc : s(x, y) ∈ C) (hxy' : G.Adj x' y')
    (hx : component G C x = component G C x')
    (hy : component G C y = component G C y') :
    x = x' ∧ y = y' := by
  have he : s(x', y') = s(x, y) := by
    by_contra hn
    have hr : (G.deleteEdges {s(x, y)}).Adj x' y' := deleteEdges_adj.mpr ⟨hxy', hn⟩
    have hr₁ := Reachable.mono (singleDeletion_le (G := G) hc) (ConnectedComponent.exact hx)
    have hr₂ := Reachable.mono (singleDeletion_le (G := G) hc) (ConnectedComponent.exact hy.symm)
    exact isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hG hxy)
      (hr₁.trans (hr.reachable.trans hr₂))
  rcases Sym2.eq_iff.mp he with h | h
  · exact ⟨h.1.symm, h.2.symm⟩
  · exact (cut_separates hG hxy hc (hx.trans (congrArg (component G C) h.1))).elim

private theorem componentGraph_isAcyclic (hG : G.IsAcyclic) (C : Set (Sym2 V)) :
    (componentGraph G C).IsAcyclic := by
  apply isAcyclic_iff_forall_adj_isBridge.mpr
  rintro A B ⟨hne, x, y, hxy, hc, rfl, rfl⟩
  rw [isBridge_iff]
  let D := G.deleteEdges {s(x, y)}
  let f : Components G C → D.ConnectedComponent :=
    ConnectedComponent.lift D.connectedComponentMk
      (fun _ _ p _ => ConnectedComponent.sound (Reachable.mono (singleDeletion_le hc) ⟨p⟩))
  have hstep {A B : Components G C}
      (h : ((componentGraph G C).deleteEdges {s(component G C x, component G C y)}).Adj A B) :
      f A = f B := by
    obtain ⟨⟨_, a, b, hab, _, rfl, rfl⟩, hd⟩ := deleteEdges_adj.mp h
    have hn : s(a, b) ≠ s(x, y) := by
      intro he
      apply hd
      simp only [Set.mem_singleton_iff]
      exact congrArg (Sym2.map (component G C)) he
    exact ConnectedComponent.connectedComponentMk_eq_of_adj (deleteEdges_adj.mpr ⟨hab, hn⟩)
  have hw {A B : Components G C}
      (q : ((componentGraph G C).deleteEdges {s(component G C x, component G C y)}).Walk A B) :
      f A = f B := by
    induction q with
    | nil => rfl
    | cons h _ ih => exact (hstep h).trans ih
  rintro ⟨q⟩
  have he : D.connectedComponentMk x = D.connectedComponentMk y := hw q
  exact isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hG hxy) (ConnectedComponent.exact he)

private def projectWalk (hG : G.IsAcyclic) (C : Set (Sym2 V)) : {a b : V} →
    G.Walk a b → (componentGraph G C).Walk (component G C a) (component G C b)
  | _, _, .nil => .nil
  | _, _, @Walk.cons _ _ x y _ h p => by
    classical
    exact if hc : s(x, y) ∈ C then .cons (componentGraph_adj hG h hc) (projectWalk hG C p)
      else (projectWalk hG C p).copy (same_component_of_uncut h hc).symm rfl

private theorem projectWalk_edges (hG : G.IsAcyclic) (C : Set (Sym2 V)) {a b : V}
    (p : G.Walk a b) :
    letI : DecidablePred (· ∈ C) := Classical.decPred _
    (projectWalk hG C p).edges = p.edges.filterMap
      (fun e => if e ∈ C then some (e.map (component G C)) else none) := by
  classical
  induction p with
  | nil => rfl
  | @cons x y z h p ih =>
    by_cases hc : s(x, y) ∈ C
    · simp [projectWalk, hc, ih]
    · simp [projectWalk, hc, ih]

private theorem cut_map_injOn (hG : G.IsAcyclic) {C : Set (Sym2 V)} (hC : C ⊆ G.edgeSet) :
    Set.InjOn (Sym2.map (component G C)) C := by
  intro e he e' he'
  induction e using Sym2.inductionOn with
  | hf x y =>
    induction e' using Sym2.inductionOn with
    | hf x' y' =>
      intro hm
      change s(component G C x, component G C y) =
        s(component G C x', component G C y') at hm
      rcases Sym2.eq_iff.mp hm with h | h
      · obtain ⟨rfl, rfl⟩ := cutEndpoints_unique hG (hC he) he (hC he') h.1 h.2
        rfl
      · have hadj : G.Adj y' x' := (show G.Adj x' y' from hC he').symm
        obtain ⟨rfl, rfl⟩ := cutEndpoints_unique hG (hC he) he hadj h.1 h.2
        exact Sym2.eq_swap

private theorem componentGraph_connected (hG : G.IsTree) (C : Set (Sym2 V)) :
    (componentGraph G C).Connected := by
  have := hG.connected.nonempty
  apply Connected.mk
  intro A B
  obtain ⟨x, rfl⟩ := Quot.exists_rep A
  obtain ⟨y, rfl⟩ := Quot.exists_rep B
  obtain ⟨p⟩ := hG.connected x y
  exact ⟨projectWalk hG.isAcyclic C p⟩

theorem componentGraph_path (hG : G.IsTree) {C : Set (Sym2 V)} (hS : OnSpine G C) :
    ∃ k, Nonempty (pathGraph (k + 1) ≃g componentGraph G C) := by
  classical
  have hC := hS.subset_edgeSet
  obtain ⟨a, b, p, hp, hs⟩ := hS
  let q := projectWalk hG.isAcyclic C p
  have hE := projectWalk_edges hG.isAcyclic C p
  have hac := componentGraph_isAcyclic hG.isAcyclic C
  have hq : q.IsPath := by
    apply (hac.isPath_iff_isTrail q).mpr
    rw [Walk.isTrail_def]
    change (projectWalk hG.isAcyclic C p).edges.Nodup
    rw [hE]
    apply hp.isTrail.edges_nodup.filterMap
    intro e e' d he he'
    by_cases h₁ : e ∈ C <;> by_cases h₂ : e' ∈ C
    · simp [h₁, h₂] at he he'
      exact cut_map_injOn hG.isAcyclic hC h₁ h₂ (he.trans he'.symm)
    all_goals simp_all
  refine ⟨q.length, path_iso_of_support hac q hq
    (support_of_closed (componentGraph_connected hG C) q ?_)⟩
  rintro A _ B ⟨_, x, y, _, hc, rfl, rfl⟩
  have hm : s(component G C x, component G C y) ∈ q.edges := by
    change _ ∈ (projectWalk hG.isAcyclic C p).edges
    rw [hE]
    exact List.mem_filterMap.mpr ⟨s(x, y), hs _ hc, by simp [hc]⟩
  exact q.snd_mem_support_of_mem_edges hm


theorem pathGraph_degree_pos {n : ℕ} (hn : 0 < n) (x : Fin (n + 1)) :
    0 < degree (pathGraph (n + 1)) x := by
  apply (Set.ncard_pos (Set.toFinite _)).mpr
  by_cases h0 : x.val = 0
  · have h1 : 1 < n + 1 := by omega
    exact ⟨⟨1, h1⟩, pathGraph_adj.mpr (Or.inl (by simp [h0]))⟩
  · exact ⟨⟨x.val - 1, by have := x.isLt; omega⟩,
      pathGraph_adj.mpr (Or.inr (by change x.val - 1 + 1 = x.val; omega))⟩

theorem pathGraph_one_degree_zero {n : ℕ} (hn : n = 0) (x : Fin (n + 1)) :
    degree (pathGraph (n + 1)) x = 0 := by
  subst n
  have h : (pathGraph 1).neighborSet x = ∅ := by
    ext y
    simp [Subsingleton.elim y x]
  change ((pathGraph 1).neighborSet x).ncard = 0
  rw [h, Set.ncard_empty]

end

end OneJoinedPathTrees
