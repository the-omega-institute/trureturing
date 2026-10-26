/- GID: D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Steiner diameter-radius inequality for finite trees by terminal-cut averaging. -/

/-
admission_basis: open-problem-resolution (#20671; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20778
escape_witness: hull_edge_iff; pointwise_bound
Direct frozen dependencies: none (Mathlib-only imports).
The five Steiner definitions and claim retain the source expressions from #20671.
All declarations concern arbitrary finite graphs, trees or terminal sets; none is
an enumeration, checker, numeric reduction or certified finite instance.
Per-declaration proof classification (same-delivery helpers inlined):
  path_le_connected: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_connected.
  subset_hull: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_connected, D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_edge_iff, D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_eq_hull, D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_lower.
  hull_le: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_connected, D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_edge_iff, D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_mono, D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_eq_hull.
  hull_connected: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_edge_iff, D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_eq_hull, D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_lower.
  steinerDist_eq_hull: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_cut, D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_lower, D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_mono.
  hull_edge_iff: proof_shape: content; escape_witness: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_edge_iff; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.cutEdges_eq_hull.
  cutEdges_eq_hull: proof_shape: content; escape_witness: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_edge_iff; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_cut.
  steinerDist_cut: proof_shape: content; escape_witness: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.hull_edge_iff; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.pointwise_bound.
  hull_mono: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.steinerDist_mono.
  steinerDist_mono: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.dist_union_le_setEcc.
  steinerDist_lower: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.conjecture_nat.
  setEcc_bdd: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.dist_le_setEcc.
  dist_le_setEcc: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.dist_union_le_setEcc.
  dist_union_le_setEcc: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.pointwise_bound.
  separates_mono: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.cutEdges_mono.
  cutEdges_mono: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.pointwise_bound.
  opposite_terminal: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.pointwise_bound.
  count_subsets_containing: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.finite_averaging.
  finite_averaging: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.pointwise_bound.
  pointwise_bound: proof_shape: content; escape_witness: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.pointwise_bound; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.conjecture_nat.
  diameter_attained: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.conjecture_nat.
  radius_attained: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.conjecture_nat.
  conjecture_nat: proof_shape: content; escape_witness: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.pointwise_bound; consumers: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.result.
  result: proof_shape: content; escape_witness: D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.pointwise_bound; consumers: none (settling result).
-/


import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Binding conventions for Q. Zhang and Y. Tian, "On the Steiner k-diameter and Steiner (k, k′)-radius of trees",
arXiv:2511.22492v1 (27 November 2025).

* Section 1: "The Steiner distance d_G(S) … is defined as the minimum size among all connected subgraphs whose vertex sets
  contain S", d_G(S) = min{|E(T)| : S ⊆ V(T)}.
* "The Steiner k-eccentricity ε_k(v; G) of a vertex v in G is defined by max{d_G(S) : v ∈ S ⊆ V(G), |S| = k} … the
  Steiner k-diameter of G is Sd_k(G) = max{ε_k(v) : v ∈ V(G)}."
* "ε_{k,k′}(S′; G) = max{d_G(S) : S′ ⊆ S ⊆ V(G), |S| = k} … The Steiner (k, k′)-radius of G is
  Sr_{k,k′}(G) = min{ε_{k,k′}(S′; G) : S′ ⊆ V(G), |S′| = k′}".
* Conjecture 5.1: "Let n, k, k′ be integers with n ≥ k ≥ 3 and k > k′ ≥ 1 and let T be a tree with order n. Then
  Sd_k(T) ≤ k/(k − k′) Sr_{k,k′}(T) − k′(k′ − 1)/(k − k′)." -/

namespace D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The Steiner distance `d_G(S)`: the minimum number of edges of a connected subgraph whose vertex set contains `S`. -/
noncomputable def steinerDist (G : SimpleGraph V) (S : Finset V) : ℕ :=
  sInf {m | ∃ H : G.Subgraph, H.Connected ∧ (S : Set V) ⊆ H.verts ∧ H.edgeSet.ncard = m}

/-- The Steiner `k`-eccentricity `ε_k(v; G) = max{d_G(S) : v ∈ S, |S| = k}`. -/
noncomputable def steinerEcc (G : SimpleGraph V) (k : ℕ) (v : V) : ℕ :=
  sSup {m | ∃ S : Finset V, v ∈ S ∧ S.card = k ∧ steinerDist G S = m}

/-- The Steiner `k`-diameter `Sd_k(G) = max{ε_k(v) : v ∈ V(G)}`. -/
noncomputable def steinerDiam (G : SimpleGraph V) (k : ℕ) : ℕ :=
  sSup {m | ∃ v : V, steinerEcc G k v = m}

/-- The Steiner `(k, k′)`-eccentricity `ε_{k,k′}(S′; G) = max{d_G(S) : S′ ⊆ S, |S| = k}`. -/
noncomputable def steinerSetEcc (G : SimpleGraph V) (k : ℕ) (S' : Finset V) : ℕ :=
  sSup {m | ∃ S : Finset V, S' ⊆ S ∧ S.card = k ∧ steinerDist G S = m}

/-- The Steiner `(k, k′)`-radius `Sr_{k,k′}(G) = min{ε_{k,k′}(S′; G) : |S′| = k′}`. -/
noncomputable def steinerRadius (G : SimpleGraph V) (k k' : ℕ) : ℕ :=
  sInf {m | ∃ S' : Finset V, S'.card = k' ∧ steinerSetEcc G k S' = m}

/-- Conjecture 5.1. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (T : SimpleGraph V) (k k' : ℕ),
    T.IsTree → k ≤ Fintype.card V → 3 ≤ k → k' < k → 1 ≤ k' →
      (steinerDiam T k : ℚ) ≤
        (k : ℚ) / ((k : ℚ) - k') * steinerRadius T k k' - (k' : ℚ) * ((k' : ℚ) - 1) / ((k : ℚ) - k')

end D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius


namespace D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V}

private noncomputable def hull (T : SimpleGraph V) (S : Finset V) : T.Subgraph :=
  sInf {H | H.Connected ∧ (S : Set V) ⊆ H.verts}

omit [Fintype V] in
private theorem path_le_connected (ht : T.IsTree) {H : T.Subgraph} (hc : H.Connected)
    {u v : V} (hu : u ∈ H.verts) (hv : v ∈ H.verts)
    {p : T.Walk u v} (hp : p.IsPath) : p.toSubgraph ≤ H := by
  obtain ⟨q, hq⟩ := (Subgraph.preconnected_iff_forall_exists_walk_subgraph H).mp
    hc.preconnected hu hv
  have eqp : q.bypass = p := (ht.existsUnique_path u v).unique q.bypass_isPath hp
  rw [← eqp]
  exact q.toSubgraph_bypass_le_toSubgraph.trans hq

omit [Fintype V] [DecidableEq V] in
private theorem subset_hull (S : Finset V) : (S : Set V) ⊆ (hull T S).verts := by
  intro v hv
  simp only [hull, Subgraph.verts_sInf, Set.mem_iInter]
  intro H hH
  exact hH.2 hv

omit [Fintype V] [DecidableEq V] in
private theorem hull_le {S : Finset V} {H : T.Subgraph} (hc : H.Connected)
    (hs : (S : Set V) ⊆ H.verts) : hull T S ≤ H := sInf_le ⟨hc,hs⟩

omit [Fintype V] in
private theorem hull_connected (ht : T.IsTree) {S : Finset V} (hs : S.Nonempty) :
    (hull T S).Connected := by
  rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
  refine ⟨?_, ?_⟩
  · obtain ⟨v,hv⟩ := hs
    exact ⟨v, subset_hull S hv⟩
  · intro u v hu hv
    obtain ⟨p,hp,_⟩ := ht.existsUnique_path u v
    refine ⟨p, le_sInf ?_⟩
    intro H hH
    have hm := hull_le hH.1 hH.2
    exact path_le_connected ht hH.1 (hm.1 hu) (hm.1 hv) hp

private theorem steinerDist_eq_hull (ht : T.IsTree) {S : Finset V} (hs : S.Nonempty) :
    steinerDist T S = (hull T S).edgeSet.ncard := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨hull T S, hull_connected ht hs, subset_hull S, rfl⟩
  · apply le_csInf
    · exact ⟨_, hull T S, hull_connected ht hs, subset_hull S, rfl⟩
    · rintro m ⟨H,hc,hS,rfl⟩
      exact Set.ncard_le_ncard (Subgraph.edgeSet_mono (hull_le hc hS))

end D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius
namespace D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V}

def Separates (T : SimpleGraph V) (S : Finset V) (e : Sym2 V) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, ¬ (T.deleteEdges {e}).Reachable a b

omit [Fintype V] in
private theorem hull_edge_iff (ht : T.IsTree) {S : Finset V} (hs : S.Nonempty)
    {e : Sym2 V} :
    e ∈ (hull T S).edgeSet ↔ Separates T S e := by
  constructor
  · intro hmem
    by_contra hn
    obtain ⟨a,ha⟩ := hs
    have hreach : ∀ b ∈ S, (T.deleteEdges {e}).Reachable a b := by
      intro b hb
      by_contra hh
      exact hn ⟨a,ha,b,hb,hh⟩
    let K := T.deleteEdges {e}
    let C := K.connectedComponentMk a
    let L : T.Subgraph := {
      verts := C.toSubgraph.verts
      Adj := C.toSubgraph.Adj
      adj_sub := fun h => (T.deleteEdges_le {e}) (C.toSubgraph.adj_sub h)
      edge_vert := C.toSubgraph.edge_vert
      symm := C.toSubgraph.symm }
    have hLc : L.Connected := ⟨C.connected_toSubgraph.coe⟩
    have hSL : (S : Set V) ⊆ L.verts := by
      intro b hb
      change K.connectedComponentMk b = K.connectedComponentMk a
      exact ConnectedComponent.sound (hreach b hb).symm
    have hEL := Subgraph.edgeSet_mono (hull_le hLc hSL) hmem
    have hEK : e ∈ K.edgeSet := C.toSubgraph.edgeSet_subset hEL
    simp [K, edgeSet_deleteEdges] at hEK
  · rintro ⟨a,ha,b,hb,hab⟩
    obtain ⟨p,hp⟩ := (Subgraph.preconnected_iff_forall_exists_walk_subgraph _).mp
      (hull_connected ht hs).preconnected (subset_hull S ha) (subset_hull S hb)
    exact Subgraph.edgeSet_mono hp (p.mem_edges_toSubgraph.mpr
      (p.mem_edges_of_not_reachable_deleteEdges hab))

noncomputable def cutEdges (T : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact T.edgeFinset.filter (Separates T S)

private theorem cutEdges_eq_hull (ht : T.IsTree) {S : Finset V} (hs : S.Nonempty) :
    (cutEdges T S : Set (Sym2 V)) = (hull T S).edgeSet := by
  classical
  ext e
  simp only [cutEdges, Finset.mem_coe, Finset.mem_filter, mem_edgeFinset]
  exact ⟨fun h => (hull_edge_iff ht hs).mpr h.2,
    fun h => ⟨(hull T S).edgeSet_subset h,
      (hull_edge_iff ht hs).mp h⟩⟩

theorem steinerDist_cut (ht : T.IsTree) {S : Finset V} (hs : S.Nonempty) :
    steinerDist T S = (cutEdges T S).card := by
  rw [steinerDist_eq_hull ht hs, ← cutEdges_eq_hull ht hs, Set.ncard_coe_finset]

end D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius


namespace D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
private theorem hull_mono {U W : Finset V} (h : U ⊆ W) : hull T U ≤ hull T W := by
  apply le_sInf
  intro H hH
  exact hull_le hH.1 (fun v hv => hH.2 (h hv))

private theorem steinerDist_mono (ht : T.IsTree) {U W : Finset V} (hu : U.Nonempty)
    (h : U ⊆ W) : steinerDist T U ≤ steinerDist T W := by
  rw [steinerDist_eq_hull ht hu, steinerDist_eq_hull ht (hu.mono h)]
  exact Set.ncard_le_ncard (Subgraph.edgeSet_mono (hull_mono h))

private theorem steinerDist_lower (ht : T.IsTree) {S : Finset V} (hs : S.Nonempty) :
    S.card - 1 ≤ steinerDist T S := by
  classical
  let H := hull T S
  have hH := (hull_connected ht hs).coe.card_vert_le_card_edgeSet_add_one
  have he : H.coe.edgeSet.ncard = H.edgeSet.ncard := by
    rw [← H.image_coe_edgeSet_coe]
    exact (Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.coe_injective)).symm
  have hv : S.card ≤ H.verts.ncard := by
    simpa using Set.ncard_le_ncard (subset_hull (T := T) S)
  rw [steinerDist_eq_hull ht hs]
  change H.verts.ncard ≤ H.coe.edgeSet.ncard + 1 at hH
  rw [he] at hH
  change S.card - 1 ≤ H.edgeSet.ncard
  omega

omit [DecidableEq V] in
private theorem setEcc_bdd (T : SimpleGraph V) (k : ℕ) (B : Finset V) :
    BddAbove {m | ∃ S : Finset V, B ⊆ S ∧ S.card = k ∧ steinerDist T S = m} := by
  apply (Set.finite_range (steinerDist T)).bddAbove.mono
  rintro m ⟨S,_,_,rfl⟩
  exact ⟨S,rfl⟩

omit [DecidableEq V] in
private theorem dist_le_setEcc {B S : Finset V} {k : ℕ} (h : B ⊆ S) (hk : S.card = k) :
    steinerDist T S ≤ steinerSetEcc T k B :=
  le_csSup (setEcc_bdd T k B) ⟨S,h,hk,rfl⟩

private theorem dist_union_le_setEcc (ht : T.IsTree) {B X : Finset V} {k r : ℕ}
    (hb : B.Nonempty) (hB : B.card = r) (hX : X.card = k-r)
    (hr : r ≤ k) (hk : k ≤ Fintype.card V) :
    steinerDist T (B ∪ X) ≤ steinerSetEcc T k B := by
  have hu : (B ∪ X).card ≤ k := by
    calc
      _ ≤ B.card + X.card := Finset.card_union_le _ _
      _ = k := by rw [hB,hX,Nat.add_sub_of_le hr]
  obtain ⟨S,hS,hSc⟩ := Finset.exists_superset_card_eq hu hk
  exact (steinerDist_mono ht (hb.mono Finset.subset_union_left) hS).trans
    (dist_le_setEcc (Finset.subset_union_left.trans hS) hSc)

end D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius


namespace D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius
open SimpleGraph
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
private theorem separates_mono {U W : Finset V} {e : Sym2 V} (h : U ⊆ W)
    (hs : Separates T U e) : Separates T W e := by
  obtain ⟨a,ha,b,hb,hab⟩ := hs
  exact ⟨a,h ha,b,h hb,hab⟩

omit [DecidableEq V] in
private theorem cutEdges_mono {U W : Finset V} (h : U ⊆ W) : cutEdges T U ⊆ cutEdges T W := by
  classical
  intro e he
  obtain ⟨het,hes⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨het,separates_mono h hes⟩

private theorem opposite_terminal {A B : Finset V} (hb : B.Nonempty) {e : Sym2 V}
    (heA : e ∈ cutEdges T A) :
    ∃ a ∈ A, ∀ X : Finset V, a ∈ X → e ∈ cutEdges T (B ∪ X) := by
  classical
  obtain ⟨b,hb⟩ := hb
  obtain ⟨het,u,hu,v,hv,huv⟩ := Finset.mem_filter.mp heA
  have hor : ¬ (T.deleteEdges {e}).Reachable b u ∨
      ¬ (T.deleteEdges {e}).Reachable b v := by
    by_contra hn
    push Not at hn
    exact huv (hn.1.symm.trans hn.2)
  rcases hor with hor | hor
  · refine ⟨u,hu,fun X hX => Finset.mem_filter.mpr ⟨het,?_⟩⟩
    exact ⟨b,Finset.mem_union_left _ hb,u,Finset.mem_union_right _ hX,hor⟩
  · refine ⟨v,hv,fun X hX => Finset.mem_filter.mpr ⟨het,?_⟩⟩
    exact ⟨b,Finset.mem_union_left _ hb,v,Finset.mem_union_right _ hX,hor⟩

end D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius
namespace D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius
open SimpleGraph
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V}

/- Count the subsets of a fixed size containing a nominated element. -/
omit [Fintype V] in
private theorem count_subsets_containing (A : Finset V) {a : V} (ha : a ∈ A)
    {s : ℕ} (hs : 1 ≤ s) :
    ((A.powersetCard s).filter (fun X => a ∈ X)).card =
      (A.card-1).choose (s-1) := by
  classical
  simpa using Finset.card_filter_powersetCard_subset {a} A s
    (Finset.singleton_subset_iff.mpr ha) (by simpa using hs)

/- Finite averaging for sets containing a deterministic part and sampled witnesses. -/
omit [Fintype V] in
private theorem finite_averaging {E : Type} [DecidableEq E] (A : Finset V) (J Q : Finset E)
    (f : E → V) (Y : Finset V → Finset E) (s R : ℕ)
    (hs : 1 ≤ s) (hdis : Disjoint J Q)
    (hf : ∀ e ∈ Q, f e ∈ A)
    (hJ : ∀ X ∈ A.powersetCard s, J ⊆ Y X)
    (hQ : ∀ X ∈ A.powersetCard s, ∀ e ∈ Q, f e ∈ X → e ∈ Y X)
    (hR : ∀ X ∈ A.powersetCard s, (Y X).card ≤ R) :
    (A.card.choose s) * J.card + (A.card-1).choose (s-1) * Q.card ≤
      (A.card.choose s) * R := by
  classical
  let F := A.powersetCard s
  have point : ∀ X ∈ F, J.card + (Q.filter (fun e => f e ∈ X)).card ≤ (Y X).card := by
    intro X hX
    have hd : Disjoint J (Q.filter (fun e => f e ∈ X)) :=
      hdis.mono_right (Finset.filter_subset _ _)
    rw [← Finset.card_union_of_disjoint hd]
    exact Finset.card_le_card (Finset.union_subset (hJ X hX)
      (fun e he => hQ X hX e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2))
  have double : (∑ X ∈ F, (Q.filter (fun e => f e ∈ X)).card) =
      (A.card-1).choose (s-1) * Q.card := by
    calc
      _ = ∑ e ∈ Q, (F.filter (fun X => f e ∈ X)).card := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        exact Finset.sum_comm
      _ = ∑ e ∈ Q, (A.card-1).choose (s-1) := by
        apply Finset.sum_congr rfl
        intro e he
        exact count_subsets_containing A (hf e he) hs
      _ = _ := by simp [Nat.mul_comm]
  calc
    _ = ∑ X ∈ F, (J.card + (Q.filter (fun e => f e ∈ X)).card) := by
      rw [Finset.sum_add_distrib, double]
      simp [F, Finset.card_powersetCard, Nat.mul_comm]
    _ ≤ ∑ X ∈ F, (Y X).card := Finset.sum_le_sum point
    _ ≤ ∑ X ∈ F, R := Finset.sum_le_sum hR
    _ = _ := by simp [F, Finset.card_powersetCard, Nat.mul_comm]

end D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius


namespace D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V}

theorem pointwise_bound (ht : T.IsTree) {A B : Finset V} {k r : ℕ}
    (hA : A.card = k) (hB : B.card = r) (hkr : r < k) (hr : 1 ≤ r)
    (hk : k ≤ Fintype.card V) :
    (k-r) * steinerDist T A + r * steinerDist T B ≤ k * steinerSetEcc T k B := by
  classical
  have hb : B.Nonempty := Finset.card_pos.mp (by omega)
  have ha : A.Nonempty := Finset.card_pos.mp (by omega)
  have hs : 1 ≤ k-r := by exact Nat.le_sub_of_add_le' hkr
  have hk1 : 1 ≤ k := by exact Nat.one_le_of_lt hkr
  let H := cutEdges T A
  let J := cutEdges T B
  let Q := H \ J
  let b : V := hb.choose
  have pick : ∀ e : Sym2 V, ∃ a : V, e ∈ Q →
      a ∈ A ∧ ∀ X : Finset V, a ∈ X → e ∈ cutEdges T (B ∪ X) := by
    intro e
    by_cases he : e ∈ Q
    · obtain ⟨a,ha,hf⟩ := opposite_terminal hb (Finset.mem_sdiff.mp he).1

      exact ⟨a,fun _ => ⟨ha,hf⟩⟩
    · exact ⟨b,fun h => (he h).elim⟩
  choose f hf using pick
  have hav := finite_averaging A J Q f (fun X => cutEdges T (B ∪ X)) (k-r)
    (steinerSetEcc T k B) hs Finset.disjoint_sdiff
    (fun e he => (hf e he).1)
    (fun X _ => cutEdges_mono Finset.subset_union_left)
    (fun X _ e he hX => (hf e he).2 X hX)
    (fun X hX => by
      rw [← steinerDist_cut ht (hb.mono Finset.subset_union_left)]
      exact dist_union_le_setEcc ht hb hB (Finset.mem_powersetCard.mp hX).2 hkr.le hk)
  rw [hA] at hav
  have hid : k * (k-1).choose (k-r-1) = (k.choose (k-r)) * (k-r) := by
    have h := Nat.add_one_mul_choose_eq (k-1) (k-r-1)
    simpa only [Nat.sub_add_cancel hk1, Nat.sub_add_cancel hs] using h
  have hn : 0 < k.choose (k-r) := Nat.choose_pos (Nat.sub_le _ _)
  have hm : (k.choose (k-r)) * (k*J.card + (k-r)*Q.card) ≤
      (k.choose (k-r)) * (k*steinerSetEcc T k B) := by
    calc
      _ = k * ((k.choose (k-r))*J.card + (k-1).choose (k-r-1)*Q.card) := by
        calc
          _ = (k.choose (k-r))*k*J.card + ((k.choose (k-r))*(k-r))*Q.card := by ring
          _ = (k.choose (k-r))*k*J.card + (k*(k-1).choose (k-r-1))*Q.card := by rw [hid]
          _ = _ := by ring
      _ ≤ k * ((k.choose (k-r))*steinerSetEcc T k B) := Nat.mul_le_mul_left k hav
      _ = _ := by ring
  have havg : k*J.card + (k-r)*Q.card ≤ k*steinerSetEcc T k B :=
    Nat.le_of_mul_le_mul_left hm hn
  have hcard : H.card ≤ Q.card+J.card := Finset.card_le_card_sdiff_add_card
  rw [steinerDist_cut ht ha,steinerDist_cut ht hb]
  change (k-r)*H.card+r*J.card ≤ k*steinerSetEcc T k B
  calc
    _ ≤ (k-r)*(Q.card+J.card)+r*J.card :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ hcard) _
    _ = ((k-r)+r)*J.card+(k-r)*Q.card := by ring
    _ = k*J.card+(k-r)*Q.card := by rw [Nat.sub_add_cancel hkr.le]
    _ ≤ _ := havg

end D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius


namespace D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V}

omit [DecidableEq V] in
private theorem diameter_attained (ht : T.IsTree) {k : ℕ}
    (hk : k ≤ Fintype.card V) (hk1 : 1 ≤ k) :
    ∃ A : Finset V, A.card = k ∧ steinerDist T A = steinerDiam T k := by
  have hv : Nonempty V := ht.connected.nonempty
  have hdne : {m | ∃ v : V, steinerEcc T k v = m}.Nonempty := by
    obtain ⟨v⟩ := hv
    exact ⟨_,v,rfl⟩
  have hdb : BddAbove {m | ∃ v : V, steinerEcc T k v = m} := by
    exact (Set.finite_range (steinerEcc T k)).bddAbove
  obtain ⟨v,hv⟩ := Nat.sSup_mem hdne hdb
  have hkn : {m | ∃ S : Finset V, v ∈ S ∧ S.card = k ∧ steinerDist T S = m}.Nonempty := by
    obtain ⟨S,hS,hSc⟩ := Finset.exists_superset_card_eq
      (s := {v}) (by simpa using hk1) hk
    exact ⟨_,S,hS (Finset.mem_singleton_self v),hSc,rfl⟩
  have hkb : BddAbove {m | ∃ S : Finset V, v ∈ S ∧ S.card = k ∧ steinerDist T S = m} := by
    apply (Set.finite_range (steinerDist T)).bddAbove.mono
    rintro m ⟨S,_,_,rfl⟩
    exact ⟨S,rfl⟩
  obtain ⟨A,_,hAc,hAd⟩ := Nat.sSup_mem hkn hkb
  exact ⟨A,hAc,hAd.trans hv⟩

omit [DecidableEq V] in
private theorem radius_attained (T : SimpleGraph V) {k r : ℕ} (hr : r ≤ Fintype.card V) :
    ∃ B : Finset V, B.card = r ∧ steinerSetEcc T k B = steinerRadius T k r := by
  have hn : {m | ∃ B : Finset V, B.card = r ∧ steinerSetEcc T k B = m}.Nonempty := by
    obtain ⟨B,_,hB⟩ := Finset.exists_superset_card_eq (s := ∅) (by simp) hr
    exact ⟨_,B,hB,rfl⟩
  exact Nat.sInf_mem hn

private theorem conjecture_nat (ht : T.IsTree) {k r : ℕ} (hk : k ≤ Fintype.card V)
    (hkr : r < k) (hr : 1 ≤ r) :
    (k-r)*steinerDiam T k+r*(r-1) ≤ k*steinerRadius T k r := by
  obtain ⟨A,hA,hD⟩ := diameter_attained ht hk (Nat.one_le_of_lt hkr)
  obtain ⟨B,hB,hR⟩ := radius_attained T (hkr.le.trans hk)
  have havg := pointwise_bound ht hA hB hkr hr hk
  have hb : B.Nonempty := Finset.card_pos.mp (by omega)
  have hlo := steinerDist_lower ht hb
  rw [hB] at hlo
  have hmul := Nat.mul_le_mul_left r hlo
  rw [hD,hR] at havg
  exact (Nat.add_le_add_left hmul _).trans havg

theorem result : claim := by
  intro V _ _ T k r ht hk hk3 hkr hr
  have h := conjecture_nat ht hk hkr hr
  have hq : (((k-r)*steinerDiam T k+r*(r-1) : ℕ) : ℚ) ≤
      ((k*steinerRadius T k r : ℕ) : ℚ) := by exact Rat.natCast_le_natCast.mpr h
  rw [Nat.cast_add,Nat.cast_mul,Nat.cast_mul,Nat.cast_mul,
    Nat.cast_sub hkr.le,Nat.cast_sub hr] at hq
  have hpos : (0 : ℚ) < (k : ℚ)-(r : ℚ) := sub_pos.mpr (by exact_mod_cast hkr)
  apply (le_sub_iff_add_le).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpos).mpr
  rw [add_mul, div_mul_cancel₀ _ hpos.ne']
  norm_num only [Nat.cast_one] at hq
  nlinarith

end D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius
