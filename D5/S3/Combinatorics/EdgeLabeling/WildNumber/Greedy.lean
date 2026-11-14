/- GID: D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy
   generality: G
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite edge-colored graphs and termination of the greedy wild-set algorithm. -/

/-
admission_basis: escape-witness (exists_greedy_output)
escape_witness: exists_greedy_output
Direct frozen dependencies: none.
wildColor_mono: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: dip_zero_of_connected, dip_pos_of_crossing.
kappa_connected: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
dip_zero_of_connected: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
step_positive: proof_shape: content; escape_witness: none; Direct frozen dependencies: none.
exists_greedy_output: proof_shape: content; escape_witness: exists_greedy_output; Direct frozen dependencies: none.
The potential and greedy-step formulas inline the source finite edge set; the
amplification proofs use SimpleGraph.edgeFinset via a compiled correspondence.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21209
-/

import Mathlib.Data.Multiset.Sort
import Mathlib.Order.Lattice.Nat
import D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamGraph
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Binding conventions for K. Anders, B. Foster-Greenwood, R. Garcia and N. Krawzik, "The wild number of an
edge-colored graph", arXiv:2508.06711v1 (8 August 2025).

* §1: an edge-colored graph is a finite simple graph `G` with a surjective edge coloring `γ : E(G) → C`; `Gᵢ` has edge
  set `Eᵢ(G)`; "For any color cᵢ, define the graph Gᵢᵂ to be the subgraph of G with vertex set V(G) and edge set
  W ∪ Eᵢ(G). If the set of edges W is such that for every cᵢ ∈ C, the subgraph Gᵢᵂ is connected, then W is a
  color-connecting set. … The wild number of G, denoted wld(G), is the size of an ideal wild set of G."
* §1: the dip number of an edge, `δ(e) = Σᵢ (κ(Gᵢ) − κ(Gᵢᵉ))`, with `κ` the number of components.
* §5.2: "The potential of an edge e in an edge-colored graph G is the nonincreasing dip sequence of the graph G/e."
  Example 5.9 lists every edge of `G/e`, the contracted one with dip number 0.
* Algorithm 5.10 (Greedy): "Initialize by letting W = ∅. While the graph G/W is not color-connected, do the following
  two steps: (1) Order the edges in G/W with the highest dip number lexicographically by potential in G/W (i.e.,
  compare first terms of potential, highest wins; if tie, compare next term; etc.). (2) Select an edge [u][v] ∈ E(G/W)
  with greatest potential, and add the edge uv ∈ E(G) to the wild set W. When G/W is color-connected, return the set W."
  The components of the colour-`c` graph of `G/W` are those of `Gᵂ_c`, so the dip number and the potential in `G/W`
  are computed on `Gᵂ_c`; an edge of `W` has dip number 0.
* Question 7.5: "How far off can Algorithm 5.10 be from the actual wild number? Is it ever off by more than one? or
  two?" -/
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [Fintype C]
/-- `Eᵢ(G)`: the edges of colour `c`. -/
def colorEdges (G : SimpleGraph V) (γ : G.edgeSet → C) (c : C) : Set (Sym2 V) :=
  {e | ∃ h : e ∈ G.edgeSet, γ ⟨e, h⟩ = c}
/-- `Gᵢᵂ`: vertex set `V(G)`, edge set `W ∪ Eᵢ(G)`. -/
def wildColorGraph (G : SimpleGraph V) (γ : G.edgeSet → C) (W : Finset (Sym2 V)) (c : C) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet ((W : Set (Sym2 V)) ∪ colorEdges G γ c)
/-- `W ⊆ E(G)` is color-connecting when every `Gᵢᵂ` is connected. -/
def IsColorConnecting (G : SimpleGraph V) (γ : G.edgeSet → C) (W : Finset (Sym2 V)) : Prop :=
  (W : Set (Sym2 V)) ⊆ G.edgeSet ∧ ∀ c, (wildColorGraph G γ W c).Connected
/-- `wld(G)`: the least size of a color-connecting set. -/
noncomputable def wildNumber (G : SimpleGraph V) (γ : G.edgeSet → C) : ℕ :=
  sInf {k | ∃ W : Finset (Sym2 V), IsColorConnecting G γ W ∧ W.card = k}
/-- The dip number of the edge `e` of `G/W`: `Σᵢ (κ(Gᵢᵂ) − κ(Gᵢ^{W ∪ {e}}))`. -/
noncomputable def dip (G : SimpleGraph V) (γ : G.edgeSet → C) (W : Finset (Sym2 V)) (e : Sym2 V) : ℕ :=
  ∑ c : C, (Nat.card (wildColorGraph G γ W c).ConnectedComponent - Nat.card (wildColorGraph G γ (insert e W) c).ConnectedComponent)
/-- The potential of `e` in `G/W`: the nonincreasing dip sequence of `(G/W)/e`, over every edge of `G`. -/
noncomputable def potential (G : SimpleGraph V) (γ : G.edgeSet → C) (W : Finset (Sym2 V)) (e : Sym2 V) : List ℕ :=
  (((Set.toFinite G.edgeSet).toFinset).val.map (dip G γ (insert e W))).sort (· ≥ ·)
/-- One step of Algorithm 5.10 from the wild set `W`: `G/W` is not color-connected, `e` is an edge of `G/W` of highest
dip number, and no edge of that dip number has a lexicographically greater potential. -/
def IsGreedyStep (G : SimpleGraph V) (γ : G.edgeSet → C) (W : Finset (Sym2 V)) (e : Sym2 V) : Prop :=
  ¬ IsColorConnecting G γ W ∧ e ∈ (Set.toFinite G.edgeSet).toFinset \ W ∧
    (∀ f ∈ (Set.toFinite G.edgeSet).toFinset \ W, dip G γ W f ≤ dip G γ W e) ∧
    ∀ f ∈ (Set.toFinite G.edgeSet).toFinset \ W, dip G γ W f = dip G γ W e →
      ¬ List.Lex (· < ·) (potential G γ W e) (potential G γ W f)
/-- The wild sets reachable from `∅` by steps of Algorithm 5.10. -/
inductive IsGreedyRun (G : SimpleGraph V) (γ : G.edgeSet → C) : Finset (Sym2 V) → Prop
  | empty : IsGreedyRun G γ ∅
  | step {W : Finset (Sym2 V)} {e : Sym2 V} : IsGreedyRun G γ W → IsGreedyStep G γ W e →
      IsGreedyRun G γ (insert e W)
/-- A set returned by Algorithm 5.10. -/
def IsGreedyOutput (G : SimpleGraph V) (γ : G.edgeSet → C) (W : Finset (Sym2 V)) : Prop :=
  IsGreedyRun G γ W ∧ IsColorConnecting G γ W
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
open SimpleGraph
open D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]
private theorem wildColor_mono (G : SimpleGraph V) (γ : G.edgeSet → C)
    {W W' : Finset (Sym2 V)} (h : W ⊆ W') (c : C) :
    wildColorGraph G γ W c ≤ wildColorGraph G γ W' c := by
  exact SimpleGraph.fromEdgeSet_mono (Set.union_subset_union_left _ h)
theorem kappa_connected {G : SimpleGraph V} (h : G.Connected) : Nat.card G.ConnectedComponent = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  exact ⟨h.preconnected.subsingleton_connectedComponent,
    Nonempty.map G.connectedComponentMk h.nonempty⟩
theorem dip_zero_of_connected (G : SimpleGraph V) (γ : G.edgeSet → C)
    (W : Finset (Sym2 V)) (h : IsColorConnecting G γ W) (e : Sym2 V) : dip G γ W e = 0 := by
  unfold dip
  apply Finset.sum_eq_zero
  intro c hc
  rw [kappa_connected (h.2 c),kappa_connected (SimpleGraph.Connected.mono
    (wildColor_mono G γ (Finset.subset_insert e W) c) (h.2 c))]
  rfl
private theorem kappa_lt_of_crossing {G H : SimpleGraph V} (hle : G ≤ H) {u v : V}
    (hn : ¬G.Reachable u v) (hy : H.Reachable u v) : Nat.card H.ConnectedComponent < Nat.card G.ConnectedComponent := by
  classical
  let f := ConnectedComponent.map (Hom.ofLE hle)
  have hf : Function.Surjective f := ConnectedComponent.surjective_map_ofLE hle
  have hleCard := Nat.card_le_card_of_surjective f hf
  have hne : Nat.card H.ConnectedComponent ≠ Nat.card G.ConnectedComponent := by
    intro hc
    have hinj : Function.Injective f :=
      ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hf,hc.symm⟩).1
    apply hn
    apply ConnectedComponent.exact
    apply hinj
    exact ConnectedComponent.sound hy
  omega
private theorem dip_pos_of_crossing (G : SimpleGraph V) (γ : G.edgeSet → C)
    (W : Finset (Sym2 V)) (c : C) {u v : V}
    (hn : ¬(wildColorGraph G γ W c).Reachable u v) : 0 < dip G γ W s(u,v) := by
  have huv : u ≠ v := by intro h; subst v; exact hn .rfl
  have hy : (wildColorGraph G γ (insert s(u,v) W) c).Reachable u v := by
    apply Adj.reachable
    rw [wildColorGraph,SimpleGraph.fromEdgeSet_adj]
    exact ⟨Or.inl (Finset.mem_insert_self _ _),huv⟩
  have hlt := kappa_lt_of_crossing (wildColor_mono G γ (Finset.subset_insert s(u,v) W) c) hn hy
  have hterm := Nat.sub_pos_of_lt hlt
  apply lt_of_lt_of_le hterm
  unfold dip
  exact Finset.single_le_sum
    (f := fun d : C => Nat.card (wildColorGraph G γ W d).ConnectedComponent -
      Nat.card (wildColorGraph G γ (insert s(u,v) W) d).ConnectedComponent)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
private theorem exists_positive_dip (G : SimpleGraph V) (γ : G.edgeSet → C) (hg : G.Connected)
    (W : Finset (Sym2 V)) (hw : (W : Set _) ⊆ G.edgeSet) (hn : ¬IsColorConnecting G γ W) :
    ∃ e ∈ (Set.toFinite G.edgeSet).toFinset \ W, 0 < dip G γ W e := by
  classical
  obtain ⟨c,hc⟩ : ∃ c, ¬(wildColorGraph G γ W c).Connected :=
    not_forall.mp (fun hh => hn ⟨hw,hh⟩)
  have hcross : ∃ u v, G.Adj u v ∧ ¬(wildColorGraph G γ W c).Reachable u v := by
    by_contra hh
    have hp : ∀ u v, G.Adj u v → (wildColorGraph G γ W c).Reachable u v := by
      intro u v ha
      by_contra hn
      exact hh ⟨u,v,ha,hn⟩
    letI : Nonempty V := hg.nonempty
    apply hc
    refine ⟨?_⟩
    intro u v
    exact D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamGraph.reachable_map_of_adj id (fun {x y} hxy => hp x y hxy) (hg u v)
  obtain ⟨u,v,ha,hc⟩ := hcross
  refine ⟨s(u,v),Finset.mem_sdiff.mpr ⟨?_,?_⟩,dip_pos_of_crossing G γ W c hc⟩
  · simpa only [Set.Finite.mem_toFinset,SimpleGraph.mem_edgeSet] using ha
  · intro he
    apply hc
    apply Adj.reachable
    rw [wildColorGraph,SimpleGraph.fromEdgeSet_adj]
    exact ⟨Or.inl he,ha.ne⟩
theorem step_positive (G : SimpleGraph V) (γ : G.edgeSet → C) (hg : G.Connected)
    (W : Finset (Sym2 V)) (hw : (W : Set _) ⊆ G.edgeSet) {e}
    (hs : IsGreedyStep G γ W e) : 0 < dip G γ W e := by
  obtain ⟨f,hf,hpos⟩ := exists_positive_dip G γ hg W hw hs.1
  exact lt_of_lt_of_le hpos (hs.2.2.1 f hf)
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
open SimpleGraph
open D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]
private theorem exists_greedy_step (G : SimpleGraph V) (γ : G.edgeSet → C) (hg : G.Connected)
    (W : Finset (Sym2 V)) (hw : (W : Set _) ⊆ G.edgeSet) (hn : ¬IsColorConnecting G γ W) :
    ∃ e, IsGreedyStep G γ W e := by
  classical
  obtain ⟨f,hf,_⟩ := exists_positive_dip G γ hg W hw hn
  let S := (Set.toFinite G.edgeSet).toFinset \ W
  obtain ⟨d,hd,hmax⟩ := S.exists_max_image (dip G γ W) ⟨f,hf⟩
  let T := S.filter (fun e => dip G γ W e = dip G γ W d)
  have hT : T.Nonempty := ⟨d,Finset.mem_filter.mpr ⟨hd,rfl⟩⟩
  obtain ⟨e,he,hpot⟩ := T.exists_max_image (potential G γ W) hT
  obtain ⟨heS,hed⟩ := Finset.mem_filter.mp he
  refine ⟨e,hn,heS,?_,?_⟩
  · intro g hg
    rw [hed]
    exact hmax g hg
  · intro g hg hge hlex
    have hgt : g ∈ T := Finset.mem_filter.mpr ⟨hg,hge.trans hed⟩
    exact not_lt_of_ge (hpot g hgt) hlex
theorem exists_greedy_output (G : SimpleGraph V) (γ : G.edgeSet → C) (hg : G.Connected) :
    ∃ U, IsGreedyOutput G γ U := by
  classical
  let R := ((Set.toFinite G.edgeSet).toFinset).powerset.filter (IsGreedyRun G γ)
  have hR : R.Nonempty := ⟨∅,Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.empty_subset _),.empty⟩⟩
  obtain ⟨W,hW,hmax⟩ := R.exists_max_image Finset.card hR
  obtain ⟨hsub,hr⟩ := Finset.mem_filter.mp hW
  have hv : (W : Set _) ⊆ G.edgeSet := by
    intro e he
    have := (Finset.mem_powerset.mp hsub) he
    simpa [] using this
  by_cases hc : IsColorConnecting G γ W
  · exact ⟨W,hr,hc⟩
  · obtain ⟨e,he⟩ := exists_greedy_step G γ hg W hv hc
    have hm := Finset.mem_sdiff.mp he.2.1
    have hnew : insert e W ∈ R := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr ?_,.step hr he⟩
      exact Finset.insert_subset hm.1 (Finset.mem_powerset.mp hsub)
    have hn := hmax (insert e W) hnew
    rw [Finset.card_insert_of_notMem hm.2] at hn
    omega
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
