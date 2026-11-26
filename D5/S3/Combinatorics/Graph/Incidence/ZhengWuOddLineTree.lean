/- GID: D5/S3/Combinatorics/Graph/Incidence/ZhengWuOddLineTree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Incidence/ZhengWuOddLineTree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Odd line-graph spanning trees are characterized by odd branches of an endpoint split tree. -/

import D5.S3.Combinatorics.Graph.Incidence.EndpointSplit
import D5.S3.Combinatorics.Graph.Incidence.TreeParity
import Mathlib.Data.Set.Card.Arithmetic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Incidence.ZhengWuOddLineTree

open SimpleGraph
open D5.S3.Combinatorics.Graph.Incidence.EndpointSplit
open D5.S3.Combinatorics.Graph.Incidence.TreeParity (exists_isTree_odd_neighborSet_card)
open scoped Sym2 BigOperators

section

variable {V : Type} {F : SimpleGraph V}

/-- The tree spans the actual edges of the original graph. -/
private def HasOddLineTree (F : SimpleGraph V) : Prop :=
  ∃ H : SimpleGraph F.edgeSet, H ≤ F.lineGraph ∧ H.IsTree ∧
    ∀ e, Odd (Nat.card (H.neighborSet e))

private theorem hasOddLineTree_positive_even [Finite V] (h : HasOddLineTree F) :
    0 < Nat.card F.edgeSet ∧ Even (Nat.card F.edgeSet) := by
  classical
  obtain ⟨H, _, ht, ho⟩ := h
  have := ht.nonempty
  let := Fintype.ofFinite F.edgeSet
  refine ⟨Nat.card_pos, ?_⟩
  have hh := H.even_card_odd_degree_vertices
  have hall (e : F.edgeSet) : Odd (H.degree e) := by
    rw [← H.card_neighborSet_eq_degree e, ← Nat.card_eq_fintype_card]
    exact ho e
  simpa [hall, Nat.card_eq_fintype_card] using hh

/-- The number of odd-order components after deleting the designated vertex. -/
private noncomputable def oddBranchCount {W : Type} (G : SimpleGraph W) (b : W) : ℕ :=
  Nat.card {C : (TreeParity.withoutVertex G b).ConnectedComponent // Odd (Nat.card C.supp)}

/-- The endpoint-partition criterion in the Zheng–Wu event. -/
private def HasOddBranchSplitTree (F : SimpleGraph V) : Prop :=
  0 < Nat.card F.edgeSet ∧ Even (Nat.card F.edgeSet) ∧
    ∃ P : EndpointPartition F, P.splitGraph.IsTree ∧
      ∀ b : P.Block, 2 ≤ Nat.card (P.splitGraph.neighborSet b) →
        2 ≤ oddBranchCount P.splitGraph b

end

section

variable {V : Type*} {F : SimpleGraph V} {P : EndpointPartition F}

/-- Forget a block member's incidence and component witnesses. -/
private def memberEdge (b : P.Block) (e : P.Members b) : F.edgeSet := e.val.val

private theorem memberEdge_injective (b : P.Block) : Function.Injective (memberEdge b) := by
  intro e f h
  exact Subtype.ext (Subtype.ext h)

/-- Two distinct original edges have at most one common endpoint. -/
private theorem sharedEndpoint_unique {e f : F.edgeSet} (hef : e ≠ f) {u v : V}
    (hue : u ∈ e.val) (huf : u ∈ f.val) (hve : v ∈ e.val) (hvf : v ∈ f.val) : u = v := by
  by_contra h
  exact hef (Subtype.ext (Sym2.eq_of_ne_mem h hue hve huf hvf))


end

section

variable {V : Type} {F : SimpleGraph V} (P : EndpointPartition F)

@[local simp] private theorem edgeEquiv_val (e : F.edgeSet) : (P.edgeEquiv e).val = P.splitPair e := rfl

private theorem membersEquivNeighbor_pair (b : P.Block) (a : P.Members b) :
    s(b, (P.membersEquivNeighbor b a).val) = P.splitPair a.val.val :=
  Sym2.other_spec _

end

section

variable {V : Type*} {F : SimpleGraph V}

/-- Restrict a line-graph subgraph to all edges at one endpoint. -/
private def endpointGraph (H : SimpleGraph F.edgeSet) (v : V) : SimpleGraph (Incident F v) :=
  H.induce ({e : F.edgeSet | v ∈ e.val} : Set F.edgeSet)

/-- Partition each endpoint's incident edges by reachability in its restriction. -/
private def forestPartition (H : SimpleGraph F.edgeSet) : EndpointPartition F :=
  fun v => (endpointGraph H v).reachableSetoid

/-- The restriction to one component of one endpoint graph. -/
private def blockGraph (H : SimpleGraph F.edgeSet) (b : (forestPartition H).Block) :
    SimpleGraph ((forestPartition H).Members b) :=
  ConnectedComponent.toSimpleGraph (G := endpointGraph H b.1) b.2

private theorem blockGraph_isTree {H : SimpleGraph F.edgeSet} (hH : H.IsAcyclic)
    (b : (forestPartition H).Block) : (blockGraph H b).IsTree :=
  (hH.induce _).isTree_connectedComponent b.2

private theorem splitGraph_connected_of_line_subgraph {H : SimpleGraph F.edgeSet}
    (hsub : H ≤ F.lineGraph) (hH : H.Connected) : (forestPartition H).splitGraph.Connected := by
  apply (forestPartition H).splitGraph_connected_of_steps hH
  intro e f h
  obtain ⟨_, v, he, hf⟩ := lineGraph_adj_iff_exists.mp (hsub h)
  let a : Incident F v := ⟨e, he⟩
  let b : Incident F v := ⟨f, hf⟩
  have heq : Quotient.mk ((forestPartition H) v) a = Quotient.mk ((forestPartition H) v) b :=
    Quotient.sound (Adj.reachable (G := endpointGraph H v) (u := a) (v := b) h)
  let b := (forestPartition H).blockOf v a
  have hb : b ∈ (forestPartition H).splitPair e :=
    ((forestPartition H).mem_splitPair_iff b e).mpr ⟨a.property, rfl⟩
  refine ⟨b, hb, ?_⟩
  exact ((forestPartition H).mem_splitPair_iff _ _).mpr ⟨hf, heq.symm⟩

/-- The subgraph on a block of the endpoint forest includes in the supplied line-graph subgraph. -/
private def blockEmbedding (H : SimpleGraph F.edgeSet) (b : (forestPartition H).Block) :
    blockGraph H b ↪g H where
  toFun := memberEdge b
  inj' := memberEdge_injective b
  map_rel_iff' := Iff.rfl

private theorem edgeMem_memberEndpoints {H : SimpleGraph F.edgeSet}
    {b : (forestPartition H).Block} (e : (blockGraph H b).edgeSet)
    {a : F.edgeSet} (ha : a ∈ ((blockEmbedding H b).mapEdgeSet e).val) :
    ∃ x : (forestPartition H).Members b, memberEdge b x = a := by
  have hm : a ∈ (e.val.map (memberEdge b)) := ha
  obtain ⟨x, _, hx⟩ := Sym2.mem_map.mp hm
  exact ⟨x, hx⟩

/-- Every line-subgraph edge belongs to a unique local block graph. -/
private noncomputable def blockEdgesEquiv (H : SimpleGraph F.edgeSet) (hsub : H ≤ F.lineGraph) :
    (Σ b : (forestPartition H).Block, (blockGraph H b).edgeSet) ≃ H.edgeSet := by
  let P := forestPartition H
  let f (p : Σ b : P.Block, (blockGraph H b).edgeSet) :=
    (blockEmbedding H p.1).mapEdgeSet p.2
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨b, e⟩ ⟨c, f'⟩ h
    rcases e with ⟨⟨a, d⟩, had⟩
    let x := memberEdge b a
    let y := memberEdge b d
    have hxy : H.Adj x y := had
    have hx : x ∈ ((blockEmbedding H c).mapEdgeSet f').val := by
      rw [← show (blockEmbedding H b).mapEdgeSet ⟨s(a, d), had⟩ =
        (blockEmbedding H c).mapEdgeSet f' from h]
      exact Sym2.mem_mk_left x y
    have hy : y ∈ ((blockEmbedding H c).mapEdgeSet f').val := by
      rw [← show (blockEmbedding H b).mapEdgeSet ⟨s(a, d), had⟩ =
        (blockEmbedding H c).mapEdgeSet f' from h]
      exact Sym2.mem_mk_right x y
    obtain ⟨a', ha'⟩ := edgeMem_memberEndpoints f' hx
    obtain ⟨d', hd'⟩ := edgeMem_memberEndpoints f' hy
    have hroot : b.1 = c.1 :=
      sharedEndpoint_unique hxy.ne a.val.property d.val.property
        (ha' ▸ a'.val.property) (hd' ▸ d'.val.property)
    have hb : b = c := by
      rcases b with ⟨v, bc⟩
      rcases c with ⟨w, cc⟩
      change v = w at hroot
      subst w
      have hinc : a.val = a'.val := Subtype.ext ha'.symm
      have hc : bc = cc := a.property.symm.trans ((congrArg (Quotient.mk (P v)) hinc).trans a'.property)
      subst cc
      rfl
    subst c
    exact congrArg (Sigma.mk b) ((blockEmbedding H b).mapEdgeSet.injective h)
  · rintro ⟨⟨e, f'⟩, he⟩
    have h : H.Adj e f' := he
    obtain ⟨_, v, hev, hfv⟩ := lineGraph_adj_iff_exists.mp (hsub h)
    let a : Incident F v := ⟨e, hev⟩
    let d : Incident F v := ⟨f', hfv⟩
    let b := P.blockOf v a
    have hc : Quotient.mk (P v) d = Quotient.mk (P v) a :=
      Quotient.sound (Adj.reachable (G := endpointGraph H v) (u := d) (v := a) h.symm)
    let a' : P.Members b := ⟨a, rfl⟩
    let d' : P.Members b := ⟨d, hc⟩
    exact ⟨⟨b, ⟨s(a', d'), h⟩⟩, rfl⟩

/-- The endpoint forest components of a spanning tree give a split tree on
one more vertex than the number of original edges. -/
private theorem forestPartition_isTree_and_card [Finite V] {H : SimpleGraph F.edgeSet}
    (hsub : H ≤ F.lineGraph) (hH : H.IsTree) :
    (forestPartition H).splitGraph.IsTree ∧
      Nat.card (forestPartition H).Block = Nat.card F.edgeSet + 1 := by
  let P := forestPartition H
  classical
  let := Fintype.ofFinite P.Block
  have hcard (b : P.Block) :
      Nat.card (blockGraph H b).edgeSet + 1 = Nat.card (P.Members b) :=
    (isTree_iff_connected_and_card.mp (blockGraph_isTree hH.isAcyclic b)).2
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset P.Block)) rfl (fun b _ => hcard b)
  rw [Finset.sum_add_distrib, ← Nat.card_sigma, ← Nat.card_sigma, card_total_members P,
    Nat.card_congr (blockEdgesEquiv H hsub)] at hsum
  have hh := (isTree_iff_connected_and_card.mp hH).2
  have hcount : Nat.card P.Block = Nat.card F.edgeSet + 1 := by
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, ← Nat.card_eq_fintype_card] at hsum
    omega
  refine ⟨isTree_iff_connected_and_card.mpr
    ⟨splitGraph_connected_of_line_subgraph hsub hH.connected, ?_⟩, hcount⟩
  change Nat.card P.splitGraph.edgeSet + 1 = Nat.card P.Block
  rw [P.card_edgeSet, hcount]

end

section

variable {V : Type} {F : SimpleGraph V}
variable {H : SimpleGraph F.edgeSet}

/-- A member at the endpoint of a given edge lies in the block to which the partition sends it. -/
private def memberAt (H : SimpleGraph F.edgeSet) {v : V} (a : Incident F v) :
    (forestPartition H).Members ((forestPartition H).blockOf v a) :=
  ⟨a, rfl⟩

/-- The local neighbors at a block member are precisely the neighbors incident to its root. -/
private def blockNeighborsEquiv (b : (forestPartition H).Block) (x : (forestPartition H).Members b) :
    (blockGraph H b).neighborSet x ≃ {y : H.neighborSet (memberEdge b x) // b.1 ∈ y.val.val} where
  toFun y := ⟨⟨memberEdge b y.val, y.property⟩, y.val.val.property⟩
  invFun y :=
    let a : Incident F b.1 := ⟨y.val.val, y.property⟩
    have hadj : (endpointGraph H b.1).Adj a x.val := (H.adj_symm y.val.property)
    have hc : Quotient.mk (forestPartition H b.1) a = b.2 :=
      (Quotient.sound hadj.reachable).trans x.property
    ⟨⟨a, hc⟩, y.val.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The two local degrees of an edge of the original graph sum to its line-subgraph degree. -/
private theorem card_neighbors_eq_add_local [Finite V] (hsub : H ≤ F.lineGraph) {u v : V} (huv : F.Adj u v) :
    let e : F.edgeSet := ⟨s(u, v), huv⟩
    let e_u : Incident F u := ⟨e, Sym2.mem_mk_left u v⟩
    let e_v : Incident F v := ⟨e, Sym2.mem_mk_right u v⟩
    Nat.card (H.neighborSet e) =
      Nat.card ((blockGraph H ((forestPartition H).blockOf u e_u)).neighborSet (memberAt H e_u)) +
      Nat.card ((blockGraph H ((forestPartition H).blockOf v e_v)).neighborSet (memberAt H e_v)) := by
  classical
  dsimp only
  let e : F.edgeSet := ⟨s(u, v), huv⟩
  let e_u : Incident F u := ⟨e, Sym2.mem_mk_left u v⟩
  let e_v : Incident F v := ⟨e, Sym2.mem_mk_right u v⟩
  rw [Nat.card_congr (blockNeighborsEquiv _ (memberAt H e_u)),
    Nat.card_congr (blockNeighborsEquiv _ (memberAt H e_v))]
  let Su (f : H.neighborSet e) := u ∈ f.val.val
  let Sv (f : H.neighborSet e) := v ∈ f.val.val
  have hv_iff (f : H.neighborSet e) : (¬ Su f) ↔ Sv f := by
    have h := f.property
    obtain ⟨_, w, hw, hw'⟩ := lineGraph_adj_iff_exists.mp (hsub h)
    change w ∈ s(u, v) at hw
    constructor
    · intro hnu
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact False.elim (hnu hw')
      · exact hw'
    · intro hv hu
      exact huv.ne (sharedEndpoint_unique h.ne
        (Sym2.mem_mk_left u v) hu (Sym2.mem_mk_right u v) hv)
  rw [← Nat.card_congr (Equiv.sumCompl Su), Nat.card_sum,
    Nat.card_congr (Equiv.subtypeEquivRight hv_iff)]
  rfl

/-- The odd local degree predicate at a block uses the original edge label. -/
private def OddAt (H : SimpleGraph F.edgeSet) (b : (forestPartition H).Block) (e : F.edgeSet) : Prop :=
  ∃ a : (forestPartition H).Members b, memberEdge b a = e ∧
    Odd (Nat.card ((blockGraph H b).neighborSet a))

private theorem oddAt_iff (b : (forestPartition H).Block) (a : (forestPartition H).Members b) :
    OddAt H b (memberEdge b a) ↔ Odd (Nat.card ((blockGraph H b).neighborSet a)) := by
  constructor
  · rintro ⟨a', ha', hodd⟩
    rwa [(memberEdge_injective b ha')] at hodd
  · exact fun h => ⟨a, rfl, h⟩

private theorem oddAt_mem {b : (forestPartition H).Block} {e : F.edgeSet} (h : OddAt H b e) :
    b ∈ (forestPartition H).splitPair e := by
  obtain ⟨a, rfl, _⟩ := h
  exact ((forestPartition H).mem_splitPair_iff _ _).mpr ⟨a.val.property, a.property⟩

private theorem existsUnique_oddAt [Finite V] (hsub : H ≤ F.lineGraph)
    (hodd : ∀ e, Odd (Nat.card (H.neighborSet e))) (e : F.edgeSet) :
    ∃! b : (forestPartition H).Block, OddAt H b e := by
  rcases e with ⟨⟨u, v⟩, huv⟩
  let e : F.edgeSet := ⟨s(u, v), huv⟩
  let P := forestPartition H
  let e_u : Incident F u := ⟨e, Sym2.mem_mk_left u v⟩
  let e_v : Incident F v := ⟨e, Sym2.mem_mk_right u v⟩
  let b := P.blockOf u e_u
  let c := P.blockOf v e_v
  have hsum := hodd e
  rw [card_neighbors_eq_add_local hsub (show F.Adj u v from huv), Nat.odd_add,
    ← Nat.not_odd_iff_even,
    ← oddAt_iff b (memberAt H e_u), ← oddAt_iff c (memberAt H e_v)] at hsum
  change OddAt H b e ↔ ¬ OddAt H c e at hsum
  have hpair : P.splitPair e = s(b, c) := rfl
  have hend (d : P.Block) (hd : OddAt H d e) : d = b ∨ d = c :=
    Sym2.mem_iff.mp (hpair ▸ oddAt_mem hd)
  by_cases hb : OddAt H b e
  · refine ⟨b, hb, fun d hd => (hend d hd).resolve_right ?_⟩
    rintro rfl
    exact (hsum.mp hb) hd
  · refine ⟨c, Classical.byContradiction (fun hc => hb (hsum.mpr hc)), fun d hd => (hend d hd).resolve_left ?_⟩
    rintro rfl
    exact hb hd

/-- Every split edge points to the endpoint block with odd local degree. -/
private noncomputable def oddHead [Finite V] (hsub : H ≤ F.lineGraph)
    (hodd : ∀ e, Odd (Nat.card (H.neighborSet e))) :
    (forestPartition H).splitGraph.edgeSet → (forestPartition H).Block :=
  fun f => Classical.choose (existsUnique_oddAt hsub hodd ((forestPartition H).edgeEquiv.symm f))

private theorem oddHead_eq_iff [Finite V] (hsub : H ≤ F.lineGraph)
    (hodd : ∀ e, Odd (Nat.card (H.neighborSet e)))
    (f : (forestPartition H).splitGraph.edgeSet) (b : (forestPartition H).Block) :
    oddHead hsub hodd f = b ↔ OddAt H b ((forestPartition H).edgeEquiv.symm f) := by
  have h := Classical.choose_spec
    (existsUnique_oddAt hsub hodd ((forestPartition H).edgeEquiv.symm f))
  exact ⟨fun he => he ▸ h.1, fun hb => (h.2 b hb).symm⟩

private theorem oddHead_mem [Finite V] (hsub : H ≤ F.lineGraph)
    (hodd : ∀ e, Odd (Nat.card (H.neighborSet e)))
    (f : (forestPartition H).splitGraph.edgeSet) : oddHead hsub hodd f ∈ f.val := by
  have h := oddAt_mem ((oddHead_eq_iff hsub hodd f _).mp rfl)
  rw [← edgeEquiv_val, Equiv.apply_symm_apply] at h
  exact h

/-- Incoming split edges correspond to the odd-degree vertices of the local tree. -/
private noncomputable def oddMembersEquivIncoming [Finite V] (hsub : H ≤ F.lineGraph)
    (hodd : ∀ e, Odd (Nat.card (H.neighborSet e))) (b : (forestPartition H).Block) :
    {a : (forestPartition H).Members b // Odd (Nat.card ((blockGraph H b).neighborSet a))} ≃
      {f : (forestPartition H).splitGraph.edgeSet // oddHead hsub hodd f = b} := by
  let P := forestPartition H
  let f (a : {a : P.Members b // Odd (Nat.card ((blockGraph H b).neighborSet a))}) :
      {f : P.splitGraph.edgeSet // oddHead hsub hodd f = b} :=
    ⟨P.edgeEquiv (memberEdge b a.val), by
      rw [oddHead_eq_iff, Equiv.symm_apply_apply]
      exact (oddAt_iff b a.val).mpr a.property⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a a' he
    exact Subtype.ext (memberEdge_injective b (P.edgeEquiv.injective (congrArg Subtype.val he)))
  · intro g
    obtain ⟨a, ha, ho⟩ := (oddHead_eq_iff hsub hodd g.val b).mp g.property
    refine ⟨⟨a, ho⟩, Subtype.ext ?_⟩
    change P.edgeEquiv (memberEdge b a) = g.val
    rw [ha, Equiv.apply_symm_apply]

private theorem even_card_odd_neighbors {W : Type*} [Finite W] (G : SimpleGraph W) :
    Even (Nat.card {x : W // Odd (Nat.card (G.neighborSet x))}) := by
  classical
  let := Fintype.ofFinite W
  have hdeg (x : W) : Nat.card (G.neighborSet x) = G.degree x :=
    Nat.card_eq_fintype_card.trans (G.card_neighborSet_eq_degree x)
  simp only [hdeg, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact G.even_card_odd_degree_vertices

private theorem oddHead_even_indegree [Finite V] (hsub : H ≤ F.lineGraph)
    (hodd : ∀ e, Odd (Nat.card (H.neighborSet e))) (b : (forestPartition H).Block) :
    Even (TreeParity.indegree (oddHead hsub hodd) b) := by
  rw [TreeParity.indegree, ← Nat.card_congr (oddMembersEquivIncoming hsub hodd b)]
  exact even_card_odd_neighbors (blockGraph H b)

private theorem two_le_card_odd_neighbors_of_isTree {W : Type*} [Finite W] (G : SimpleGraph W)
    (hT : G.IsTree) (hcard : 2 ≤ Nat.card W) :
    2 ≤ Nat.card {x : W // Odd (Nat.card (G.neighborSet x))} := by
  classical
  let := Fintype.ofFinite W
  have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by
    rwa [← Nat.card_eq_fintype_card])
  obtain ⟨u, v, hne, hu, hv⟩ := hT.exists_ne_and_degree_eq_one
  have hodd (x : W) (h : G.degree x = 1) : Odd (Nat.card (G.neighborSet x)) := by
    rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree, h]
    decide
  have : Nontrivial {x : W // Odd (Nat.card (G.neighborSet x))} :=
    ⟨⟨⟨u, hodd u hu⟩, ⟨v, hodd v hv⟩, fun h => hne (congrArg Subtype.val h)⟩⟩
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance

/-- The local odd-degree labels and the odd branches are indexed by the same split edges. -/
private noncomputable def oddMembersEquivOddBranches [Finite V] (hsub : H ≤ F.lineGraph)
    (hodd : ∀ e, Odd (Nat.card (H.neighborSet e))) (hT : (forestPartition H).splitGraph.IsTree)
    (hcard : Odd (Nat.card (forestPartition H).Block)) (b : (forestPartition H).Block) :
    {a : (forestPartition H).Members b // Odd (Nat.card ((blockGraph H b).neighborSet a))} ≃
      {C : (TreeParity.withoutVertex (forestPartition H).splitGraph b).ConnectedComponent //
        Odd (Nat.card C.supp)} := by
  let P := forestPartition H
  classical
  let := Fintype.ofFinite P.Block
  let E := TreeParity.neighborEquivBranch hT b
  apply Equiv.subtypeEquiv ((P.membersEquivNeighbor b).trans E)
  intro a
  let w := P.membersEquivNeighbor b a
  let e : P.splitGraph.edgeSet := ⟨s(w.val, b), P.splitGraph.adj_symm w.property⟩
  have he : e = P.edgeEquiv (memberEdge b a) := by
    apply Subtype.ext
    exact Sym2.eq_swap.trans (membersEquivNeighbor_pair P b a)
  have hbranch := (TreeParity.even_indegrees_iff_odd_neighbor_branches hT hcard
    (oddHead hsub hodd) (oddHead_mem hsub hodd)).mp (oddHead_even_indegree hsub hodd) b w
  change _ ↔ Odd (Nat.card (TreeParity.neighborBranch P.splitGraph b w).supp)
  rw [← hbranch]
  change _ ↔ oddHead hsub hodd e = b
  rw [he, oddHead_eq_iff, Equiv.symm_apply_apply]
  exact (oddAt_iff b a).symm

/-- The full forward implication of the Zheng–Wu line-graph criterion. -/
private theorem hasOddBranchSplitTree_of_hasOddLineTree [Finite V] (h : HasOddLineTree F) :
    HasOddBranchSplitTree F := by
  obtain ⟨hpos, heven⟩ := hasOddLineTree_positive_even h
  obtain ⟨H, hsub, hH, hodd⟩ := h
  let P := forestPartition H
  obtain ⟨ht, hcard⟩ := forestPartition_isTree_and_card hsub hH
  have hOdd : Odd (Nat.card P.Block) := by
    rw [hcard, Nat.odd_add]
    simpa using heven
  refine ⟨hpos, heven, P, ht, fun b hb => ?_⟩
  have hmem : 2 ≤ Nat.card (P.Members b) := by
    rw [Nat.card_congr (P.membersEquivNeighbor b)]
    exact hb
  change 2 ≤ Nat.card {C : (TreeParity.withoutVertex P.splitGraph b).ConnectedComponent //
    Odd (Nat.card C.supp)}
  rw [← Nat.card_congr (oddMembersEquivOddBranches hsub hodd ht hOdd b)]
  exact two_le_card_odd_neighbors_of_isTree _ (blockGraph_isTree hH.isAcyclic b) hmem

end

section

variable {V : Type} {F : SimpleGraph V} {P : EndpointPartition F}

/-- A block member belongs to the split edge with the same original label. -/
private theorem member_mem_splitPair (b : P.Block) (a : P.Members b) :
    b ∈ P.splitPair (memberEdge b a) :=
  (P.mem_splitPair_iff b _).mpr ⟨a.val.property, a.property⟩

private noncomputable def incomingEquiv (head : P.splitGraph.edgeSet → P.Block)
    (hhead : ∀ e, head e ∈ e.val) (b : P.Block) :
    {a : P.Members b // head (P.edgeEquiv (memberEdge b a)) = b} ≃
      {e : P.splitGraph.edgeSet // head e = b} := by
  let f (a : {a : P.Members b // head (P.edgeEquiv (memberEdge b a)) = b}) :
      {e : P.splitGraph.edgeSet // head e = b} :=
    ⟨P.edgeEquiv (memberEdge b a.val), a.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro a d h
    apply Subtype.ext
    exact memberEdge_injective b (P.edgeEquiv.injective (congrArg Subtype.val h))
  · intro e
    let g := P.edgeEquiv.symm e.val
    have he : P.edgeEquiv g = e.val := P.edgeEquiv.apply_symm_apply _
    have hb : b ∈ P.splitPair g := by
      rw [← edgeEquiv_val P g, he]
      have hh := hhead e.val
      rw [e.property] at hh
      exact hh
    obtain ⟨hv, hc⟩ := (P.mem_splitPair_iff b g).mp hb
    exact ⟨⟨⟨⟨g, hv⟩, hc⟩, he ▸ e.property⟩, Subtype.ext he⟩

private noncomputable def incomingEquivOddBranches [Fintype P.Block]
    (ht : P.splitGraph.IsTree) (htOdd : Odd (Nat.card P.Block))
    (head : P.splitGraph.edgeSet → P.Block) (hhead : ∀ e, head e ∈ e.val)
    (heven : ∀ b, Even (TreeParity.indegree head b)) (b : P.Block) :
    {a : P.Members b // head (P.edgeEquiv (memberEdge b a)) = b} ≃
      {C : (TreeParity.withoutVertex P.splitGraph b).ConnectedComponent //
        Odd (Nat.card C.supp)} := by
  apply Equiv.subtypeEquiv ((P.membersEquivNeighbor b).trans (TreeParity.neighborEquivBranch ht b))
  intro a
  let w := P.membersEquivNeighbor b a
  have he : (⟨s(w.val, b), P.splitGraph.adj_symm w.property⟩ : P.splitGraph.edgeSet) =
      P.edgeEquiv (memberEdge b a) :=
    Subtype.ext (Sym2.eq_swap.trans (membersEquivNeighbor_pair P b a))
  exact he ▸ (TreeParity.even_indegrees_iff_odd_neighbor_branches ht htOdd head hhead).mp heven b w

/-- Even split indegrees prescribe the local odd vertices. A singleton block
uses the edgeless tree and receives no oriented edge. -/
private theorem exists_localTrees [Finite V] (ht : P.splitGraph.IsTree)
    (hm : Even (Nat.card F.edgeSet))
    (hb : ∀ b : P.Block, 2 ≤ Nat.card (P.splitGraph.neighborSet b) →
      2 ≤ oddBranchCount P.splitGraph b) :
    ∃ (head : P.splitGraph.edgeSet → P.Block)
      (T : (b : P.Block) → SimpleGraph (P.Members b)),
      (∀ e, head e ∈ e.val) ∧ (∀ b, (T b).IsTree) ∧
      ∀ b (a : P.Members b), Odd (Nat.card ((T b).neighborSet a)) ↔
        head (P.edgeEquiv (memberEdge b a)) = b := by
  classical
  let := Fintype.ofFinite P.Block
  have htOdd : Odd (Nat.card P.Block) := by
    rw [← (isTree_iff_connected_and_card.mp ht).2, P.card_edgeSet, Nat.odd_add]
    simpa using hm
  obtain ⟨head, ⟨hhead, heven⟩, _⟩ :=
    TreeParity.existsUnique_even_indegree_head ht htOdd
  refine ⟨head, ?_⟩
  have localTree (b : P.Block) :
      ∃ G : SimpleGraph (P.Members b), G.IsTree ∧
        ∀ a : P.Members b, Odd (Nat.card (G.neighborSet a)) ↔
          head (P.edgeEquiv (memberEdge b a)) = b := by
    let := Fintype.ofFinite (P.Members b)
    let S : Finset (P.Members b) :=
      Finset.univ.filter (fun a => head (P.edgeEquiv (memberEdge b a)) = b)
    have hS (a : P.Members b) : a ∈ S ↔ head (P.edgeEquiv (memberEdge b a)) = b := by
      simp [S]
    have hscard : Nat.card {a : P.Members b // head (P.edgeEquiv (memberEdge b a)) = b} =
        S.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hSeven : Even S.card := by
      rw [← hscard, Nat.card_congr (incomingEquiv head hhead b)]
      exact heven b
    by_cases hbig : 2 ≤ Nat.card (P.Members b)
    · have hneigh : 2 ≤ Nat.card (P.splitGraph.neighborSet b) :=
        (Nat.card_congr (P.membersEquivNeighbor b)) ▸ hbig
      have hbranches := hb b hneigh
      change 2 ≤ Nat.card {C : (TreeParity.withoutVertex P.splitGraph b).ConnectedComponent //
        Odd (Nat.card C.supp)} at hbranches
      rw [← Nat.card_congr (incomingEquivOddBranches ht htOdd head hhead heven b), hscard] at hbranches
      obtain ⟨G, hG, hodd⟩ := exists_isTree_odd_neighborSet_card S
        (Finset.card_pos.mp (by omega)) hSeven
      exact ⟨G, hG, fun a => (hodd a).trans (hS a)⟩
    · have := P.members_nonempty b
      have hone : Nat.card (P.Members b) = 1 := by
        have : 0 < Nat.card (P.Members b) := Nat.card_pos
        omega
      have hsingle : Subsingleton (P.Members b) := Fintype.card_le_one_iff_subsingleton.mp (by
        rw [← Nat.card_eq_fintype_card, hone])
      have hle : S.card ≤ 1 := by
        calc
          S.card ≤ (Finset.univ : Finset (P.Members b)).card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = 1 := by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hone]
      have hzero : S.card = 0 := by
        have := Nat.even_iff.mp hSeven
        omega
      refine ⟨⊥, ?_, ?_⟩
      · exact ⟨(connected_iff _).mpr ⟨fun a d => (hsingle.elim a d).symm ▸ Reachable.rfl,
          P.members_nonempty b⟩, isAcyclic_bot⟩
      · intro a
        have hnmem : a ∉ S := by rw [Finset.card_eq_zero.mp hzero]; exact Finset.notMem_empty _
        refine iff_of_false ?_ (mt (hS a).mpr hnmem)
        simp
  choose T hT hodd using localTree
  exact ⟨T, hhead, hT, hodd⟩

end

section

variable {V : Type} {F : SimpleGraph V} {P : EndpointPartition F}

private def memberEmbedding (b : P.Block) : P.Members b ↪ F.edgeSet :=
  ⟨memberEdge b, memberEdge_injective b⟩

private def mappedBlock (T : (b : P.Block) → SimpleGraph (P.Members b)) (b : P.Block) :
    SimpleGraph F.edgeSet :=
  (T b).map (memberEmbedding b)

/-- Join the local trees on the common set of original edge labels. -/
private def joinedGraph (T : (b : P.Block) → SimpleGraph (P.Members b)) : SimpleGraph F.edgeSet :=
  ⨆ b, mappedBlock T b

variable (T : (b : P.Block) → SimpleGraph (P.Members b))

private theorem mapped_adj_implies_mem {b : P.Block} {e f : F.edgeSet}
    (h : (mappedBlock T b).Adj e f) : b ∈ P.splitPair e ∧ b ∈ P.splitPair f := by
  obtain ⟨a, d, _, ha, hd⟩ := (map_adj (memberEmbedding b) (T b) e f).mp h
  exact ⟨ha ▸ member_mem_splitPair b a, hd ▸ member_mem_splitPair b d⟩

private theorem block_eq_of_common_edges {b c : P.Block} {e f : F.edgeSet} (hef : e ≠ f)
    (hbe : b ∈ P.splitPair e) (hbf : b ∈ P.splitPair f)
    (hce : c ∈ P.splitPair e) (hcf : c ∈ P.splitPair f) : b = c := by
  rcases b with ⟨u, B⟩
  rcases c with ⟨v, C⟩
  obtain ⟨hu, hB⟩ := (P.mem_splitPair_iff ⟨u, B⟩ e).mp hbe
  obtain ⟨huf, _⟩ := (P.mem_splitPair_iff ⟨u, B⟩ f).mp hbf
  obtain ⟨hv, hC⟩ := (P.mem_splitPair_iff ⟨v, C⟩ e).mp hce
  obtain ⟨hvf, _⟩ := (P.mem_splitPair_iff ⟨v, C⟩ f).mp hcf
  have huv := sharedEndpoint_unique hef hu huf hv hvf
  change u = v at huv
  subst v
  exact congrArg (Sigma.mk u) (hB.symm.trans hC)

private theorem mapped_adj_block_unique {b c : P.Block} {e f : F.edgeSet}
    (hb : (mappedBlock T b).Adj e f) (hc : (mappedBlock T c).Adj e f) : b = c := by
  obtain ⟨hbe, hbf⟩ := mapped_adj_implies_mem T hb
  obtain ⟨hce, hcf⟩ := mapped_adj_implies_mem T hc
  exact block_eq_of_common_edges hb.ne hbe hbf hce hcf

private theorem joinedGraph_le_lineGraph : joinedGraph T ≤ F.lineGraph := by
  intro e f h
  obtain ⟨b, hadj⟩ := iSup_adj.mp h
  obtain ⟨he, hf⟩ := mapped_adj_implies_mem T hadj
  exact lineGraph_adj_iff_exists.mpr ⟨hadj.ne, b.1,
    ((P.mem_splitPair_iff b e).mp he).1, ((P.mem_splitPair_iff b f).mp hf).1⟩

private theorem joinedGraph_connected (ht : P.splitGraph.Connected) (hT : ∀ b, (T b).Connected) :
    (joinedGraph T).Connected := by
  apply P.connected_of_splitGraph_connected ht
  intro b e f he hf
  obtain ⟨heRoot, heClass⟩ := (P.mem_splitPair_iff b e).mp he
  obtain ⟨hfRoot, hfClass⟩ := (P.mem_splitPair_iff b f).mp hf
  let a : P.Members b := ⟨⟨e, heRoot⟩, heClass⟩
  let d : P.Members b := ⟨⟨f, hfRoot⟩, hfClass⟩
  let inc : (T b) →g joinedGraph T :=
    (Hom.ofLE (le_iSup (mappedBlock T) b)).comp
      (Embedding.map (memberEmbedding b) (T b)).toHom
  exact ((hT b).preconnected a d).map inc

private theorem mapped_edgeSets_disjoint :
    Pairwise fun b c => Disjoint (mappedBlock T b).edgeSet (mappedBlock T c).edgeSet := by
  intro b c hbc
  apply Set.disjoint_left.mpr
  rintro ⟨e, f⟩ hb hc
  exact hbc (mapped_adj_block_unique T hb hc)

private theorem joinedGraph_edge_count [Finite V] (ht : P.splitGraph.IsTree)
    (hT : ∀ b, (T b).IsTree) :
    Nat.card (joinedGraph T).edgeSet + 1 = Nat.card F.edgeSet := by
  classical
  let := Fintype.ofFinite P.Block
  have hsum : Nat.card (joinedGraph T).edgeSet =
      ∑ b : P.Block, Nat.card (T b).edgeSet := by
    simp only [joinedGraph, Nat.card_coe_set_eq, edgeSet_iSup]
    rw [Set.ncard_iUnion_of_finite (fun _ => Set.toFinite _) (mapped_edgeSets_disjoint T),
      finsum_eq_sum_of_fintype]
    simp only [mappedBlock, edgeSet_map, Set.ncard_image_of_injective _ (memberEmbedding _).sym2Map.injective]
  have hadd (b : P.Block) : Nat.card (T b).edgeSet + 1 = Nat.card (P.Members b) :=
    (isTree_iff_connected_and_card.mp (hT b)).2
  have hn := Finset.sum_congr (s₁ := (Finset.univ : Finset P.Block)) rfl (fun b _ => hadd b)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    ← Nat.card_eq_fintype_card, ← hsum, ← Nat.card_sigma, card_total_members P] at hn
  have hm := (isTree_iff_connected_and_card.mp ht).2
  rw [P.card_edgeSet] at hm
  omega

private theorem joinedGraph_neighborSet {b c : P.Block} {e : F.edgeSet}
    (hp : P.splitPair e = s(b, c)) :
    (joinedGraph T).neighborSet e =
      (mappedBlock T b).neighborSet e ∪ (mappedBlock T c).neighborSet e := by
  ext f
  constructor
  · intro h
    have hAdj : (joinedGraph T).Adj e f := h
    obtain ⟨d, hd⟩ := iSup_adj.mp hAdj
    have hmem := (mapped_adj_implies_mem T hd).1
    rw [hp, Sym2.mem_iff] at hmem
    rcases hmem with rfl | rfl
    · exact Or.inl hd
    · exact Or.inr hd
  · rintro (h | h)
    · exact iSup_adj.mpr ⟨b, h⟩
    · exact iSup_adj.mpr ⟨c, h⟩

private theorem mapped_neighbors_disjoint {b c : P.Block} (hbc : b ≠ c) (e : F.edgeSet) :
    Disjoint ((mappedBlock T b).neighborSet e) ((mappedBlock T c).neighborSet e) :=
  Set.disjoint_left.mpr fun _ hb hc => hbc (mapped_adj_block_unique T hb hc)

private theorem joinedGraph_degree [Finite V] {b c : P.Block}
    (a : P.Members b) (d : P.Members c) {e : F.edgeSet}
    (ha : memberEdge b a = e) (hd : memberEdge c d = e)
    (hp : P.splitPair e = s(b, c)) (hbc : b ≠ c) :
    Nat.card ((joinedGraph T).neighborSet e) =
      Nat.card ((T b).neighborSet a) + Nat.card ((T c).neighborSet d) := by
  simp only [Nat.card_coe_set_eq]
  rw [joinedGraph_neighborSet T hp, Set.ncard_union_eq (mapped_neighbors_disjoint T hbc e)]
  have heq (x : P.Block) (m : P.Members x) (hm : memberEdge x m = e) :
      ((mappedBlock T x).neighborSet e).ncard = ((T x).neighborSet m).ncard := by
    rw [← hm]
    change (((T x).map (memberEmbedding x)).neighborSet (memberEmbedding x m)).ncard = _
    rw [neighborSet_map, Set.ncard_image_of_injective _ (memberEmbedding x).injective]
  rw [heq b a ha, heq c d hd]

end

section

variable {V : Type} [Finite V] {F : SimpleGraph V}

/-- The block trees join to an odd spanning tree of the original line graph. -/
private theorem hasOddLineTree_of_hasOddBranchSplitTree (h : HasOddBranchSplitTree F) :
    HasOddLineTree F := by
  obtain ⟨_, hm, P, ht, hbranch⟩ := h
  obtain ⟨head, T, hhead, hT, hodd⟩ := exists_localTrees ht hm hbranch
  refine ⟨joinedGraph T, joinedGraph_le_lineGraph T, ?_, ?_⟩
  · exact isTree_iff_connected_and_card.mpr
      ⟨joinedGraph_connected T ht.connected (fun b => (hT b).connected),
        joinedGraph_edge_count T ht hT⟩
  · rintro ⟨⟨u, v⟩, huv⟩
    change F.Adj u v at huv
    let e : F.edgeSet := ⟨s(u, v), huv⟩
    let eu : Incident F u := ⟨e, Sym2.mem_mk_left u v⟩
    let ev : Incident F v := ⟨e, Sym2.mem_mk_right u v⟩
    let b := P.blockOf u eu
    let c := P.blockOf v ev
    let a : P.Members b := ⟨eu, rfl⟩
    let d : P.Members c := ⟨ev, rfl⟩
    have hp : P.splitPair e = s(b, c) := rfl
    have hbc : b ≠ c := fun h => huv.ne (congrArg Sigma.fst h)
    have horient := hhead (P.edgeEquiv e)
    rw [edgeEquiv_val P e, hp, Sym2.mem_iff] at horient
    change Odd (Nat.card ((joinedGraph T).neighborSet e))
    rw [joinedGraph_degree T a d (e := e) rfl rfl hp hbc, Nat.odd_add, Nat.not_odd_iff_even.symm,
      hodd b a, hodd c d]
    change (head (P.edgeEquiv e) = b ↔ ¬ head (P.edgeEquiv e) = c)
    rcases horient with hb | hc
    · simp [hb, hbc]
    · simp [hc, hbc.symm]

end

/-- Zheng–Wu §5(2), line-graph subquestion. The two sides use the same finite root graph. -/
theorem result {V : Type} [Finite V] (F : SimpleGraph V) :
    (∃ H : SimpleGraph F.edgeSet, H ≤ F.lineGraph ∧ H.IsTree ∧
      ∀ e, Odd (Nat.card (H.neighborSet e))) ↔
    (0 < Nat.card F.edgeSet ∧ Even (Nat.card F.edgeSet) ∧
      ∃ P : EndpointPartition F, P.splitGraph.IsTree ∧
        ∀ b : P.Block, 2 ≤ Nat.card (P.splitGraph.neighborSet b) →
          2 ≤ Nat.card {C : (P.splitGraph.induce {x | x ≠ b}).ConnectedComponent //
            Odd (Nat.card C.supp)}) :=
  ⟨hasOddBranchSplitTree_of_hasOddLineTree, hasOddLineTree_of_hasOddBranchSplitTree⟩

end D5.S3.Combinatorics.Graph.Incidence.ZhengWuOddLineTree
