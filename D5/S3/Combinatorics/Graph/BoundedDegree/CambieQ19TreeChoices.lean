/- GID: D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.CycleGraph]
   utility: none
   digest: Spanning trees on actual Cambie supports are independent cycle-edge deletions. -/

import D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement

/-! The tree fibers over the support configurations of the fixed graph. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement

open SimpleGraph

section TreeFoundation

open scoped Sym2

private theorem sum_left_reachable {A B : Type} {G : SimpleGraph A} {H : SimpleGraph B}
    {x y : A} (h : (G ⊕g H).Reachable (.inl x) (.inl y)) : G.Reachable x y := by
  let f : A ⊕ B → A := Sum.elim id (fun _ => x)
  have hf {u v} (huv : (G ⊕g H).Adj u v) : G.Reachable (f u) (f v) := by
    rcases u with u | u <;> rcases v with v | v
    · exact ((sum_adj_inl).mp huv).reachable
    · exact (not_adj_sum_inl_inr _ _ huv).elim
    · exact (not_adj_sum_inl_inr _ _ huv.symm).elim
    · exact .rfl
  rw [reachable_iff_reflTransGen]
  exact (reachable_iff_reflTransGen ..).mp h |>.lift' f
    (fun _ _ huv => (reachable_iff_reflTransGen ..).mp (hf huv))

private theorem acyclic_sum {A B : Type} {G : SimpleGraph A} {H : SimpleGraph B}
    (hG : G.IsAcyclic) (hH : H.IsAcyclic) : (G ⊕g H).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  rintro (u | u) (v | v) h
  · rw [isBridge_iff]
    have he : (G ⊕g H).deleteEdges {s(Sum.inl u, Sum.inl v)} =
        G.deleteEdges {s(u, v)} ⊕g H := by
      ext (a | a) (b | b) <;> simp
    rw [he]
    exact fun hr => isBridge_iff.mp
      (isAcyclic_iff_forall_adj_isBridge.mp hG ((sum_adj_inl).mp h)) (sum_left_reachable hr)
  · exact (not_adj_sum_inl_inr _ _ h).elim
  · exact (not_adj_sum_inl_inr _ _ h.symm).elim
  · rw [isBridge_iff]
    have he : (G ⊕g H).deleteEdges {s(Sum.inr u, Sum.inr v)} =
        G ⊕g H.deleteEdges {s(u, v)} := by
      ext (a | a) (b | b) <;> simp
    rw [he]
    exact fun hr => isBridge_iff.mp
      (isAcyclic_iff_forall_adj_isBridge.mp hH ((sum_adj_inr).mp h))
      (sum_left_reachable (hr.map Iso.sumComm.toHom))

private theorem acyclic_of_sides {A B : Type} {K : SimpleGraph (A ⊕ B)}
    (hl : (K.comap Sum.inl).IsAcyclic) (hr : (K.comap Sum.inr).IsAcyclic)
    (hu : ∀ x y x' y', K.Adj (.inl x) (.inr y) → K.Adj (.inl x') (.inr y') →
      x = x' ∧ y = y') :
    K.IsAcyclic := by
  classical
  let L := (K.comap Sum.inl) ⊕g (K.comap Sum.inr)
  have hL : L.IsAcyclic := acyclic_sum hl hr
  by_cases hc : ∃ x y, K.Adj (.inl x) (.inr y)
  · obtain ⟨a, b, hab⟩ := hc
    have cross (x : A) (y : B) :
        K.Adj (.inl x) (.inr y) ↔
          (joinAt (K.comap Sum.inl) (K.comap Sum.inr) a b).Adj (.inl x) (.inr y) := by
      rw [joinAt_cross]
      exact ⟨fun h => hu x y a b h hab, by rintro ⟨rfl, rfl⟩; exact hab⟩
    have hK : K = joinAt (K.comap Sum.inl) (K.comap Sum.inr) a b := by
      ext (x | x) (y | y)
      · exact (joinAt_inl (K.comap Sum.inl) (K.comap Sum.inr) a b x y).symm
      · exact cross x y
      · exact (K.adj_comm _ _).trans ((cross y x).trans ((joinAt _ _ a b).adj_comm _ _))
      · exact (joinAt_inr (K.comap Sum.inl) (K.comap Sum.inr) a b x y).symm
    rw [hK]
    exact hL.sup_edge_of_not_reachable (not_reachable_sum_inl_inr a b)
  · have hK : K = L := by
      ext (x | x) (y | y)
      · rfl
      · exact ⟨fun h => (hc ⟨x, y, h⟩).elim, fun h => (not_adj_sum_inl_inr _ _ h).elim⟩
      · exact ⟨fun h => (hc ⟨y, x, h.symm⟩).elim,
          fun h => (not_adj_sum_inl_inr _ _ h.symm).elim⟩
      · rfl
    exact hK.symm ▸ hL

private theorem joinAt_induce_isAcyclic {A B : Type} {G : SimpleGraph A} {H : SimpleGraph B}
    (a : A) (b : B) (S : Set (A ⊕ B))
    (hl : (G.induce (leftSet S)).IsAcyclic) (hr : (H.induce (rightSet S)).IsAcyclic) :
    ((joinAt G H a b).induce S).IsAcyclic := by
  rw [← (splitIso (joinAt G H a b) S).isAcyclic_iff]
  apply acyclic_of_sides
  · rwa [splitGraph_inl]
  · rwa [splitGraph_inr]
  · intro x y x' y' hxy hxy'
    obtain ⟨hx, hy⟩ := (splitGraph_cross G H a b S x y).mp hxy
    obtain ⟨hx', hy'⟩ := (splitGraph_cross G H a b S x' y').mp hxy'
    exact ⟨Subtype.ext (hx.trans hx'.symm), Subtype.ext (hy.trans hy'.symm)⟩

private theorem joinAt_mono {A B : Type} {G K : SimpleGraph A} {H L : SimpleGraph B}
    (hG : G ≤ K) (hH : H ≤ L) (a : A) (b : B) : joinAt G H a b ≤ joinAt K L a b := by
  apply sup_le_sup_right
  rintro (x | x) (y | y) h
  · exact hG h
  · exact h
  · exact h
  · exact hH h

private theorem joinAt_keeps_preconnected {A B : Type}
    {G K : SimpleGraph A} {H L : SimpleGraph B}
    (a : A) (b : B) (S : Set (A ⊕ B))
    (h : ((joinAt G H a b).induce S).Preconnected)
    (hl : (G.induce (leftSet S)).Preconnected → (K.induce (leftSet S)).Preconnected)
    (hr : (H.induce (rightSet S)).Preconnected → (L.induce (rightSet S)).Preconnected) :
    ((joinAt K L a b).induce S).Preconnected := by
  intro x y
  have hconn : ((joinAt G H a b).induce S).Connected :=
    induced_connected_of_preconnected h ⟨x.val, x.property⟩
  obtain ⟨hne, hgl, hgr, hb⟩ := (joinAt_induce_connected a b S).mp hconn
  exact ((joinAt_induce_connected a b S).mpr ⟨hne, hl hgl, hr hgr, hb⟩) x y

private theorem cycle_isCycles (m : ℕ) : (cycleGraph (m + 3)).IsCycles := by
  intro x _
  rw [ncard_neighborSet]
  exact cycleGraph_degree_three_le

private theorem cycle_walk_edges {m : ℕ} {x : Fin (m + 3)}
    {p : (cycleGraph (m + 3)).Walk x x} (hp : p.IsCycle) :
    ∀ e ∈ (cycleGraph (m + 3)).edgeSet, e ∈ p.edges := by
  obtain ⟨c, hc⟩ := p.toSubgraph_connected.exists_verts_eq_connectedComponentSupp
    (fun _ hu _ huv => (hp.adj_toSubgraph_iff_of_isCycles (cycle_isCycles m) hu _).mpr huv)
  have hv (v : Fin (m + 3)) : v ∈ p.toSubgraph.verts := by
    rw [hc]
    obtain ⟨w, rfl⟩ := c.exists_rep
    exact (ConnectedComponent.mem_supp_iff _ _).mpr
      (ConnectedComponent.sound (preconnected_cycleGraph v w))
  intro e
  induction e using Sym2.inductionOn with
  | hf u v =>
    intro he
    have hadj := (hp.adj_toSubgraph_iff_of_isCycles (cycle_isCycles m) (hv u) v).mpr he
    exact Walk.adj_toSubgraph_iff_mem_edges.mp hadj

private theorem cycle_delete_tree {m : ℕ} (e : (cycleGraph (m + 3)).edgeSet) :
    ((cycleGraph (m + 3)).deleteEdges {e.val}).IsTree := by
  constructor
  · apply preconnected_cycleGraph.connected_deleteEdges_of_not_isBridge
    intro hb
    exact ((isBridge_iff_forall_cycle_notMem e.property).mp hb
      (cycleGraph.cycle m) cycleGraph.isCycle_cycle)
        (cycle_walk_edges cycleGraph.isCycle_cycle e.val e.property)
  · intro x p hp
    let f : (cycleGraph (m + 3)).deleteEdges {e.val} →g cycleGraph (m + 3) :=
      Hom.ofLE (deleteEdges_le _)
    let p' := p.map f
    have hp' : p'.IsCycle := hp.map (f := f) Function.injective_id
    have he : e.val ∈ p'.edges := cycle_walk_edges hp' e.val e.property
    have hpE : e.val ∈ p.edges := by
      simpa [p', f, Walk.edges_map, Hom.coe_ofLE] using he
    have hm := p.edges_subset_edgeSet hpE
    rw [edgeSet_deleteEdges] at hm
    exact hm.2 rfl

private theorem cycle_induce_proper_acyclic {m : ℕ} {S : Set (Fin (m + 3))}
    (h : S ≠ Set.univ) : ((cycleGraph (m + 3)).induce S).IsAcyclic := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, v ∉ S := by simpa [Set.eq_univ_iff_forall] using h
  have adj : (cycleGraph (m + 3)).Adj (v + 1) v :=
    cycleGraph_adj.mpr (.inl (by abel))
  let e : (cycleGraph (m + 3)).edgeSet := ⟨s(v + 1, v), adj⟩
  have hle : (cycleGraph (m + 3)).induce S ≤ ((cycleGraph (m + 3)).deleteEdges {e.val}).induce S := by
    intro x y hxy
    show ((cycleGraph (m + 3)).deleteEdges {e.val}).Adj x.val y.val
    rw [deleteEdges_adj]
    refine ⟨hxy, ?_⟩
    intro he
    rcases Sym2.eq_iff.mp he with he | he
    · exact hv (he.2 ▸ y.2)
    · exact hv (he.1 ▸ x.2)
  exact ((cycle_delete_tree e).isAcyclic.induce S).anti hle

end TreeFoundation
section TreeChoices

open scoped Sym2

/-- The choice is one actual edge precisely when the complete cycle block is present. -/
abbrev CycleChoice {V : Type} (G : SimpleGraph V) (S : Set V) :=
  {e : Option G.edgeSet // e ≠ none ↔ S = Set.univ}

private def pruneCycle {V : Type} (G : SimpleGraph V) : Option G.edgeSet → SimpleGraph V
  | none => G
  | some e => G.deleteEdges {e.val}

private theorem pruneCycle_le {V : Type} (G : SimpleGraph V) (e : Option G.edgeSet) :
    pruneCycle G e ≤ G := by cases e <;> first | exact le_rfl | exact deleteEdges_le _

private theorem pruneCycle_preconnected {m : ℕ} {S : Set (Fin (m + 3))}
    (e : CycleChoice (cycleGraph (m + 3)) S)
    (h : ((cycleGraph (m + 3)).induce S).Preconnected) :
    ((pruneCycle (cycleGraph (m + 3)) e.val).induce S).Preconnected := by
  obtain ⟨_ | f, hf⟩ := e
  · exact h
  · have he := hf.mp (by simp)
    subst S
    exact ((induceUnivIso _).connected_iff.mpr (cycle_delete_tree f).connected).preconnected

private theorem pruneCycle_acyclic {m : ℕ} {S : Set (Fin (m + 3))}
    (e : CycleChoice (cycleGraph (m + 3)) S) :
    ((pruneCycle (cycleGraph (m + 3)) e.val).induce S).IsAcyclic := by
  obtain ⟨_ | f, hf⟩ := e
  · exact cycle_induce_proper_acyclic (fun h => hf.mpr h rfl)
  · exact (cycle_delete_tree f).isAcyclic.induce S

private theorem pruneCycle_choice_inj {V : Type} {G : SimpleGraph V} {S : Set V}
    {a b : CycleChoice G S}
    (h : ∀ x ∈ S, ∀ y ∈ S, (pruneCycle G a.val).Adj x y ↔ (pruneCycle G b.val).Adj x y) :
    a = b := by
  obtain ⟨a | a, ha⟩ := a <;> obtain ⟨b | b, hb⟩ := b
  · rfl
  · exact ((ha.mpr (hb.mp (by simp))) rfl).elim
  · exact ((hb.mpr (ha.mp (by simp))) rfl).elim
  · have hs := ha.mp (by simp)
    have heq : G.deleteEdges {a.val} = G.deleteEdges {b.val} := by
      ext x y
      exact h x (hs.symm ▸ Set.mem_univ _) y (hs.symm ▸ Set.mem_univ _)
    have hn : a.val ∉ (G.deleteEdges {a.val}).edgeSet := by
      rw [edgeSet_deleteEdges]; simp
    rw [heq, edgeSet_deleteEdges] at hn
    have hab : a.val = b.val := by simpa [a.property] using hn
    cases Subtype.ext hab
    rfl

/-- Independent choices of one core edge and one triangle edge when their blocks are full. -/
abbrev DeletionChoices (c : Configuration) :=
  CycleChoice (cycleGraph 5000) (coreSet c.vertices) ×
    CycleChoice (cycleGraph 3) (triangleSet c.vertices)

/-- Actual tree subgraphs with the specified support, retaining their actual host edges. -/
abbrev TreeFiber (S : Set Vertex) := {H : G500.Subgraph // H.coe.IsTree ∧ H.verts = S}

private def prunedHost {S : Set Vertex}
    (e : CycleChoice (cycleGraph 5000) (coreSet S))
    (f : CycleChoice (cycleGraph 3) (triangleSet S)) : SimpleGraph Vertex :=
  joinAt
    (joinAt (joinAt (pruneCycle (cycleGraph 5000) e.val) (pathGraph 500) 0 0)
      (pathGraph 500) (.inl 1000) 0)
    (pruneCycle (cycleGraph 3) f.val) (.inl (.inl 500)) 0

private theorem prunedHost_le {S : Set Vertex} (e : CycleChoice _ (coreSet S))
    (f : CycleChoice _ (triangleSet S)) : prunedHost e f ≤ G500 :=
  joinAt_mono
    (joinAt_mono (joinAt_mono (pruneCycle_le _ _) le_rfl _ _) le_rfl _ _)
    (pruneCycle_le _ _) _ _

private theorem prunedHost_tree {S : Set Vertex} (hS : (G500.induce S).Connected)
    (e : CycleChoice (cycleGraph 5000) (coreSet S))
    (f : CycleChoice (cycleGraph 3) (triangleSet S)) :
    ((prunedHost e f).induce S).IsTree := by
  unfold prunedHost
  unfold G500 at hS
  constructor
  · refine @SimpleGraph.Connected.mk _ _ ?_ hS.nonempty
    apply joinAt_keeps_preconnected (.inl (.inl 500)) 0 S hS.preconnected
    · intro hl
      apply joinAt_keeps_preconnected (Sum.inl (1000 : Fin 5000)) (0 : Fin 500) (leftSet S) hl _ id
      intro hl'
      exact joinAt_keeps_preconnected 0 0 _ hl' (pruneCycle_preconnected (m := 4997) e) id
    · exact pruneCycle_preconnected (m := 0) f
  · apply joinAt_induce_isAcyclic
    · apply joinAt_induce_isAcyclic
      · exact joinAt_induce_isAcyclic 0 0 _ (pruneCycle_acyclic (m := 4997) e)
          ((isAcyclic_pathGraph 500).induce _)
      · exact (isAcyclic_pathGraph 500).induce _
    · exact pruneCycle_acyclic (m := 0) f

private def supportedSubgraph {V : Type} {G L : SimpleGraph V} (hL : L ≤ G) (S : Set V) :
    G.Subgraph where
  verts := S
  Adj x y := L.Adj x y ∧ x ∈ S ∧ y ∈ S
  adj_sub h := hL h.1
  edge_vert h := h.2.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩

private def supportedIso {V : Type} {G L : SimpleGraph V} (hL : L ≤ G) (S : Set V) :
    (supportedSubgraph hL S).coe ≃g L.induce S where
  toEquiv := Equiv.refl S
  map_rel_iff' {x y} := ⟨fun h => ⟨h, x.2, y.2⟩, fun h => h.1⟩

private def decodeTree {S : Set Vertex} (hS : (G500.induce S).Connected)
    (e : CycleChoice (cycleGraph 5000) (coreSet S))
    (f : CycleChoice (cycleGraph 3) (triangleSet S)) : TreeFiber S :=
  ⟨supportedSubgraph (prunedHost_le e f) S,
    (supportedIso (prunedHost_le e f) S).isTree_iff.mpr (prunedHost_tree hS e f), rfl⟩

private theorem prunedHost_core_adj {S : Set Vertex} (e : CycleChoice _ (coreSet S))
    (f : CycleChoice _ (triangleSet S)) (x y : Fin 5000) :
    (prunedHost e f).Adj (core x) (core y) ↔ (pruneCycle (cycleGraph 5000) e.val).Adj x y := by
  simp only [prunedHost, joinAt_inl]

private theorem prunedHost_triangle_adj {S : Set Vertex} (e : CycleChoice _ (coreSet S))
    (f : CycleChoice _ (triangleSet S)) (x y : Fin 3) :
    (prunedHost e f).Adj (triangle x) (triangle y) ↔
      (pruneCycle (cycleGraph 3) f.val).Adj x y := by
  simp only [prunedHost, joinAt_inr]

private theorem decodeTree_inj {S : Set Vertex} (hS : (G500.induce S).Connected)
    (a b : CycleChoice (cycleGraph 5000) (coreSet S) × CycleChoice (cycleGraph 3) (triangleSet S))
    (h : decodeTree hS a.1 a.2 = decodeTree hS b.1 b.2) : a = b := by
  have h_adj {x y : Vertex} (hx : x ∈ S) (hy : y ∈ S) :
      (prunedHost a.1 a.2).Adj x y ↔ (prunedHost b.1 b.2).Adj x y := by
    have he := congrArg (fun H : TreeFiber S => H.val.Adj x y) h
    exact ⟨fun hxy => (he ▸ ⟨hxy, hx, hy⟩ :
      (decodeTree hS b.1 b.2).val.Adj x y).1,
      fun hxy => (he.symm ▸ ⟨hxy, hx, hy⟩ :
        (decodeTree hS a.1 a.2).val.Adj x y).1⟩
  apply Prod.ext
  · apply pruneCycle_choice_inj
    intro x hx y hy
    exact (prunedHost_core_adj a.1 a.2 x y).symm.trans
      ((h_adj hx hy).trans (prunedHost_core_adj b.1 b.2 x y))
  · apply pruneCycle_choice_inj
    intro x hx y hy
    exact (prunedHost_triangle_adj a.1 a.2 x y).symm.trans
      ((h_adj hx hy).trans (prunedHost_triangle_adj b.1 b.2 x y))

private theorem exists_cycle_choice {V : Type} {G : SimpleGraph V} {H : G.Subgraph}
    (hH : H.coe.IsAcyclic) {m : ℕ} (f : Fin (m + 3) ↪ V) (hS : Set (Fin (m + 3)))
    (hs : hS = f ⁻¹' H.verts)
    (hsub : H.spanningCoe.comap f ≤ cycleGraph (m + 3)) :
    ∃ e : CycleChoice (cycleGraph (m + 3)) hS, H.spanningCoe.comap f ≤ pruneCycle _ e.val := by
  classical
  by_cases hfull : hS = Set.univ
  · have mem (x : Fin (m + 3)) : f x ∈ H.verts := by
      change x ∈ f ⁻¹' H.verts
      rw [← hs, hfull]
      exact Set.mem_univ x
    have nle : ¬cycleGraph (m + 3) ≤ H.spanningCoe.comap f := by
      intro h
      let g : cycleGraph (m + 3) →g H.coe :=
        ⟨fun x => ⟨f x, mem x⟩, fun hadj => h hadj⟩
      have ha : (cycleGraph (m + 3)).IsAcyclic :=
        hH.comap g (fun _ _ he => f.injective (congrArg Subtype.val he))
      exact ha (cycleGraph.cycle m) cycleGraph.isCycle_cycle
    rw [← edgeSet_subset_edgeSet] at nle
    obtain ⟨e, he, hne⟩ := Set.not_subset.mp nle
    refine ⟨⟨some ⟨e, he⟩, by simp [hfull]⟩, ?_⟩
    intro x y hxy
    show ((cycleGraph (m + 3)).deleteEdges {e}).Adj x y
    rw [deleteEdges_adj]
    refine ⟨hsub hxy, ?_⟩
    intro h
    exact hne (Set.mem_singleton_iff.mp h ▸ hxy)
  · exact ⟨⟨none, by simp [hfull]⟩, hsub⟩

private theorem subgraph_eq_of_connected_le_tree {V : Type} {G : SimpleGraph V}
    {H K : G.Subgraph} (hc : H.coe.Connected) (ht : K.coe.IsTree)
    (hv : H.verts = K.verts) (he : ∀ ⦃x y⦄, H.Adj x y → K.Adj x y) : H = K := by
  let F : SimpleGraph K.verts := H.spanningCoe.induce K.verts
  let iso : H.coe ≃g F := ⟨Set.equivOfEq hv, Iff.rfl⟩
  have hle : F ≤ K.coe := fun _ _ h => he h
  have hge := (isTree_iff_minimal_connected.mp ht).2 (iso.connected_iff.mp hc) hle
  apply Subgraph.ext hv
  funext x y
  apply propext
  refine ⟨fun h => he h, fun hxy => ?_⟩
  exact @hge ⟨x, K.edge_vert hxy⟩ ⟨y, K.edge_vert hxy.symm⟩ hxy

private theorem decodeTree_surj {S : Set Vertex} (hS : (G500.induce S).Connected)
    (H : TreeFiber S) :
    ∃ (a : CycleChoice (cycleGraph 5000) (coreSet S) × CycleChoice (cycleGraph 3) (triangleSet S)),
      decodeTree hS a.1 a.2 = H := by
  let ec : Fin 5000 ↪ Vertex :=
    ⟨core, fun _ _ h => Sum.inl.inj (Sum.inl.inj (Sum.inl.inj h))⟩
  let et : Fin 3 ↪ Vertex := ⟨triangle, Sum.inr_injective⟩
  have sub₀ : H.val.spanningCoe.comap ec ≤ cycleGraph 5000 := by
    intro x y h
    have hadj : G500.Adj (core x) (core y) := H.val.adj_sub h
    simpa only [G500, joinAt_inl] using hadj
  have sub₁ : H.val.spanningCoe.comap et ≤ cycleGraph 3 := by
    intro x y h
    have hadj : G500.Adj (triangle x) (triangle y) := H.val.adj_sub h
    simpa only [G500, joinAt_inr] using hadj
  obtain ⟨a, ha⟩ := exists_cycle_choice H.property.1.isAcyclic ec (coreSet S)
    (congrArg coreSet H.property.2.symm) sub₀
  obtain ⟨b, hb⟩ := exists_cycle_choice H.property.1.isAcyclic et (triangleSet S)
    (congrArg triangleSet H.property.2.symm) sub₁
  refine ⟨(a, b), Subtype.ext ?_⟩
  apply Eq.symm
  apply subgraph_eq_of_connected_le_tree H.property.1.connected (decodeTree hS a b).property.1
    H.property.2
  intro x y hxy
  refine ⟨?_, H.property.2 ▸ H.val.edge_vert hxy, H.property.2 ▸ H.val.edge_vert hxy.symm⟩
  have h : G500.Adj x y := H.val.adj_sub hxy
  rcases x with ((x | x) | x) | x <;> rcases y with ((y | y) | y) | y
  all_goals simp only [prunedHost, G500, joinAt_inl, joinAt_inr, joinAt_cross] at h ⊢
  all_goals try exact h
  all_goals try exact ha hxy
  all_goals try exact hb hxy

/-- Spanning trees on each actual support are precisely the independent cycle-edge deletions. -/
noncomputable def treeFiberEquiv (c : Configuration) :
    TreeFiber (supportEquiv.symm c).val ≃ DeletionChoices c :=
  (Equiv.ofBijective (fun a : DeletionChoices c => decodeTree c.supportConnected a.1 a.2)
    ⟨fun _ _ h => decodeTree_inj c.supportConnected _ _ h, decodeTree_surj c.supportConnected⟩).symm

/-- The decoded tree keeps exactly the pruned host's edges with both endpoints in the support. -/
theorem treeFiberEquiv_edges (c : Configuration) (e : DeletionChoices c) (x y : Vertex) :
    ((treeFiberEquiv c).symm e).val.Adj x y ↔
      (prunedHost e.1 e.2).Adj x y ∧ x ∈ c.vertices ∧ y ∈ c.vertices :=
  Iff.rfl

/-- Every decoded tree has the vertex order of its support configuration. -/
theorem treeFiberEquiv_order (c : Configuration) (e : DeletionChoices c) :
    Nat.card ((treeFiberEquiv c).symm e).val.verts = c.vertexOrder := by
  rw [((treeFiberEquiv c).symm e).property.2, supportEquiv_order]

private theorem cycle_edge_card (m : ℕ) : Nat.card (cycleGraph (m + 3)).edgeSet = m + 3 := by
  let e : (cycleGraph (m + 3)).edgeSet :=
    ⟨s(1, 0), cycleGraph_adj.mpr (.inl (sub_zero _))⟩
  have h := (isTree_iff_connected_and_card.mp (cycle_delete_tree e)).2
  rw [edgeSet_deleteEdges, Nat.card_fin] at h
  exact (Set.ncard_sdiff_singleton_add_one e.property).symm.trans h

/-- With all the vertices present, the deletion choices are the actual edges of that cycle. -/
def fullCycleChoiceEquiv {V : Type} (G : SimpleGraph V) :
    CycleChoice G Set.univ ≃ G.edgeSet where
  toFun e := e.val.get (Option.ne_none_iff_isSome.mp (e.property.mpr rfl))
  invFun e := ⟨some e, by simp⟩
  left_inv := by
    rintro ⟨_ | e, h⟩
    · exact (h.mpr rfl rfl).elim
    · rfl
  right_inv _ := rfl

/-- With a vertex absent, there is exactly one choice, which deletes no edge. -/
def properCycleChoiceEquiv {V : Type} (G : SimpleGraph V) {S : Set V} (h : S ≠ Set.univ) :
    CycleChoice G S ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨none, by simp [h]⟩
  left_inv := by
    rintro ⟨_ | e, he⟩
    · rfl
    · exact (h (he.mp (by simp))).elim
  right_inv _ := rfl

theorem deletionChoices_card (c : Configuration) :
    Nat.card (DeletionChoices c) =
      (if coreSet c.vertices = Set.univ then 5000 else 1) *
      (if triangleSet c.vertices = Set.univ then 3 else 1) := by
  classical
  have card_choice {m : ℕ} (S : Set (Fin (m + 3))) :
      Nat.card (CycleChoice (cycleGraph (m + 3)) S) = if S = Set.univ then m + 3 else 1 := by
    by_cases h : S = Set.univ
    · subst S
      rw [ite_eq_left rfl, Nat.card_congr (fullCycleChoiceEquiv _), cycle_edge_card]
    · rw [ite_eq_right h, Nat.card_congr (properCycleChoiceEquiv _ h), Nat.card_unique]
  unfold DeletionChoices
  rw [Nat.card_prod]
  exact (congrArg₂ (· * ·)
    (card_choice (m := 4997) _) (card_choice (m := 0) _))

private def mappedDeletion {A B : Type} (f : A → B) {G : SimpleGraph A}
    (e : Option G.edgeSet) : Set (Sym2 B) :=
  match e with
  | none => ∅
  | some v => {Sym2.map f v.val}

/-- The selected edges as actual unordered pairs of host vertices. -/
def DeletionChoices.deletedEdges {c : Configuration} (e : DeletionChoices c) : Set (Sym2 Vertex) :=
  mappedDeletion core e.1.val ∪ mappedDeletion triangle e.2.val

private theorem joinAt_cross_reverse {A B : Type} (G : SimpleGraph A) (H : SimpleGraph B)
    (a : A) (b : B) (x : A) (y : B) :
    (joinAt G H a b).Adj (.inr y) (.inl x) ↔ x = a ∧ y = b :=
  ((joinAt G H a b).adj_comm _ _).trans (joinAt_cross G H a b x y)

private theorem prunedHost_deleteEdges (c : Configuration) (e : DeletionChoices c) :
    prunedHost e.1 e.2 = G500.deleteEdges e.deletedEdges := by
  obtain ⟨⟨_ | ⟨a, ha⟩, hp⟩, ⟨_ | ⟨b, hb⟩, hq⟩⟩ := e
  · ext x y
    simp [prunedHost, G500, DeletionChoices.deletedEdges, mappedDeletion, pruneCycle]
  · induction b using Sym2.inductionOn with
    | hf u v =>
      ext (((x | x) | x) | x) (((y | y) | y) | y) <;>
        simp [prunedHost, G500, DeletionChoices.deletedEdges, mappedDeletion,
          pruneCycle, joinAt_inl, joinAt_inr, joinAt_cross, joinAt_cross_reverse]
  · induction a using Sym2.inductionOn with
    | hf u v =>
      ext (((x | x) | x) | x) (((y | y) | y) | y) <;>
        simp [prunedHost, G500, DeletionChoices.deletedEdges, mappedDeletion,
          pruneCycle, joinAt_inl, joinAt_inr, joinAt_cross, joinAt_cross_reverse]
  · induction a using Sym2.inductionOn with
    | hf a₁ a₂ =>
      induction b using Sym2.inductionOn with
      | hf b₁ b₂ =>
        ext (((x | x) | x) | x) (((y | y) | y) | y) <;>
          simp [prunedHost, G500, DeletionChoices.deletedEdges, mappedDeletion,
            pruneCycle, joinAt_inl, joinAt_inr, joinAt_cross, joinAt_cross_reverse]

/-- Fixing the support and the chosen actual edges forces every other induced edge. -/
theorem treeFiberEquiv_keeps_edge_iff (c : Configuration) (e : DeletionChoices c) (x y : Vertex) :
    ((treeFiberEquiv c).symm e).val.Adj x y ↔
      G500.Adj x y ∧ x ∈ c.vertices ∧ y ∈ c.vertices ∧ s(x, y) ∉ e.deletedEdges := by
  rw [treeFiberEquiv_edges, prunedHost_deleteEdges, deleteEdges_adj]
  constructor
  · rintro ⟨⟨h, hd⟩, hx, hy⟩
    exact ⟨h, hx, hy, hd⟩
  · rintro ⟨h, hx, hy, hd⟩
    exact ⟨⟨h, hd⟩, hx, hy⟩

#print axioms treeFiberEquiv
#print axioms treeFiberEquiv_edges
#print axioms treeFiberEquiv_order
#print axioms treeFiberEquiv_keeps_edge_iff
#print axioms deletionChoices_card

end TreeChoices

end D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement
