/- GID: D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Replacing the retained components preserves the ambient tree and transports component peaks to rooted leaves. -/

import D5.S3.Combinatorics.Graph.CayleyColoring.RootedCoordinates
import D5.S3.Combinatorics.Graph.CayleyColoring.CentralScheduler

section

namespace CayleyForest

open SimpleGraph

universe u
variable {V : Type u}

abbrev Sample (V : Type u) := {s : CayleyProbe.Tree V × SimpleGraph V // s.2 ≤ s.1.val}

def parts (H : SimpleGraph V) : Set (Set V) :=
  Set.range (fun c : H.ConnectedComponent => c.supp)

theorem mem_parts (H : SimpleGraph V) (v : V) : (H.connectedComponentMk v).supp ∈ parts H :=
  ⟨H.connectedComponentMk v, rfl⟩

theorem mem_own_part (H : SimpleGraph V) (v : V) : v ∈ (H.connectedComponentMk v).supp :=
  (ConnectedComponent.mem_supp_iff _ _).mpr rfl

theorem part_eq {H : SimpleGraph V} {s t : Set V} (hs : s ∈ parts H)
    (ht : t ∈ parts H) {v : V} (hvs : v ∈ s) (hvt : v ∈ t) : s = t := by
  obtain ⟨a, rfl⟩ := hs
  obtain ⟨b, rfl⟩ := ht
  rw [ConnectedComponent.eq_of_common_vertex hvs hvt]

theorem nonempty_part {H : SimpleGraph V} {s : Set V} (hs : s ∈ parts H) :
    s.Nonempty := by
  obtain ⟨a, rfl⟩ := hs
  exact a.nonempty_supp

theorem reachable_part {H : SimpleGraph V} {s : Set V} (hs : s ∈ parts H)
    {x y : V} (hx : x ∈ s) (hy : y ∈ s) : H.Reachable x y := by
  obtain ⟨a, rfl⟩ := hs
  exact a.reachable_of_mem_supp hx hy

theorem mem_part_of_reachable {H : SimpleGraph V} {s : Set V} (hs : s ∈ parts H)
    {x y : V} (hx : x ∈ s) (hr : H.Reachable x y) : y ∈ s := by
  obtain ⟨a, rfl⟩ := hs
  rw [ConnectedComponent.mem_supp_iff] at hx ⊢
  exact (ConnectedComponent.sound hr).symm.trans hx

def localTree (T : CayleyProbe.Tree V) {H : SimpleGraph V} (h : H ≤ T.val)
    (s : Set V) (hs : s ∈ parts H) : CayleyProbe.Tree s := by
  refine ⟨H.induce s, ?_⟩
  obtain ⟨a, rfl⟩ := hs
  exact (T.prop.isAcyclic.anti h).isTree_connectedComponent a

/-- A tree edge with endpoints in a retained component is itself retained. -/
theorem adj_of_reachable {T : CayleyProbe.Tree V} {H : SimpleGraph V} (h : H ≤ T.val)
    {x y : V} (ha : T.val.Adj x y) (hr : H.Reachable x y) : H.Adj x y := by
  by_contra nh
  have hbridge := isAcyclic_iff_forall_adj_isBridge.mp T.prop.isAcyclic ha
  apply isBridge_iff.mp hbridge
  have hsub : H ≤ T.val.deleteEdges {s(x,y)} := by
    intro a b hab
    refine deleteEdges_adj.mpr ⟨h hab, fun hm => ?_⟩
    rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp hm) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact nh hab
    · exact nh hab.symm
  exact hr.mono hsub

abbrev Family (P : Set (Set V)) := ∀ s : P, CayleyProbe.Tree s.val

def block {P : Set (Set V)} (U : Family P) (s : P) : SimpleGraph V :=
  (U s).val.map (Function.Embedding.subtype (· ∈ s.val))

def unionGraph {P : Set (Set V)} (U : Family P) : SimpleGraph V :=
  ⨆ s, block U s

theorem block_adj {P : Set (Set V)} {U : Family P} {s : P} {x y : V} :
    (block U s).Adj x y ↔
      ∃ (hx : x ∈ s.val) (hy : y ∈ s.val), (U s).val.Adj ⟨x,hx⟩ ⟨y,hy⟩ := by
  rw [block, SimpleGraph.map_adj]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b,hb⟩, hab, rfl, rfl⟩
    exact ⟨ha, hb, hab⟩
  · rintro ⟨hx, hy, ha⟩
    exact ⟨⟨x,hx⟩, ⟨y,hy⟩, ha, rfl, rfl⟩

theorem local_adj {H : SimpleGraph V} (U : Family (parts H)) (s : parts H)
    (x y : s.val) : (unionGraph U).Adj x.val y.val ↔ (U s).val.Adj x y := by
  rw [unionGraph, iSup_adj]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨hx, hy, h⟩ := block_adj.mp ht
    have ht' : t = s := Subtype.ext (part_eq t.prop s.prop hx x.prop)
    subst t
    exact h
  · intro h
    exact ⟨s, block_adj.mpr ⟨x.prop,y.prop,h⟩⟩

theorem local_reachable {P : Set (Set V)} (U : Family P) (s : P)
    {x y : V} (hx : x ∈ s.val) (hy : y ∈ s.val) : (unionGraph U).Reachable x y := by
  let hmap : (U s).val →g unionGraph U :=
    ⟨Subtype.val, fun {a b} hab => iSup_adj.mpr ⟨s, block_adj.mpr ⟨a.prop,b.prop,hab⟩⟩⟩
  obtain ⟨p⟩ := (U s).prop.connected ⟨x,hx⟩ ⟨y,hy⟩
  change (unionGraph U).Reachable (hmap ⟨x,hx⟩) (hmap ⟨y,hy⟩)
  exact (p.map hmap).reachable

theorem adjacent_same_part {H : SimpleGraph V} (U : Family (parts H)) {x y : V}
    (ha : (unionGraph U).Adj x y) : H.Reachable x y := by
  obtain ⟨s, hs⟩ := iSup_adj.mp ha
  obtain ⟨hx, hy, _⟩ := block_adj.mp hs
  exact reachable_part s.prop hx hy

theorem reachable_replace {H : SimpleGraph V} (U : Family (parts H)) :
    (unionGraph U).Reachable = H.Reachable := by
  funext x y
  apply propext
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact Reachable.rfl
    | cons hab _ ih => exact (adjacent_same_part U hab).trans ih
  · intro hr
    exact local_reachable U ⟨_, mem_parts H x⟩ (mem_own_part H x)
      (mem_part_of_reachable (mem_parts H x) (mem_own_part H x) hr)

theorem parts_congr {H H' : SimpleGraph V} (h : H.Reachable = H'.Reachable) :
    parts H = parts H' := by
  have aux {A B : SimpleGraph V} (e : A.Reachable = B.Reachable) :
      parts A ⊆ parts B := by
    rintro s ⟨c, rfl⟩
    obtain ⟨v, rfl⟩ := c.exists_rep
    refine ⟨B.connectedComponentMk v, Set.ext fun w => ?_⟩
    change w ∈ (B.connectedComponentMk v).supp ↔ w ∈ (A.connectedComponentMk v).supp
    rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.mem_supp_iff,
      ConnectedComponent.eq, ConnectedComponent.eq]
    exact (congrFun (congrFun e w) v).symm.to_iff
  exact Set.Subset.antisymm (aux h) (aux h.symm)

theorem reconstruct_inside {T : CayleyProbe.Tree V} {H : SimpleGraph V} (h : H ≤ T.val) :
    unionGraph (fun s : parts H => localTree T h s.val s.prop) = H := by
  ext x y
  constructor
  · intro ha
    obtain ⟨s, hs⟩ := iSup_adj.mp ha
    obtain ⟨_, _, hh⟩ := block_adj.mp hs
    exact hh
  · intro ha
    exact iSup_adj.mpr ⟨⟨_, mem_parts H x⟩, block_adj.mpr
      ⟨mem_own_part H x, mem_part_of_reachable (mem_parts H x) (mem_own_part H x) ha.reachable, ha⟩⟩

theorem block_edge_disjoint {H : SimpleGraph V} (U : Family (parts H)) :
    Pairwise (fun s t : parts H => Disjoint (block U s).edgeSet (block U t).edgeSet) := by
  intro s t hst
  rw [Set.disjoint_left]
  intro e hs ht
  induction e using Sym2.inductionOn with
  | _ x y =>
    obtain ⟨hx, _, _⟩ := block_adj.mp ((block U s).mem_edgeSet.mp hs)
    obtain ⟨hx', _, _⟩ := block_adj.mp ((block U t).mem_edgeSet.mp ht)
    exact hst (Subtype.ext (part_eq s.prop t.prop hx hx'))

theorem block_card [Finite V] {P : Set (Set V)} (U : Family P) (s : P) :
    Nat.card (block U s).edgeSet + 1 = Nat.card s.val := by
  let e := (Function.Embedding.subtype (· ∈ s.val)).sym2Map
  have he : (block U s).edgeSet = e '' (U s).val.edgeSet := edgeSet_map _ _
  rw [he, ← Nat.card_congr (Equiv.Set.image e (U s).val.edgeSet e.injective)]
  exact (isTree_iff_connected_and_card.mp (U s).prop).2

theorem retained_card [Finite V] {H : SimpleGraph V} (U W : Family (parts H)) :
    Nat.card (unionGraph U).edgeSet = Nat.card (unionGraph W).edgeSet := by
  classical
  let : Fintype (parts H) := Fintype.ofFinite _
  rw [unionGraph, unionGraph, edgeSet_iSup, edgeSet_iSup,
    Nat.card_congr (Set.unionEqSigmaOfDisjoint (block_edge_disjoint U)),
    Nat.card_congr (Set.unionEqSigmaOfDisjoint (block_edge_disjoint W)),
    Nat.card_sigma, Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro s _
  exact Nat.add_right_cancel ((block_card U s).trans (block_card W s).symm)

theorem cross_disjoint {T : CayleyProbe.Tree V} {H : SimpleGraph V} (h : H ≤ T.val)
    (U : Family (parts H)) : Disjoint (T.val \ H).edgeSet (unionGraph U).edgeSet := by
  rw [Set.disjoint_left]
  intro e hc hu
  induction e using Sym2.inductionOn with
  | _ x y =>
    have ha := (T.val \ H).mem_edgeSet.mp hc
    exact ha.2 (adj_of_reachable h ha.1 (adjacent_same_part U ((unionGraph U).mem_edgeSet.mp hu)))

theorem replaced_connected {T : CayleyProbe.Tree V} {H : SimpleGraph V}
    (U : Family (parts H)) : ((T.val \ H) ⊔ unionGraph U).Connected := by
  classical
  have := T.prop.connected.nonempty
  refine ⟨fun x y => ?_⟩
  obtain ⟨p⟩ := T.prop.connected x y
  induction p with
  | nil => exact Reachable.rfl
  | @cons x y z ha p ih =>
    apply Reachable.trans _ ih
    by_cases he : H.Adj x y
    · exact (Reachable.mono le_sup_right) ((congrFun (congrFun (reachable_replace U) x) y).mpr he.reachable)
    · exact ((sup_adj (T.val \ H) (unionGraph U) x y).mpr (Or.inl ⟨ha, he⟩)).reachable

/-- Replace the retained trees while keeping every deleted edge at its original endpoints. -/
noncomputable def replace [Finite V] (S : Sample V) (U : Family (parts S.val.2)) : Sample V := by
  classical
  let T := S.val.1
  let H := S.val.2
  let C := T.val \ H
  let H' := unionGraph U
  have decomp : C ⊔ H = T.val := sdiff_sup_cancel S.prop
  have h₁ : Disjoint C.edgeSet H.edgeSet := by
    rw [show C = T.val \ H from rfl, edgeSet_sdiff]
    exact Set.disjoint_sdiff_left
  have h₂ : Disjoint C.edgeSet H'.edgeSet := cross_disjoint S.prop U
  have hH : Nat.card H'.edgeSet = Nat.card H.edgeSet := by
    change Nat.card (unionGraph U).edgeSet = Nat.card S.val.2.edgeSet
    conv_rhs => rw [← reconstruct_inside S.prop]
    exact retained_card U _
  have hcard : Nat.card (C ⊔ H').edgeSet = Nat.card T.val.edgeSet := by
    rw [edgeSet_sup, Nat.card_congr (Equiv.Set.union h₂), Nat.card_sum, hH, ← decomp,
      edgeSet_sup, Nat.card_congr (Equiv.Set.union h₁), Nat.card_sum]
  have ht : (C ⊔ H').IsTree := isTree_iff_connected_and_card.mpr
    ⟨replaced_connected U, hcard ▸ (isTree_iff_connected_and_card.mp T.prop).2⟩
  exact ⟨⟨⟨C ⊔ H', ht⟩, H'⟩, le_sup_right⟩

theorem replace_cross [Finite V] (S : Sample V) (U : Family (parts S.val.2)) :
    (replace S U).val.1.val \ (replace S U).val.2 = S.val.1.val \ S.val.2 := by
  ext x y
  change (((S.val.1.val \ S.val.2).Adj x y ∨ (unionGraph U).Adj x y) ∧
    ¬(unionGraph U).Adj x y) ↔ (S.val.1.val \ S.val.2).Adj x y
  have hd (h : (S.val.1.val \ S.val.2).Adj x y) (h' : (unionGraph U).Adj x y) : False :=
    Set.disjoint_left.mp (cross_disjoint S.prop U)
      ((S.val.1.val \ S.val.2).mem_edgeSet.mpr h) ((unionGraph U).mem_edgeSet.mpr h')
  exact ⟨fun h => h.1.resolve_right h.2, fun h => ⟨Or.inl h, fun h' => hd h h'⟩⟩

theorem replace_card [Finite V] (S : Sample V) (U : Family (parts S.val.2)) :
    Nat.card (replace S U).val.2.edgeSet = Nat.card S.val.2.edgeSet := by
  change Nat.card (unionGraph U).edgeSet = Nat.card S.val.2.edgeSet
  conv_rhs => rw [← reconstruct_inside S.prop]
  exact retained_card U _

theorem replace_reachable [Finite V] (S : Sample V) (U : Family (parts S.val.2)) :
    (replace S U).val.2.Reachable = S.val.2.Reachable :=
  reachable_replace U


end CayleyForest

end

section

namespace CayleyForest

open SimpleGraph

universe u
variable {V : Type u} [Finite V]

omit [Finite V] in
theorem dist_of_mem_support {G : SimpleGraph V} {r x z : V}
    (p : G.Walk r x) (hz : z ∈ p.support) : G.dist r z ≤ p.length := by
  classical
  exact (G.dist_le (p.takeUntil z hz)).trans (p.length_takeUntil_le_length hz)

omit [Finite V] in
theorem dist_lt_of_mem_dropLast {G : SimpleGraph V} {r x z : V}
    (p : G.Walk r x) (hp : p.IsPath) (hz : z ∈ p.support.dropLast) :
    G.dist r z < p.length := by
  classical
  have he : p.support.dropLast ++ [x] = p.support := by
    simpa only [p.getLast_support] using List.dropLast_append_getLast p.support_ne_nil
  have hne : z ≠ x := by
    intro e
    subst z
    have hd := hp.support_nodup
    rw [← he, List.nodup_append'] at hd
    exact hd.2.2 hz (by simp)
  have hm : z ∈ p.support := List.mem_of_mem_dropLast hz
  exact (G.dist_le (p.takeUntil z hm)).trans_lt (p.length_takeUntil_lt_length hm hne)

omit [Finite V] in
theorem length_of_path {G : SimpleGraph V} (ha : G.IsAcyclic) {v w : V}
    {p : G.Walk v w} (hp : p.IsPath) : p.length = G.dist v w := by
  obtain ⟨q, hq, hd⟩ := p.reachable.exists_path_of_dist
  have he : p = q := congrArg Subtype.val
    ((isAcyclic_iff_subsingleton_path.mp ha v w).elim ⟨p,hp⟩ ⟨q,hq⟩)
  exact he ▸ hd

/-- The component's closest vertex to the global root, with its original label. -/
noncomputable def entry (T : CayleyProbe.Tree V) (r : V) {H : SimpleGraph V}
    (s : Set V) (hs : s ∈ parts H) : s := by
  classical
  letI := Fintype.ofFinite s
  have hu : (Finset.univ : Finset s).Nonempty := by
    obtain ⟨v, hv⟩ := nonempty_part hs
    exact ⟨⟨v,hv⟩, Finset.mem_univ _⟩
  exact (Finset.exists_min_image Finset.univ (fun v : s => T.val.dist r v.val) hu).choose

theorem entry_min (T : CayleyProbe.Tree V) (r : V) {H : SimpleGraph V}
    (s : Set V) (hs : s ∈ parts H) (v : s) :
    T.val.dist r (entry T r s hs).val ≤ T.val.dist r v.val := by
  classical
  let : Fintype s := Fintype.ofFinite s
  unfold entry
  exact (Finset.exists_min_image (Finset.univ : Finset s)
    (fun v : s => T.val.dist r v.val) ⟨v,Finset.mem_univ v⟩).choose_spec.2 v (Finset.mem_univ _)

theorem entry_eq_of_root_mem (T : CayleyProbe.Tree V) (r : V) {H : SimpleGraph V}
    (s : Set V) (hs : s ∈ parts H) (hr : r ∈ s) : (entry T r s hs).val = r := by
  have h := entry_min T r s hs ⟨r,hr⟩
  change T.val.dist r (entry T r s hs).val ≤ T.val.dist r r at h
  rw [dist_self, Nat.le_zero] at h
  exact ((T.prop.connected.dist_eq_zero_iff).mp h).symm

/-- Within each retained component, global depth differs from local depth by a constant. -/
theorem local_depth (T : CayleyProbe.Tree V) (r : V) {H : SimpleGraph V} (h : H ≤ T.val)
    (s : Set V) (hs : s ∈ parts H) (x : s) :
    T.val.dist r x.val = T.val.dist r (entry T r s hs).val +
      (localTree T h s hs).val.dist (entry T r s hs) x := by
  classical
  let e := entry T r s hs
  let L := localTree T h s hs
  obtain ⟨p, hp, hd⟩ := T.prop.connected.exists_path_of_dist r e.val
  obtain ⟨q, hq, hqdist⟩ := L.prop.connected.exists_path_of_dist e x
  let f : L.val →g T.val := ⟨Subtype.val, fun ha => h ha⟩
  let w := q.map f
  have hw : w.IsPath := hq.map (f := f) Subtype.val_injective
  have hds : p.support.dropLast.Disjoint w.support := by
    intro a ha hb
    have hlt : T.val.dist r a < T.val.dist r e.val := hd ▸ dist_lt_of_mem_dropLast p hp ha
    change a ∈ (q.map f).support at hb
    rw [Walk.support_map, List.mem_map] at hb
    obtain ⟨z, _, rfl⟩ := hb
    exact (not_lt_of_ge (entry_min T r s hs z)) hlt
  have hpw : (p.append w).IsPath :=
    (Walk.isPath_append' p w).mpr ⟨hp.dropLast, hw, hds⟩
  have hlen := length_of_path T.prop.isAcyclic hpw
  rw [Walk.length_append, hd, show w.length = q.length from Walk.length_map _ _, hqdist] at hlen
  exact hlen.symm

omit [Finite V] in
theorem root_side_of_edge (T : CayleyProbe.Tree V) (r : V) {x y : V}
    (hxy : T.val.Adj x y) :
    (T.val.deleteEdges {s(x,y)}).Reachable r x ↔ T.val.dist r x < T.val.dist r y := by
  classical
  have aux {a b : V} (h : T.val.dist r a < T.val.dist r b) :
      (T.val.deleteEdges {s(a,b)}).Reachable r a := by
    obtain ⟨p, _, hd⟩ := T.prop.connected.exists_path_of_dist r a
    refine reachable_deleteEdges_iff_exists_walk.mpr ⟨p, fun hb => ?_⟩
    exact (not_le_of_gt h) (hd ▸ dist_of_mem_support p (p.snd_mem_support_of_mem_edges hb))
  refine ⟨fun hr => ?_, aux⟩
  by_contra hn
  have hlt : T.val.dist r y < T.val.dist r x :=
    lt_of_le_of_ne (not_lt.mp hn) (T.prop.dist_ne_of_adj r hxy).symm
  have hs : (T.val.deleteEdges {s(x,y)}).Reachable r y := by
    simpa only [Sym2.eq_swap] using (aux hlt)
  exact (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp T.prop.isAcyclic hxy))
    (hr.symm.trans hs)

omit [Finite V] in
theorem sup_reachable_congr (C : SimpleGraph V) {H H' : SimpleGraph V}
    (he : H.Reachable = H'.Reachable) :
    (C ⊔ H).Reachable = (C ⊔ H').Reachable := by
  have aux {A B : SimpleGraph V} (e : A.Reachable = B.Reachable) :
      (C ⊔ A).Reachable ≤ (C ⊔ B).Reachable := by
    rintro x y ⟨p⟩
    induction p with
    | nil => exact Reachable.rfl
    | @cons x y z ha _ ih =>
      apply Reachable.trans _ ih
      rcases (sup_adj C A x y).mp ha with hc | hh
      · exact Adj.reachable (G := C ⊔ B) (Or.inl hc)
      · exact (Reachable.mono le_sup_right) ((congrFun (congrFun e x) y).mp hh.reachable)
  exact le_antisymm (aux he) (aux he.symm)

/-- Across each deleted edge, replacing the retained components preserves the rootward direction. -/
theorem cross_orientation (S : Sample V) (U : Family (parts S.val.2)) (r : V) {x y : V}
    (hc : (S.val.1.val \ S.val.2).Adj x y) :
    (replace S U).val.1.val.dist r x < (replace S U).val.1.val.dist r y ↔
      S.val.1.val.dist r x < S.val.1.val.dist r y := by
  let C := S.val.1.val \ S.val.2
  let H := S.val.2
  let H' := unionGraph U
  have decomp : C ⊔ H = S.val.1.val := sdiff_sup_cancel S.prop
  have ha : (replace S U).val.1.val.Adj x y := Or.inl hc
  rw [← root_side_of_edge (replace S U).val.1 r ha,
    ← root_side_of_edge S.val.1 r hc.1]
  have d₁ : H.deleteEdges {s(x,y)} = H :=
    deleteEdges_eq_self.mpr (Set.disjoint_singleton_right.mpr hc.2)
  have d₂ : H'.deleteEdges {s(x,y)} = H' :=
    deleteEdges_eq_self.mpr (Set.disjoint_singleton_right.mpr
      (fun hh => Set.disjoint_left.mp (cross_disjoint S.prop U) hc hh))
  change ((C ⊔ H').deleteEdges {s(x,y)}).Reachable r x ↔
    (S.val.1.val.deleteEdges {s(x,y)}).Reachable r x
  rw [← decomp, deleteEdges_sup, deleteEdges_sup, d₁, d₂,
    sup_reachable_congr _ (reachable_replace U)]

/-- Any non-entry vertex in a retained component has a closer retained neighbor. -/
theorem internal_parent (T : CayleyProbe.Tree V) (r : V) {H : SimpleGraph V}
    (h : H ≤ T.val) (s : Set V) (hs : s ∈ parts H) (x : s)
    (hx : x ≠ entry T r s hs) :
    ∃ y : s, H.Adj x.val y.val ∧ T.val.dist r y.val < T.val.dist r x.val := by
  obtain ⟨y, hy, _⟩ := CayleyProbe.shorterNeighbor (localTree T h s hs).prop hx
  refine ⟨y, hy.1, ?_⟩
  rw [local_depth T r h s hs x, local_depth T r h s hs y]
  exact Nat.add_lt_add_left hy.2 _

theorem entry_replace (S : Sample V) (U : Family (parts S.val.2)) (r : V)
    (s : Set V) (hs : s ∈ parts S.val.2)
    (ht : s ∈ parts (replace S U).val.2) :
    entry (replace S U).val.1 r s ht = entry S.val.1 r s hs := by
  let e := entry S.val.1 r s hs
  by_cases hr : r ∈ s
  · exact Subtype.ext ((entry_eq_of_root_mem _ _ _ _ hr).trans (entry_eq_of_root_mem _ _ _ _ hr).symm)
  · have her : e.val ≠ r := fun he => hr (he ▸ e.prop)
    let p := CayleyColors.parent S.val.1 r ⟨e.val,her⟩
    have hp := CayleyColors.parent_spec S.val.1 r ⟨e.val,her⟩
    have hc : (S.val.1.val \ S.val.2).Adj p e.val := by
      refine ⟨hp.1.symm, fun he => ?_⟩
      have hm := mem_part_of_reachable hs e.prop he.symm.reachable
      exact (not_lt_of_ge (entry_min _ _ _ hs ⟨p,hm⟩)) hp.2
    have hn := (cross_orientation S U r hc).mpr hp.2
    by_contra he
    obtain ⟨y, hy, hdy⟩ := internal_parent (replace S U).val.1 r (replace S U).prop s ht e
      (Ne.symm he)
    have hy' := CayleyColors.parent_unique (replace S U).val.1 r ⟨e.val,her⟩
      ((replace S U).prop hy) hdy
    have hp' := CayleyColors.parent_unique (replace S U).val.1 r ⟨e.val,her⟩
      (show (replace S U).val.1.val.Adj e.val p from Or.inl hc.symm) hn
    have eq : y.val = p := hy'.trans hp'.symm
    have hmem := mem_part_of_reachable hs e.prop
      (show S.val.2.Reachable e.val y.val from adjacent_same_part U hy)
    exact (not_lt_of_ge (entry_min _ _ _ hs ⟨y.val,hmem⟩))
      (by simpa only [eq] using hp.2)

theorem local_after (S : Sample V) (U : Family (parts S.val.2)) (s : Set V)
    (hs : s ∈ parts S.val.2) (ht : s ∈ parts (replace S U).val.2) :
    localTree (replace S U).val.1 (replace S U).prop s ht = U ⟨s, hs⟩ := by
  apply Subtype.ext
  ext x y
  exact local_adj U ⟨s,hs⟩ x y

variable [LinearOrder V]

/-- Apply the fixed-entry peak-to-leaf map to each retained component. -/
noncomputable def transform (r : V) (S : Sample V) (backward : Bool) : Sample V :=
  replace S fun s =>
    let e := CayleyProbe.fixedRootEquiv (entry S.val.1 r s.val s.prop)
    (if backward then e.symm else e) (localTree S.val.1 S.prop s.val s.prop)

theorem transform_inverse (r : V) (S : Sample V) (b : Bool) :
    transform r (transform r S b) (!b) = S := by
  classical
  let U : Family (parts S.val.2) := fun s =>
    let e := CayleyProbe.fixedRootEquiv (entry S.val.1 r s.val s.prop)
    (if b then e.symm else e) (localTree S.val.1 S.prop s.val s.prop)
  let S' := replace S U
  let U' : Family (parts S'.val.2) := fun s =>
    let e := CayleyProbe.fixedRootEquiv (entry S'.val.1 r s.val s.prop)
    (if !b then e.symm else e) (localTree S'.val.1 S'.prop s.val s.prop)
  have hparts : parts S'.val.2 = parts S.val.2 := parts_congr (replace_reachable S U)
  have hloc (s : Set V) (h : s ∈ parts S'.val.2) (h' : s ∈ parts S.val.2) :
      U' ⟨s,h⟩ = localTree S.val.1 S.prop s h' := by
    change (if !b then (CayleyProbe.fixedRootEquiv (entry S'.val.1 r s h)).symm
      else CayleyProbe.fixedRootEquiv (entry S'.val.1 r s h))
        (localTree S'.val.1 S'.prop s h) = _
    rw [entry_replace S U r s h' h, local_after S U s h' h]
    cases b <;> simp [U]
  have hin : unionGraph U' = S.val.2 := by
    ext x y
    constructor
    · intro hab
      obtain ⟨s, hs⟩ := iSup_adj.mp hab
      obtain ⟨hx, hy, ha⟩ := block_adj.mp hs
      rw [hloc s.val s.prop (hparts ▸ s.prop)] at ha
      exact ha
    · intro hab
      let s := (S.val.2.connectedComponentMk x).supp
      have hs : s ∈ parts S.val.2 := mem_parts _ _
      have ht : s ∈ parts S'.val.2 := hparts.symm ▸ hs
      refine iSup_adj.mpr ⟨⟨s,ht⟩, block_adj.mpr ⟨mem_own_part _ _,
        mem_part_of_reachable hs (mem_own_part _ _) hab.reachable, ?_⟩⟩
      rw [hloc s ht hs]
      exact hab
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change (S'.val.1.val \ S'.val.2) ⊔ unionGraph U' = S.val.1.val
    rw [replace_cross S U, hin, sdiff_sup_cancel S.prop]
  · exact hin

noncomputable def forestEquiv (r : V) : Sample V ≃ Sample V where
  toFun S := transform r S false
  invFun S := transform r S true
  left_inv S := transform_inverse r S false
  right_inv S := transform_inverse r S true

theorem forestEquiv_retained (r : V) (S : Sample V) :
    Nat.card ((forestEquiv r) S).val.2.edgeSet = Nat.card S.val.2.edgeSet :=
  replace_card _ _

def NoRetainedChild (T : CayleyProbe.Tree V) (H : SimpleGraph V) (r v : V) : Prop :=
  ¬ ∃ w, H.Adj v w ∧ T.val.dist r v < T.val.dist r w

omit [LinearOrder V] in
theorem leaf_local (S : Sample V) (r : V) (s : Set V) (hs : s ∈ parts S.val.2)
    (x : s) :
    NoRetainedChild S.val.1 S.val.2 r x.val ↔
      CayleyProbe.RootedLeaf (localTree S.val.1 S.prop s hs).val
        (entry S.val.1 r s hs) x := by
  unfold NoRetainedChild CayleyProbe.RootedLeaf
  apply not_congr
  constructor
  · rintro ⟨y, ha, hlt⟩
    have hy := mem_part_of_reachable hs x.prop ha.reachable
    refine ⟨⟨y,hy⟩, ha, ?_⟩
    have d := local_depth S.val.1 r S.prop s hs ⟨y,hy⟩
    change S.val.1.val.dist r y = _ at d
    rw [local_depth S.val.1 r S.prop s hs x, d] at hlt
    exact Nat.lt_of_add_lt_add_left hlt
  · rintro ⟨y, ha, hlt⟩
    refine ⟨y.val, ha, ?_⟩
    rw [local_depth S.val.1 r S.prop s hs x, local_depth S.val.1 r S.prop s hs y]
    exact Nat.add_lt_add_left hlt _

omit [Finite V] in
theorem peak_local (S : Sample V) (s : Set V) (hs : s ∈ parts S.val.2) (x : s) :
    CayleyProbe.Peak S.val.2 x.val ↔ CayleyProbe.Peak (localTree S.val.1 S.prop s hs).val x := by
  constructor
  · intro h y ha
    exact h y.val ha
  · intro h y ha
    exact h ⟨y, mem_part_of_reachable hs x.prop ha.reachable⟩ ha

noncomputable def splitByParts (H : SimpleGraph V) (P : V → Prop) :
    {x : V // P x} ≃ Σ s : parts H, {x : s.val // P x.val} := by
  let f : (Σ s : parts H, {x : s.val // P x.val}) → {x : V // P x} :=
    fun a => ⟨a.2.val.val, a.2.prop⟩
  refine (Equiv.ofBijective f ⟨?_, ?_⟩).symm
  · intro a b h
    rcases a with ⟨s, x⟩
    rcases b with ⟨t, y⟩
    have he : x.val.val = y.val.val := congrArg Subtype.val h
    have st : s = t := Subtype.ext (part_eq s.prop t.prop x.val.prop (he.symm ▸ y.val.prop))
    subst t
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext (Subtype.ext he)))
  · intro x
    exact ⟨⟨⟨_, mem_parts H x.val⟩, ⟨⟨x.val, mem_own_part H x.val⟩, x.prop⟩⟩, rfl⟩

omit [LinearOrder V] in
theorem by_parts_card (H : SimpleGraph V) (P : V → Prop) (hF : Fintype (parts H)) :
    Nat.card {x : V // P x} = ∑ s : parts H, Nat.card {x : s.val // P x.val} := by
  let := hF
  rw [Nat.card_congr (splitByParts H P), Nat.card_sigma]

theorem forestEquiv_peaks (r : V) (S : Sample V) :
    Nat.card {v // CayleyProbe.Peak S.val.2 v} =
      Nat.card {v // NoRetainedChild ((forestEquiv r) S).val.1 ((forestEquiv r) S).val.2 r v} := by
  classical
  let U : Family (parts S.val.2) := fun s =>
    (CayleyProbe.fixedRootEquiv (entry S.val.1 r s.val s.prop)) (localTree S.val.1 S.prop s.val s.prop)
  let S' := replace S U
  let hparts := parts_congr (replace_reachable S U)
  let P := CayleyProbe.Peak S.val.2
  let Q := NoRetainedChild S'.val.1 S'.val.2 r
  change Nat.card {v // P v} = Nat.card {v // Q v}
  let hL : Fintype (parts S.val.2) := Fintype.ofFinite _
  let hR : Fintype (parts S'.val.2) := Fintype.ofFinite _
  rw [by_parts_card S.val.2 P hL, by_parts_card S'.val.2 Q hR]
  let e : parts S.val.2 ≃ parts S'.val.2 := (Set.equivOfEq hparts).symm
  apply Fintype.sum_equiv e
  intro s
  have ht : s.val ∈ parts S'.val.2 := hparts.symm ▸ s.prop
  change Nat.card {x : s.val // P x.val} = Nat.card {x : s.val // Q x.val}
  have h₁ := Nat.card_congr (Equiv.subtypeEquivRight (peak_local S s.val s.prop))
  have h₂ := Nat.card_congr (Equiv.subtypeEquivRight (leaf_local S' r s.val ht))
  rw [h₁, h₂, local_after S U s.val s.prop ht, entry_replace S U r s.val s.prop ht]
  let : Fintype s.val := Fintype.ofFinite _
  rw [← CayleyProbe.filterCard_eq_natCard, ← CayleyProbe.filterCard_eq_natCard]
  exact CayleyProbe.fixedRootEquiv_filterCard _ _


end CayleyForest

end

section

namespace CayleyMarks

open SimpleGraph CayleyColors CayleyForest

universe u w
variable {V : Type u} {A : Type w}

section Zero
variable [Zero A]

/-- Keep an edge exactly when its difference label is zero. -/
def retained (T : CayleyProbe.Tree V) (d : T.val.edgeSet → A) : SimpleGraph V :=
  fromEdgeSet {e | ∃ h : e ∈ T.val.edgeSet, d ⟨e,h⟩ = 0}

theorem retained_edges (T : CayleyProbe.Tree V) (d : T.val.edgeSet → A) (e : Sym2 V) :
    e ∈ (retained T d).edgeSet ↔ ∃ h : e ∈ T.val.edgeSet, d ⟨e,h⟩ = 0 := by
  rw [retained, edgeSet_fromEdgeSet]
  constructor
  · exact And.left
  · rintro ⟨h,hz⟩
    exact ⟨⟨h,hz⟩, T.val.not_isDiag_of_mem_edgeSet h⟩

theorem retained_le (T : CayleyProbe.Tree V) (d : T.val.edgeSet → A) : retained T d ≤ T.val := by
  rw [← edgeSet_subset_edgeSet]
  intro e he
  exact ((retained_edges T d e).mp he).choose

theorem retained_iff (T : CayleyProbe.Tree V) (d : T.val.edgeSet → A) (e : T.val.edgeSet) :
    e.val ∈ (retained T d).edgeSet ↔ d e = 0 := by
  rw [retained_edges]
  exact ⟨fun ⟨_,h⟩ => h, fun h => ⟨e.prop,h⟩⟩

theorem retained_parent (T : CayleyProbe.Tree V) (r : V) (d : T.val.edgeSet → A)
    (v : Away r) :
    (retained T d).Adj v.val (parent T r v) ↔ d (edgeEquiv T r v) = 0 :=
  (mem_edgeSet _).symm.trans (retained_iff T d (edgeEquiv T r v))

abbrev Deleted (S : Sample V) :=
  {e : Sym2 V // e ∈ S.val.1.val.edgeSet ∧ e ∉ S.val.2.edgeSet}

def deletedEquiv (S : Sample V) : Deleted S ≃ (S.val.1.val \ S.val.2).edgeSet :=
  Set.equivOfEq (edgeSet_sdiff _ _).symm

abbrev Marked (V : Type u) (A : Type w) [Zero A] :=
  Σ S : Sample V, Deleted S → {x : A // x ≠ 0}

def split (x : Σ T : CayleyProbe.Tree V, T.val.edgeSet → A) : Marked V A :=
  let H := retained x.1 x.2
  ⟨⟨⟨x.1,H⟩, retained_le x.1 x.2⟩, fun e =>
    let he : e.val ∈ x.1.val.edgeSet := e.prop.1
    ⟨x.2 ⟨e.val,he⟩, fun hz => e.prop.2 ((retained_iff x.1 x.2 ⟨e.val,he⟩).mpr hz)⟩⟩

noncomputable def fill (x : Marked V A) (e : x.1.val.1.val.edgeSet) : A := by
  classical
  exact if h : e.val ∈ x.1.val.2.edgeSet then 0 else (x.2 ⟨e.val, e.prop, h⟩).val

noncomputable def join (x : Marked V A) : Σ T : CayleyProbe.Tree V, T.val.edgeSet → A :=
  ⟨x.1.val.1, fill x⟩

theorem fill_zero (x : Marked V A) (e : x.1.val.1.val.edgeSet) :
    fill x e = 0 ↔ e.val ∈ x.1.val.2.edgeSet := by
  classical
  by_cases h : e.val ∈ x.1.val.2.edgeSet
  · simp [fill, h]
  · simp [fill, h, (x.2 ⟨e.val,e.prop,h⟩).prop]

theorem fill_deleted (x : Marked V A) (e : Deleted x.1) :
    fill x ⟨e.val,e.prop.1⟩ = (x.2 e).val := by
  classical
  simp [fill, e.prop.2]

theorem join_retained (x : Marked V A) : retained x.1.val.1 (fill x) = x.1.val.2 := by
  apply edgeSet_injective
  ext e
  rw [retained_edges]
  change (∃ he : e ∈ x.1.val.1.val.edgeSet, fill x ⟨e,he⟩ = 0) ↔ e ∈ x.1.val.2.edgeSet
  simp only [fill_zero]
  exact ⟨fun ⟨_,hh⟩ => hh, fun hh => ⟨edgeSet_mono x.1.prop hh, hh⟩⟩

noncomputable def markedEquiv : (Σ T : CayleyProbe.Tree V, T.val.edgeSet → A) ≃ Marked V A where
  toFun := split
  invFun := join
  left_inv x := by
    classical
    change (⟨x.1, fill (split x)⟩ : Σ T : CayleyProbe.Tree V, T.val.edgeSet → A) = ⟨x.1,x.2⟩
    apply congrArg (Sigma.mk x.1)
    funext e
    by_cases h : e.val ∈ (retained x.1 x.2).edgeSet
    · exact ((fill_zero (split x) e).mpr h).trans ((retained_iff x.1 x.2 e).mp h).symm
    · exact fill_deleted (split x) ⟨e.val,e.prop,h⟩
  right_inv x := by
    classical
    let y := split (join x)
    have hH : y.1.val.2 = x.1.val.2 := join_retained x
    have hs : y.1 = x.1 := Subtype.ext (Prod.ext rfl hH)
    have hm (e : Deleted y.1) (f : Deleted x.1) (hef : e.val = f.val) :
        (y.2 e).val = (x.2 f).val := by
      have hneg : e.val ∉ x.1.val.2.edgeSet := by rw [hef]; exact f.prop.2
      change fill x ⟨e.val,e.prop.1⟩ = (x.2 f).val
      unfold fill
      rw [dite_eq_right hneg, show (⟨e.val,e.prop.1,hneg⟩ : Deleted x.1) = f from Subtype.ext hef]
    change y = x
    rcases y with ⟨s,labels⟩
    rcases x with ⟨t,labels'⟩
    dsimp only at hs hm
    cases hs
    apply congrArg (Sigma.mk s)
    funext e
    exact Subtype.ext (hm e e rfl)

end Zero

theorem conflict_retained [AddGroup A] (T : CayleyProbe.Tree V) (r : V) (c : V → A) :
    retained T ((edgeColorEquiv T r) c).2 = CayleyScheduler.conflict T.val c := by
  ext x y
  have hb (h : T.val.Adj x y) :
      (retained T ((edgeColorEquiv T r) c).2).Adj x y ↔ c x = c y := by
    rcases edge_orientation T r h with ⟨hx,he⟩ | ⟨hy,he⟩
    · have hh := retained_parent T r ((edgeColorEquiv T r) c).2 ⟨x,hx⟩
      rw [zero_pattern_iff] at hh
      exact he ▸ hh
    · have hh := retained_parent T r ((edgeColorEquiv T r) c).2 ⟨y,hy⟩
      rw [zero_pattern_iff] at hh
      have h' : (retained T ((edgeColorEquiv T r) c).2).Adj y x ↔ c y = c x := he ▸ hh
      exact (adj_comm (retained T ((edgeColorEquiv T r) c).2) x y).trans (h'.trans eq_comm)
  exact ⟨fun h => ⟨retained_le T _ h, (hb (retained_le T _ h)).mp h⟩,
    fun ⟨h,hc⟩ => (hb h).mpr hc⟩

variable [Zero A] [Finite V] [LinearOrder V]

noncomputable def markedForestEquiv (r : V) : Marked V A ≃ Marked V A :=
  Equiv.sigmaCongr (forestEquiv r) fun S =>
    let e := Set.equivOfEq (congrArg SimpleGraph.edgeSet (replace_cross S _).symm)
    Equiv.arrowCongr ((deletedEquiv S).trans (e.trans (deletedEquiv (forestEquiv r S)).symm)) (Equiv.refl _)

theorem markedForest_base (r : V) (s : Marked V A) :
    (markedForestEquiv r s).1 = forestEquiv r s.1 := rfl

/-- The occupied ordinary targets after retaining the zero-difference parent coordinates. -/
def HasTarget (T : CayleyProbe.Tree V) (r : V) (d : Away r → A) (w : V) : Prop :=
  ∃ v : Away r, parent T r v = w ∧ d v = 0

omit [Finite V] [LinearOrder V] in
theorem retained_child_iff (T : CayleyProbe.Tree V) (r : V) (d : T.val.edgeSet → A) (w : V) :
    (∃ v, (retained T d).Adj w v ∧ T.val.dist r w < T.val.dist r v) ↔
      HasTarget T r (d ∘ edgeEquiv T r) w := by
  constructor
  · rintro ⟨v,ha,hlt⟩
    have hv : v ≠ r := by
      intro he
      rw [he, dist_self] at hlt
      exact Nat.not_lt_zero _ hlt
    have hpar := parent_unique T r ⟨v,hv⟩ (retained_le T d ha.symm) hlt
    refine ⟨⟨v,hv⟩, hpar.symm, (retained_parent T r d ⟨v,hv⟩).mp ?_⟩
    exact hpar ▸ ha.symm
  · rintro ⟨v,hw,hz⟩
    have hp := parent_spec T r v
    exact ⟨v.val, hw ▸ ((retained_parent T r d v).mpr hz).symm, hw ▸ hp.2⟩


end CayleyMarks

end
