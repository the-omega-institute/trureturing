/- GID: D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Eccentric/DePatraCounting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Edge-sensitive pendant and bridge component counting correspondences. -/
import D5.S3.Combinatorics.Graph.Eccentric.DePatraBridge

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Eccentric.DePatraCounting

open SimpleGraph DePatraBridge Classical
open scoped BigOperators
noncomputable section
variable {V : Type} {G : SimpleGraph V} {S : Set V} {r l : V}

/-- A connected subgraph containing a pendant vertex and any other vertex uses its edge. -/
theorem pendant_edge (K : G.Subgraph) (hK : K.Connected) (hl : l ∈ K.verts)
    (hside : K.verts ⊆ insert l S)
    (hnbr : ∀ x ∈ insert l S, G.Adj l x → x = r)
    (hne : K ≠ G.singletonSubgraph l) : K.Adj l r := by
  have hz : ∃ z ∈ K.verts, z ≠ l := by
    by_contra hn
    apply hne
    apply (eq_singletonSubgraph_iff_verts_eq K).mpr
    ext z
    constructor
    · intro hz
      have he : z = l := by by_contra he; exact hn ⟨z, hz, he⟩
      simpa using he
    · intro hz
      simpa only [Set.mem_singleton_iff.mp hz] using hl
  obtain ⟨z, hz, hzl⟩ := hz
  obtain ⟨p⟩ := hK ⟨l, hl⟩ ⟨z, hz⟩
  cases p with
  | nil => exact False.elim (hzl rfl)
  | @cons a b c hab p =>
    have hb : b.val = r := hnbr b.val (hside b.property) (K.adj_sub hab)
    change K.Adj l b.val at hab
    simpa only [hb] using hab

/-- Removing the pendant vertex and then restoring its selected edge is exact on edges too. -/
theorem pendant_reconstruct (K : G.Subgraph) (hside : K.verts ⊆ insert l S)
    (_hl : l ∈ K.verts) (_hls : l ∉ S) (_hr : r ∈ S)
    (hnbr : ∀ x ∈ insert l S, G.Adj l x → x = r)
    (hedge : K.Adj l r) : restrict K S ⊔ G.subgraphOfAdj (K.adj_sub hedge) = K := by
  apply le_antisymm
  · exact sup_le (by
      constructor
      · exact Set.inter_subset_left
      · intro x y hxy; exact hxy.2.2)
      (subgraphOfAdj_le_iff _ K |>.mpr hedge)
  · constructor
    · intro x hx
      rcases Set.mem_insert_iff.mp (hside hx) with he | hs
      · subst x; exact Or.inr (by simp)
      · exact Or.inl ⟨hx, hs⟩
    · intro x y hxy
      by_cases hx : x = l
      · subst x
        have hy := hnbr y (hside (K.edge_vert hxy.symm)) (K.adj_sub hxy)
        subst y
        exact Or.inr rfl
      · by_cases hy : y = l
        · subst y
          have hx' := hnbr x (hside (K.edge_vert hxy)) (K.adj_sub hxy.symm)
          subst x
          exact Or.inr (by simp [subgraphOfAdj_adj, Sym2.eq_swap])
        · exact Or.inl ⟨⟨K.edge_vert hxy, (Set.mem_insert_iff.mp
            (hside (K.edge_vert hxy))).resolve_left hx⟩,
            ⟨K.edge_vert hxy.symm, (Set.mem_insert_iff.mp
            (hside (K.edge_vert hxy.symm))).resolve_left hy⟩, hxy⟩

def pendantAttach (K : RootedWithin G S r (∅ : Set V)) (he : G.Adj l r) :
    RootedWithin G (insert l S) l (∅ : Set V) :=
  ⟨K.val ⊔ G.subgraphOfAdj he,
    Subgraph.connected_sup K.property.1.preconnected
      (Subgraph.subgraphOfAdj_connected he).preconnected
      ⟨r, K.property.2.1, by simp⟩,
    Or.inr (by simp), Set.empty_subset _, by
      intro x hx
      rcases hx with hx | hx
      · exact Set.mem_insert_of_mem l (K.property.2.2.2 hx)
      · rcases (show x = l ∨ x = r from by simpa using hx) with rfl | rfl
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (K.property.2.2.2 K.property.2.1)⟩

/-- Singleton-or-rooted decomposition of the entire pendant side. -/
def pendantRootEquiv (hr : r ∈ S) (hl : l ∉ S) (he : G.Adj l r)
    (hnbr : ∀ x ∈ insert l S, G.Adj l x → x = r)
    (hexit : ∀ x y, G.Adj x y → x ∈ S → y ∉ S → x = r) :
    RootedWithin G (insert l S) l (∅ : Set V) ≃
      Unit ⊕ RootedWithin G S r (∅ : Set V) := by
  classical
  let strip (K : RootedWithin G (insert l S) l (∅ : Set V))
      (hne : K.val ≠ G.singletonSubgraph l) : RootedWithin G S r (∅ : Set V) :=
    let hedge := pendant_edge K.val K.property.1 K.property.2.1 K.property.2.2.2 hnbr hne
    ⟨restrict K.val S,
      restrict_connected K.val S r K.property.1 (K.val.edge_vert hedge.symm) hr hexit,
      ⟨K.val.edge_vert hedge.symm, hr⟩, Set.empty_subset _, fun _ hx => hx.2⟩
  let single : RootedWithin G (insert l S) l (∅ : Set V) :=
    ⟨G.singletonSubgraph l, Subgraph.singletonSubgraph_connected, by simp,
      Set.empty_subset _, by simp⟩
  let attach := fun K : RootedWithin G S r (∅ : Set V) => pendantAttach K he
  have attach_ne (K : RootedWithin G S r (∅ : Set V)) :
      (attach K).val ≠ G.singletonSubgraph l := by
    intro hh
    have hrr : r ∈ (attach K).val.verts := Or.inl K.property.2.1
    rw [hh] at hrr
    have hh' : r = l := by simpa using hrr
    exact hl (hh' ▸ hr)
  refine ⟨fun K => if h : K.val = G.singletonSubgraph l then Sum.inl ()
      else Sum.inr (strip K h),
    fun t => match t with | Sum.inl _ => single | Sum.inr K => attach K, ?_, ?_⟩
  · intro K
    by_cases hh : K.val = G.singletonSubgraph l
    · simp only [hh, dite_true]
      exact Subtype.ext hh.symm
    · simp only [hh, dite_false]
      apply Subtype.ext
      exact pendant_reconstruct K.val K.property.2.2.2 K.property.2.1 hl hr hnbr
        (pendant_edge K.val K.property.1 K.property.2.1 K.property.2.2.2 hnbr hh)
  · intro t
    cases t with
    | inl u => cases u; simp [single]
    | inr K =>
      simp only [attach_ne K, dite_false, Sum.inr.injEq]
      apply Subtype.ext
      apply restrict_sup_left K.val (G.subgraphOfAdj he) S {l, r} r
        K.property.2.2.2 (by intro x hx; exact hx) K.property.2.1
      intro x hx hx'
      rcases hx' with hx' | hx'
      · exact False.elim (hl (hx' ▸ hx))
      · simpa using hx'

theorem pendant_root_count [Finite V] (hr : r ∈ S) (hl : l ∉ S) (he : G.Adj l r)
    (hnbr : ∀ x ∈ insert l S, G.Adj l x → x = r)
    (hexit : ∀ x y, G.Adj x y → x ∈ S → y ∉ S → x = r) :
    Nat.card (RootedWithin G (insert l S) l (∅ : Set V)) =
      1 + Nat.card (RootedWithin G S r (∅ : Set V)) := by
  rw [Nat.card_congr (pendantRootEquiv hr hl he hnbr hexit), Nat.card_sum]
  simp


theorem qualifyingBridge_swap [Finite V] {u v : V} (h : QualifyingBridge G u v) :
    QualifyingBridge G v u := by
  refine ⟨h.1, ?_, ?_, ?_⟩
  · simpa only [Sym2.eq_swap] using h.2.1
  · simpa only [Sym2.eq_swap] using h.2.2.2
  · simpa only [Sym2.eq_swap] using h.2.2.1

@[simp] theorem deletedSide_swap (u v r : V) : deletedSide G v u r = deletedSide G u v r := by
  simp only [deletedSide, Sym2.eq_swap]

/-- The only edge leaving an endpoint deletion component is the original bridge. -/
theorem bridge_side_cross {u v x y : V} (hb : G.IsBridge s(u, v))
    (hxy : G.Adj x y) (hx : x ∈ deletedSide G u v u) (hy : y ∉ deletedSide G u v u) :
    x = u ∧ y = v := by
  have he : s(x, y) = s(u, v) := by
    by_contra he
    exact hy (hx.trans (deleteEdges_adj.mpr ⟨hxy, by simpa using he⟩).reachable)
  rcases Sym2.eq_iff.mp he with h | h
  · exact h
  · exact False.elim (hb (h.1 ▸ hx))

theorem bridge_pendant_data [Finite V] {u v : V} (h : QualifyingBridge G u v) :
    v ∈ deletedSide G u v v ∧ u ∉ deletedSide G u v v ∧ G.Adj u v ∧
    (∀ x ∈ insert u (deletedSide G u v v), G.Adj u x → x = v) ∧
    (∀ x y, G.Adj x y → x ∈ deletedSide G u v v → y ∉ deletedSide G u v v → x = v) := by
  have hp := qualifying_components h
  have hu : u ∈ deletedSide G u v u := Reachable.rfl
  have hv : v ∈ deletedSide G u v v := Reachable.rfl
  have hnot : u ∉ deletedSide G u v v := fun hh => Set.disjoint_left.mp hp.2.2.1 hu hh
  refine ⟨hv, hnot, hp.1, ?_, ?_⟩
  · intro x hx hux
    rcases Set.mem_insert_iff.mp hx with he | hx
    · exact False.elim (hux.ne he.symm)
    · exact (bridge_side_cross h.2.1 hux hu
        (fun hxa => Set.disjoint_left.mp hp.2.2.1 hxa hx)).2
  · intro x y hxy hx hy
    have hcross := bridge_side_cross (qualifyingBridge_swap h).2.1 hxy
    simp only [deletedSide_swap] at hcross
    exact (hcross hx hy).1

/-- The pendant extension of the second actual component contributes one singleton. -/
theorem bridge_pendant_root_count [Finite V] {u v : V} (h : QualifyingBridge G u v) :
    Nat.card (RootedWithin G (insert u (deletedSide G u v v)) u (∅ : Set V)) =
      1 + Nat.card (RootedWithin G (deletedSide G u v v) v (∅ : Set V)) := by
  obtain ⟨hr, hl, he, hnbr, hexit⟩ := bridge_pendant_data h
  exact pendant_root_count hr hl he hnbr hexit


/-- A pendant-containing subgraph with a target in the other side is never a singleton. -/
def pendantTargetsEquiv (hr : r ∈ S) (hl : l ∉ S) (he : G.Adj l r)
    (hnbr : ∀ x ∈ insert l S, G.Adj l x → x = r)
    (hexit : ∀ x y, G.Adj x y → x ∈ S → y ∉ S → x = r)
    (s : Set V) (hs : s ⊆ S) (hne : s.Nonempty) :
    RootedWithin G (insert l S) l s ≃ RootedWithin G S r s := by
  have nonsingle (K : RootedWithin G (insert l S) l s) :
      K.val ≠ G.singletonSubgraph l := by
    intro hh
    obtain ⟨x, hx⟩ := hne
    have hv := K.property.2.2.1 hx
    rw [hh] at hv
    have heq : x = l := by simpa using hv
    exact hl (heq ▸ hs hx)
  let strip (K : RootedWithin G (insert l S) l s) : RootedWithin G S r s :=
    let hedge := pendant_edge K.val K.property.1 K.property.2.1 K.property.2.2.2 hnbr
      (nonsingle K)
    ⟨restrict K.val S,
      restrict_connected K.val S r K.property.1 (K.val.edge_vert hedge.symm) hr hexit,
      ⟨K.val.edge_vert hedge.symm, hr⟩,
      fun x hx => ⟨K.property.2.2.1 hx, hs hx⟩, fun _ hx => hx.2⟩
  let attach (K : RootedWithin G S r s) : RootedWithin G (insert l S) l s :=
    ⟨K.val ⊔ G.subgraphOfAdj he,
      Subgraph.connected_sup K.property.1.preconnected
        (Subgraph.subgraphOfAdj_connected he).preconnected
        ⟨r, K.property.2.1, by simp⟩,
      Or.inr (by simp), fun x hx => Or.inl (K.property.2.2.1 hx), by
        intro x hx
        rcases hx with hx | hx
        · exact Set.mem_insert_of_mem l (K.property.2.2.2 hx)
        · rcases (show x = l ∨ x = r from by simpa using hx) with rfl | rfl
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ hr⟩
  refine ⟨strip, attach, ?_, ?_⟩
  · intro K
    apply Subtype.ext
    exact pendant_reconstruct K.val K.property.2.2.2 K.property.2.1 hl hr hnbr
      (pendant_edge K.val K.property.1 K.property.2.1 K.property.2.2.2 hnbr (nonsingle K))
  · intro K
    apply Subtype.ext
    apply restrict_sup_left K.val (G.subgraphOfAdj he) S {l, r} r
      K.property.2.2.2 (by intro x hx; exact hx) K.property.2.1
    intro x hx hx'
    rcases hx' with hx' | hx'
    · exact False.elim (hl (hx' ▸ hx))
    · simpa using hx'

theorem bridge_pendant_targets_count [Finite V] {u v : V} (h : QualifyingBridge G u v)
    (s : Set V) (hs : s ⊆ deletedSide G u v v) (hne : s.Nonempty) :
    Nat.card (RootedWithin G (insert u (deletedSide G u v v)) u s) =
      Nat.card (RootedWithin G (deletedSide G u v v) v s) := by
  obtain ⟨hr, hl, he, hnbr, hexit⟩ := bridge_pendant_data h
  exact Nat.card_congr (pendantTargetsEquiv hr hl he hnbr hexit s hs hne)

/-- Restricting the ambient vertex type does not replace edge choices by induced subgraphs. -/
def withinInduceEquiv (s : Set V) (hs : s ⊆ S) :
    Within G S s ≃ Containing (G.induce S) (Subtype.val ⁻¹' s) := by
  let f : G.induce S →g G := (Embedding.induce S).toHom
  have connected_comap (K : G.Subgraph) (hK : K.Connected) (hside : K.verts ⊆ S) :
      (K.comap f).Connected := by
    let g : K.coe →g (K.comap f).coe := {
      toFun x := ⟨⟨x.val, hside x.property⟩, x.property⟩
      map_rel' := by intro x y h; exact ⟨K.adj_sub h, h⟩ }
    apply Subgraph.connected_iff'.mpr
    apply hK.coe.map g
    intro y
    exact ⟨⟨y.val.val, y.property⟩, rfl⟩
  refine ⟨fun K => ⟨K.val.comap f,
      connected_comap K.val K.property.1 K.property.2.2,
      fun x hx => K.property.2.1 hx⟩,
    fun L => ⟨L.val.map f, subgraph_map_connected f L.property.1, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hs hx⟩, L.property.2 hx, rfl⟩
  · rintro x ⟨y, hy, rfl⟩
    exact y.property
  · intro K
    apply Subtype.ext
    apply Subgraph.ext
    · ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, K.property.2.2 hx⟩, hx, rfl⟩
    · funext x y
      apply propext
      constructor
      · rintro ⟨a, b, hab, rfl, rfl⟩; exact hab.2
      · intro hxy
        exact ⟨⟨x, K.property.2.2 (K.val.edge_vert hxy)⟩,
          ⟨y, K.property.2.2 (K.val.edge_vert hxy.symm)⟩,
          ⟨K.val.adj_sub hxy, hxy⟩, rfl, rfl⟩
  · intro L
    apply Subtype.ext
    apply Subgraph.ext
    · ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        exact (Subtype.ext hxy : y = x) ▸ hy
      · intro hx; exact ⟨x, hx, rfl⟩
    · funext x y
      apply propext
      constructor
      · rintro ⟨hG, a, b, hab, hax, hby⟩
        have ha : a = x := Subtype.ext hax
        have hb : b = y := Subtype.ext hby
        simpa only [ha, hb] using hab
      · intro hxy
        exact ⟨L.val.adj_sub hxy, x, y, hxy, rfl, rfl⟩

theorem within_induce_count (s : Set V) (hs : s ⊆ S) :
    Nat.card (Within G S s) = countContaining (G.induce S) (Subtype.val ⁻¹' s) :=
  Nat.card_congr (withinInduceEquiv s hs)

/-- Root containment and explicit targets describe the same native set of subgraphs. -/
theorem rooted_within_count (s : Set V) :
    Nat.card (RootedWithin G S r s) = Nat.card (Within G S (insert r s)) := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro K
  simp only [Set.insert_subset_iff]
  tauto

theorem within_univ_count (s : Set V) :
    Nat.card (Within G Set.univ s) = countContaining G s := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro K
  simp


/-- Omitting the pendant vertex is exactly the same as being supported on the base side. -/
def pendantRootlessEquiv (hl : l ∉ S) (s : Set V) :
    RootlessWithin G (insert l S) l s ≃ Within G S s where
  toFun K := ⟨K.val, K.property.1, K.property.2.2.1, by
    intro x hx
    exact (Set.mem_insert_iff.mp (K.property.2.2.2 hx)).resolve_left
      (fun he => K.property.2.1 (he ▸ hx))⟩
  invFun K := ⟨K.val, K.property.1, fun hx => hl (K.property.2.2 hx),
    K.property.2.1, fun _ hx => Set.mem_insert_of_mem l (K.property.2.2 hx)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- At the base root, including or omitting the pendant edge are two independent choices. -/
theorem pendant_base_count [Finite V] (hr : r ∈ S) (hl : l ∉ S) (he : G.Adj l r)
    (hnbr : ∀ x ∈ insert l S, G.Adj l x → x = r)
    (hexit : ∀ x y, G.Adj x y → x ∈ S → y ∉ S → x = r)
    (s : Set V) (hs : s ⊆ S) :
    Nat.card (RootedWithin G (insert l S) r s) =
      2 * Nat.card (RootedWithin G S r s) := by
  rw [rooted_within_count, within_count_partition _ _ _ l,
    Nat.card_congr (pendantRootlessEquiv hl (insert r s)),
    Nat.card_congr (pendantTargetsEquiv hr hl he hnbr hexit (insert r s)
      (Set.insert_subset hr hs) ⟨r, Set.mem_insert _ _⟩)]
  rw [rooted_within_count]
  have hh : insert r (insert r s) = insert r s := by simp
  rw [rooted_within_count, hh]
  omega

/-- Relabeling a side transports actual subgraphs and all of their independent edge choices. -/
theorem within_relabel_count {H : SimpleGraph V} (e : V ≃ V) (T s : Set V)
    (hside : ∀ x, x ∈ S ↔ e x ∈ T)
    (hadj : ∀ x ∈ S, ∀ y ∈ S, G.Adj x y ↔ H.Adj (e x) (e y))
    (hs : s ⊆ S) : Nat.card (Within G S s) = Nat.card (Within H T (e '' s)) := by
  let f : S ≃ T := {
    toFun x := ⟨e x.val, (hside x.val).mp x.property⟩
    invFun y := ⟨e.symm y.val, (hside (e.symm y.val)).mpr (by simp only [Equiv.apply_symm_apply]; exact y.property)⟩
    left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
    right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.val }
  let ei : G.induce S ≃g H.induce T := {
    toEquiv := f
    map_rel_iff' := by intro x y; exact (hadj x.val x.property y.val y.property).symm }
  have ht : e '' s ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hside x).mp (hs hx)
  rw [within_induce_count s hs, within_induce_count (e '' s) ht]
  rw [countContaining_iso ei]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, hx, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨x, hs hx⟩, hx, Subtype.ext hxy⟩

theorem rooted_relabel_count {H : SimpleGraph V} (e : V ≃ V) (T s : Set V)
    (hside : ∀ x, x ∈ S ↔ e x ∈ T)
    (hadj : ∀ x ∈ S, ∀ y ∈ S, G.Adj x y ↔ H.Adj (e x) (e y))
    (hr : r ∈ S) (hs : s ⊆ S) :
    Nat.card (RootedWithin G S r s) = Nat.card (RootedWithin H T (e r) (e '' s)) := by
  rw [rooted_within_count, rooted_within_count]
  simpa only [Set.image_insert_eq] using
    within_relabel_count e T (insert r s) hside hadj (Set.insert_subset hr hs)


structure RootSeparation (G : SimpleGraph V) (S T : Set V) (r : V) : Prop where
  root_left : r ∈ S
  root_right : r ∈ T
  cover : ∀ x, x ∈ S ∨ x ∈ T
  inter : ∀ x, x ∈ S → x ∈ T → x = r
  edges : ∀ x y, G.Adj x y → (x ∈ S ∧ y ∈ S) ∨ (x ∈ T ∧ y ∈ T)

namespace RootSeparation
variable {T : Set V}
theorem exit (h : RootSeparation G S T r) :
    ∀ x y, G.Adj x y → x ∈ S → y ∉ S → x = r := by
  intro x y hxy hx hy
  rcases h.edges x y hxy with hh | hh
  · exact False.elim (hy hh.2)
  · exact h.inter x hx hh.1

theorem rooted_count [Finite V] (h : RootSeparation G S T r) (s : Set V) :
    Nat.card (RootedWithin G Set.univ r s) =
      Nat.card (RootedWithin G S r (s ∩ S)) *
        Nat.card (RootedWithin G T r (s ∩ T)) :=
  rootedGluing_count G S T r s h.root_left h.root_right h.cover h.inter h.edges

theorem within_count [Finite V] (h : RootSeparation G S T r) (s : Set V)
    (hs : s ⊆ S) (hne : s.Nonempty) :
    countContaining G s = Nat.card (RootlessWithin G S r s) +
      Nat.card (RootedWithin G S r s) * Nat.card (RootedWithin G T r (s ∩ T)) := by
  obtain ⟨x, hx⟩ := hne
  rw [← within_univ_count]
  exact within_gluing_count G S T s r h.root_left h.root_right h.cover h.inter h.edges hs x hx
end RootSeparation

/-- The source bridge separates the two extended sides at u. -/
theorem bridge_separation [Finite V] {u v : V} (h : QualifyingBridge G u v) :
    RootSeparation G (deletedSide G u v u) (insert u (deletedSide G u v v)) u := by
  have hp := qualifying_components h
  refine ⟨Reachable.rfl, Set.mem_insert _ _, ?_, ?_, ?_⟩
  · intro x; exact (hp.2.1 x).imp id (Set.mem_insert_of_mem u)
  · intro x hx hy
    rcases Set.mem_insert_iff.mp hy with he | hy
    · exact he
    · exact False.elim (Set.disjoint_left.mp hp.2.2.1 hx hy)
  · intro x y hxy
    by_cases he : s(x, y) = s(u, v)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨Set.mem_insert _ _, Set.mem_insert_of_mem _ Reachable.rfl⟩
      · exact Or.inr ⟨Set.mem_insert_of_mem _ Reachable.rfl, Set.mem_insert _ _⟩
    · have hd : (G.deleteEdges {s(u, v)}).Adj x y :=
        deleteEdges_adj.mpr ⟨hxy, by simpa using he⟩
      rcases hp.2.1 x with hx | hx
      · exact Or.inl ⟨hx, hx.trans hd.reachable⟩
      · exact Or.inr ⟨Set.mem_insert_of_mem u hx,
          Set.mem_insert_of_mem u (hx.trans hd.reachable)⟩

/-- The transformed graph has the same extended-side separation at the identified root. -/
theorem shift_separation [Finite V] {u v : V} (h : QualifyingBridge G u v) :
    RootSeparation (bridgeShift G u v) (deletedSide G u v u)
      (insert u (deletedSide G u v v)) u := by
  have old := bridge_separation h
  have hp := qualifying_components h
  refine ⟨old.root_left, old.root_right, old.cover, old.inter, ?_⟩
  intro x y hxy
  rcases hxy.2 with hh | hh | ⟨hx, hy, hh⟩
  · rcases hh with ⟨rfl, rfl⟩
    exact Or.inr ⟨Set.mem_insert_of_mem _ Reachable.rfl, Set.mem_insert _ _⟩
  · rcases hh with ⟨rfl, rfl⟩
    exact Or.inr ⟨Set.mem_insert _ _, Set.mem_insert_of_mem _ Reachable.rfl⟩
  · rcases hh with hh | ⟨rfl, hh⟩ | ⟨rfl, hh⟩
    · exact old.edges x y hh
    · rcases old.edges v y hh with hs | hs
      · exact False.elim (Set.disjoint_left.mp hp.2.2.1 hs.1 Reachable.rfl)
      · exact Or.inr ⟨old.root_right, hs.2⟩
    · rcases old.edges x v hh with hs | hs
      · exact False.elim (Set.disjoint_left.mp hp.2.2.1 hs.2 Reachable.rfl)
      · exact Or.inr ⟨hs.1, old.root_right⟩


/-- The first component's complete internal adjacency is unchanged. -/
theorem shift_left_adj [Finite V] {u v x y : V} (h : QualifyingBridge G u v)
    (hx : x ∈ deletedSide G u v u) (hy : y ∈ deletedSide G u v u) :
    G.Adj x y ↔ (bridgeShift G u v).Adj x y := by
  have hd := (qualifying_components h).2.2.1
  have hxv : x ≠ v := fun he => Set.disjoint_left.mp hd hx (he ▸ Reachable.rfl)
  have hyv : y ≠ v := fun he => Set.disjoint_left.mp hd hy (he ▸ Reachable.rfl)
  have v_neighbor (z : V) (hz : z ∈ deletedSide G u v u) (hvz : G.Adj v z) : z = u := by
    have hc := bridge_side_cross (qualifyingBridge_swap h).2.1 hvz
      (show v ∈ deletedSide G v u v from Reachable.rfl)
      (by simpa only [deletedSide_swap] using
        (show z ∉ deletedSide G u v v from fun hh => Set.disjoint_left.mp hd hz hh))
    exact hc.2
  constructor
  · intro hxy
    exact ⟨hxy.ne, Or.inr (Or.inr ⟨hxv, hyv, Or.inl hxy⟩)⟩
  · rintro ⟨hne, hh | hh | ⟨_, _, hh⟩⟩
    · exact False.elim (hxv hh.1)
    · exact False.elim (hyv hh.2)
    · rcases hh with hh | ⟨hxu, hvy⟩ | ⟨hyu, hxv'⟩
      · exact hh
      · exact False.elim (hne (hxu.trans (v_neighbor y hy hvy).symm))
      · exact False.elim (hne ((v_neighbor x hx hxv'.symm).trans hyu.symm))

/-- On the extended second side, contraction and leaf addition swap the endpoint names. -/
theorem shift_right_adj_swap [Finite V] {u v x y : V} (h : QualifyingBridge G u v)
    (hx : x ∈ insert u (deletedSide G u v v))
    (hy : y ∈ insert u (deletedSide G u v v)) :
    G.Adj x y ↔ (bridgeShift G u v).Adj (Equiv.swap u v x) (Equiv.swap u v y) := by
  have huv : u ≠ v := (qualifying_components h).1.ne
  obtain ⟨hr, hl, he, hnbr, hexit⟩ := bridge_pendant_data h
  have nbr (z : V) (hz : z ∈ insert u (deletedSide G u v v)) : G.Adj u z ↔ z = v :=
    ⟨hnbr z hz, fun hh => hh ▸ he⟩
  have ucase (z : V) (hz : z ∈ insert u (deletedSide G u v v)) :
      G.Adj u z ↔ (bridgeShift G u v).Adj v (Equiv.swap u v z) := by
    rw [nbr z hz]
    by_cases hzu : z = u
    · subst z; simp [bridgeShift, huv]
    · by_cases hzv : z = v
      · subst z; simp [bridgeShift, huv, huv.symm]
      · rw [Equiv.swap_apply_of_ne_of_ne hzu hzv]
        simp [bridgeShift, hzv, hzu, Ne.symm hzv]
  have vcase (z : V) (hz : z ∈ insert u (deletedSide G u v v)) :
      G.Adj v z ↔ (bridgeShift G u v).Adj u (Equiv.swap u v z) := by
    by_cases hzu : z = u
    · subst z; simp [bridgeShift, huv, huv.symm, he.symm]
    · by_cases hzv : z = v
      · subst z; simp [bridgeShift, huv, huv.symm]
      · rw [Equiv.swap_apply_of_ne_of_ne hzu hzv]
        have hn : ¬G.Adj u z := fun hh => hzv ((nbr z hz).mp hh)
        simp [bridgeShift, hzu, hzv, huv, Ne.symm hzu, hn]
  by_cases hxu : x = u
  · subst x; simpa only [Equiv.swap_apply_left] using ucase y hy
  · by_cases hxv : x = v
    · subst x; simpa only [Equiv.swap_apply_right] using vcase y hy
    · by_cases hyu : y = u
      · subst y
        simpa only [Equiv.swap_apply_left, adj_comm] using ucase x hx
      · by_cases hyv : y = v
        · subst y
          simpa only [Equiv.swap_apply_right, adj_comm] using vcase x hx
        · rw [Equiv.swap_apply_of_ne_of_ne hxu hxv, Equiv.swap_apply_of_ne_of_ne hyu hyv]
          simp only [bridgeShift, hxv, hyv, hxu, hyu, false_and, and_false,
            false_or]
          exact ⟨fun hh => ⟨hh.ne, hxv, hyv, Or.inl hh⟩,
            fun hh => hh.2.2.2.elim id False.elim⟩

/-- Endpoint swapping preserves the extended second side as a set. -/
theorem swap_right_side [Finite V] {u v : V} (_h : QualifyingBridge G u v) (x : V) :
    x ∈ insert u (deletedSide G u v v) ↔
      Equiv.swap u v x ∈ insert u (deletedSide G u v v) := by
  classical
  by_cases hx : x = u <;> by_cases hy : x = v <;>
    simp_all [Equiv.swap_apply_def, show v ∈ deletedSide G u v v from Reachable.rfl]

theorem shift_left_within_count [Finite V] {u v : V} (h : QualifyingBridge G u v)
    (s : Set V) (hs : s ⊆ deletedSide G u v u) :
    Nat.card (Within G (deletedSide G u v u) s) =
      Nat.card (Within (bridgeShift G u v) (deletedSide G u v u) s) := by
  simpa using within_relabel_count (Equiv.refl V) (deletedSide G u v u) s
    (fun _ => Iff.rfl) (fun _ hx _ hy => shift_left_adj h hx hy) hs

theorem shift_right_rooted_count [Finite V] {u v : V} (h : QualifyingBridge G u v)
    (s : Set V) (hs : s ⊆ insert u (deletedSide G u v v)) :
    Nat.card (RootedWithin G (insert u (deletedSide G u v v)) v s) =
      Nat.card (RootedWithin (bridgeShift G u v) (insert u (deletedSide G u v v)) u
        (Equiv.swap u v '' s)) := by
  classical
  simpa using rooted_relabel_count (Equiv.swap u v) (insert u (deletedSide G u v v)) s
    (swap_right_side h) (fun _ hx _ hy => shift_right_adj_swap h hx hy)
    (Set.mem_insert_of_mem u (show v ∈ deletedSide G u v v from Reachable.rfl)) hs

/-- Targets already forced by the root have no effect on the rooted count. -/
theorem rooted_targets_root (s : Set V) (hs : s ⊆ {r}) :
    Nat.card (RootedWithin G S r s) = Nat.card (RootedWithin G S r (∅ : Set V)) := by
  rw [rooted_within_count, rooted_within_count]
  congr 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_empty_iff_false, or_false]
  constructor
  · rintro (hh | hh)
    · exact hh
    · exact Set.mem_singleton_iff.mp (hs hh)
  · exact Or.inl

theorem rooted_singleton_comm (x y : V) :
    Nat.card (RootedWithin G S x {y}) = Nat.card (RootedWithin G S y {x}) := by
  rw [rooted_within_count, rooted_within_count, Set.pair_comm]

/-- A connected subgraph crossing a sole exit must contain the exit vertex. -/
theorem containing_root_of_cross (s : Set V) (x y : V) (hx : x ∈ s) (hy : y ∈ s)
    (hxs : x ∈ S) (hys : y ∉ S)
    (hexit : ∀ a b, G.Adj a b → a ∈ S → b ∉ S → a = r) :
    countContaining G s = Nat.card (RootedWithin G Set.univ r s) := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro K
  constructor
  · rintro ⟨hK, hs⟩
    refine ⟨hK, ?_, hs, Set.subset_univ _⟩
    by_contra hr
    exact hys (verts_subset_of_root_absent K S r hK hr x (hs hx) hxs hexit (hs hy))
  · exact fun hh => ⟨hh.1, hh.2.2.1⟩


abbrev rootedCount (G : SimpleGraph V) (S : Set V) (r : V) (s : Set V) :=
  Nat.card (RootedWithin G S r s)
abbrev rootlessCount (G : SimpleGraph V) (S : Set V) (r : V) (s : Set V) :=
  Nat.card (RootlessWithin G S r s)

theorem rooted_count_iso_induce (hr : r ∈ S) (x : V) (hx : x ∈ S) :
    rootedCount G S r {x} = pairCount (G.induce S) ⟨r, hr⟩ ⟨x, hx⟩ := by
  dsimp only [rootedCount]
  rw [rooted_within_count, within_induce_count _ (Set.insert_subset hr (Set.singleton_subset_iff.mpr hx)), pairCount]
  congr 1
  ext z
  simp [Set.mem_insert_iff, Set.mem_preimage, Subtype.ext_iff]

theorem rooted_count_empty_induce (hr : r ∈ S) :
    rootedCount G S r ∅ = pairCount (G.induce S) ⟨r, hr⟩ ⟨r, hr⟩ := by
  rw [← rooted_count_iso_induce hr r hr]
  exact (rooted_targets_root {r} (Set.Subset.refl _)).symm

/-- The induced original graph on each deletion component is its connected deletion graph. -/
theorem bridge_component_induce [Finite V] {u v : V} (h : QualifyingBridge G u v) :
    G.induce (deletedSide G u v u) =
      (G.deleteEdges {s(u, v)}).induce (deletedSide G u v u) := by
  ext x y
  change G.Adj x.val y.val ↔ (G.deleteEdges {s(u, v)}).Adj x.val y.val
  rw [deleteEdges_adj]
  constructor
  · intro hxy
    refine ⟨hxy, ?_⟩
    intro he
    have he : s(x.val, y.val) = s(u, v) := Set.mem_singleton_iff.mp he
    have hd := (qualifying_components h).2.2.1
    rcases Sym2.eq_iff.mp he with he | he
    · have hy' := y.property
      rw [he.2] at hy'
      exact Set.disjoint_left.mp hd hy' Reachable.rfl
    · have hx' := x.property
      rw [he.1] at hx'
      exact Set.disjoint_left.mp hd hx' Reachable.rfl
  · exact And.left

theorem bridge_component_connected [Finite V] {u v : V} (h : QualifyingBridge G u v) :
    (G.induce (deletedSide G u v u)).Connected := by
  rw [bridge_component_induce h]
  exact (qualifying_components h).2.2.2.1

/-- Native local rooted minima have a positive value, strict singleton exclusion, and a witness. -/
theorem local_root_minimum [Finite V] (hr : r ∈ S) (hconn : (G.induce S).Connected)
    (hne : ∃ x ∈ S, x ≠ r) :
    ∃ p : ℕ, 0 < p ∧ p < rootedCount G S r ∅ ∧ 2 ≤ rootedCount G S r ∅ ∧
      (∀ x ∈ S, x ≠ r → p ≤ rootedCount G S r {x}) ∧
      (∃ x ∈ S, x ≠ r ∧ rootedCount G S r {x} = p) := by
  let rr : S := ⟨r, hr⟩
  have hn : ∃ x : S, x ≠ rr := by
    obtain ⟨x, hx, hxr⟩ := hne
    exact ⟨⟨x, hx⟩, fun he => hxr (congrArg Subtype.val he)⟩
  obtain ⟨hp, hpa, ha⟩ := rootMinimum_bounds hconn rr hn
  refine ⟨rootMinimum (G.induce S) rr, hp, ?_, ?_, ?_, ?_⟩
  · simpa only [rooted_count_empty_induce hr] using hpa
  · simpa only [rooted_count_empty_induce hr] using ha
  · intro x hx hxr
    rw [rooted_count_iso_induce hr x hx]
    apply csInf_le'
    exact ⟨⟨x, hx⟩, fun he => hxr (congrArg Subtype.val he), rfl⟩
  · obtain ⟨x, hx, he⟩ := rootMinimum_attained (G.induce S) rr hn
    exact ⟨x.val, x.property, fun hh => hx (Subtype.ext hh),
      (rooted_count_iso_induce hr x.val x.property).trans he⟩

/-- Every finite connected component supplies actual local subgraphs for arbitrary targets. -/
theorem local_rooted_pos [Finite V] (hr : r ∈ S) (hconn : (G.induce S).Connected)
    (s : Set V) (hs : s ⊆ S) : 0 < rootedCount G S r s := by
  dsimp only [rootedCount]
  rw [rooted_within_count, within_induce_count _ (Set.insert_subset hr hs)]
  exact countContaining_pos hconn _


theorem rooted_univ_singleton (x y : V) :
    rootedCount G Set.univ x {y} = pairCount G x y := by
  dsimp only [rootedCount]
  rw [rooted_within_count, within_univ_count]
  rfl

theorem shift_left_rooted_count [Finite V] {u v : V} (h : QualifyingBridge G u v)
    (s : Set V) (hs : s ⊆ deletedSide G u v u) :
    rootedCount G (deletedSide G u v u) u s =
      rootedCount (bridgeShift G u v) (deletedSide G u v u) u s := by
  dsimp only [rootedCount]
  rw [rooted_within_count, rooted_within_count]
  exact shift_left_within_count h _ (Set.insert_subset Reachable.rfl hs)

theorem shift_left_rootless_count [Finite V] {u v : V} (h : QualifyingBridge G u v)
    (s : Set V) (hs : s ⊆ deletedSide G u v u) :
    rootlessCount G (deletedSide G u v u) u s =
      rootlessCount (bridgeShift G u v) (deletedSide G u v u) u s := by
  have hw := shift_left_within_count h s hs
  rw [within_count_partition _ _ _ u, within_count_partition _ _ _ u] at hw
  have hr := shift_left_rooted_count h s hs
  dsimp only [rootedCount] at hr
  dsimp only [rootlessCount]
  omega

theorem shift_right_empty_count [Finite V] {u v : V} (h : QualifyingBridge G u v) :
    rootedCount (bridgeShift G u v) (insert u (deletedSide G u v v)) u ∅ =
      2 * rootedCount G (deletedSide G u v v) v ∅ := by
  obtain ⟨hr, hl, he, hnbr, hexit⟩ := bridge_pendant_data h
  have ht := shift_right_rooted_count h ∅ (Set.empty_subset _)
  simp only [Set.image_empty] at ht
  dsimp only [rootedCount]
  rw [← ht]
  exact pendant_base_count hr hl he hnbr hexit ∅ (Set.empty_subset _)

/-- Exact same-side counts in the original graph, with a separate rootless term. -/
theorem bridge_same_side_count [Finite V] {u v : V} (h : QualifyingBridge G u v)
    (s : Set V) (hs : s ⊆ deletedSide G u v u) (hne : s.Nonempty) :
    countContaining G s = rootlessCount G (deletedSide G u v u) u s +
      rootedCount G (deletedSide G u v u) u s *
        (1 + rootedCount G (deletedSide G u v v) v ∅) := by
  have sep := bridge_separation h
  have hi : s ∩ insert u (deletedSide G u v v) ⊆ {u} := by
    intro x hx
    exact Set.mem_singleton_iff.mpr (sep.inter x (hs hx.1) hx.2)
  rw [sep.within_count s hs hne, rooted_targets_root _ hi, bridge_pendant_root_count h]

/-- The transformed same-side rooted term is multiplied by twice the other rooted count. -/
theorem shift_same_side_count [Finite V] {u v : V} (h : QualifyingBridge G u v)
    (s : Set V) (hs : s ⊆ deletedSide G u v u) (hne : s.Nonempty) :
    countContaining (bridgeShift G u v) s = rootlessCount G (deletedSide G u v u) u s +
      rootedCount G (deletedSide G u v u) u s *
        (2 * rootedCount G (deletedSide G u v v) v ∅) := by
  have sep := shift_separation h
  have hi : s ∩ insert u (deletedSide G u v v) ⊆ {u} := by
    intro x hx
    exact Set.mem_singleton_iff.mpr (sep.inter x (hs hx.1) hx.2)
  rw [sep.within_count s hs hne, rooted_targets_root _ hi]
  change _ = _
  rw [show Nat.card (RootlessWithin (bridgeShift G u v) (deletedSide G u v u) u s) =
    rootlessCount G (deletedSide G u v u) u s from (shift_left_rootless_count h s hs).symm]
  rw [show Nat.card (RootedWithin (bridgeShift G u v) (deletedSide G u v u) u s) =
    rootedCount G (deletedSide G u v u) u s from (shift_left_rooted_count h s hs).symm]
  exact congrArg (fun n => rootlessCount G (deletedSide G u v u) u s +
    rootedCount G (deletedSide G u v u) u s * n) (shift_right_empty_count h)

/-- Root pair counts on the first component, including its root itself. -/
theorem bridge_root_pair_left [Finite V] {u v x : V} (h : QualifyingBridge G u v)
    (hx : x ∈ deletedSide G u v u) :
    pairCount G u x = rootedCount G (deletedSide G u v u) u {x} *
      (1 + rootedCount G (deletedSide G u v v) v ∅) := by
  have sep := bridge_separation h
  have hi : ({x} : Set V) ∩ insert u (deletedSide G u v v) ⊆ {u} := by
    intro y hy
    exact Set.mem_singleton_iff.mpr (sep.inter y (Set.mem_singleton_iff.mp hy.1 ▸ hx) hy.2)
  rw [← rooted_univ_singleton]
  dsimp only [rootedCount]
  rw [sep.rooted_count,
    Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hx),
    rooted_targets_root _ hi, bridge_pendant_root_count h]

theorem shift_root_pair_left [Finite V] {u v x : V} (h : QualifyingBridge G u v)
    (hx : x ∈ deletedSide G u v u) :
    pairCount (bridgeShift G u v) u x = rootedCount G (deletedSide G u v u) u {x} *
      (2 * rootedCount G (deletedSide G u v v) v ∅) := by
  have sep := shift_separation h
  have hi : ({x} : Set V) ∩ insert u (deletedSide G u v v) ⊆ {u} := by
    intro y hy
    exact Set.mem_singleton_iff.mpr (sep.inter y (Set.mem_singleton_iff.mp hy.1 ▸ hx) hy.2)
  rw [← rooted_univ_singleton]
  dsimp only [rootedCount]
  rw [sep.rooted_count,
    Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hx), rooted_targets_root _ hi]
  change _ = _
  rw [show Nat.card (RootedWithin (bridgeShift G u v) (deletedSide G u v u) u {x}) =
    rootedCount G (deletedSide G u v u) u {x} from
      (shift_left_rooted_count h {x} (Set.singleton_subset_iff.mpr hx)).symm]
  exact congrArg (fun n => rootedCount G (deletedSide G u v u) u {x} * n)
    (shift_right_empty_count h)


theorem rooted_targets_eq (s t : Set V) (he : insert r s = insert r t) :
    rootedCount G S r s = rootedCount G S r t := by
  dsimp only [rootedCount]
  rw [rooted_within_count, rooted_within_count, he]

/-- Cross-side pair counts in an actual single-root union. -/
theorem separation_pair_cross [Finite V] {T : Set V} (h : RootSeparation G S T r)
    (x y : V) (hx : x ∈ S) (hy : y ∈ T) (hyn : y ∉ S) :
    pairCount G x y = rootedCount G S r {x} * rootedCount G T r {y} := by
  rw [pairCount, containing_root_of_cross {x, y} x y (by simp) (by simp) hx hyn h.exit,
    h.rooted_count]
  have hs : ({x, y} : Set V) ∩ S = {x} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hh | hh, hz⟩
      · exact hh
      · exact False.elim (hyn (hh ▸ hz))
    · intro hh; subst z; exact ⟨Or.inl rfl, hx⟩
  rw [hs]
  apply congrArg (fun n => rootedCount G S r {x} * n)
  apply rooted_targets_eq
  ext z
  simp only [Set.mem_insert_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro (hz | ⟨hz | hz, ht⟩)
    · exact Or.inl hz
    · subst z; exact Or.inl (h.inter x hx ht)
    · exact Or.inr hz
  · rintro (hz | hz)
    · exact Or.inl hz
    · subst z; exact Or.inr ⟨Or.inr rfl, hy⟩

/-- Exact crossing-bridge count for every pair of vertices on opposite deletion components. -/
theorem bridge_pair_cross [Finite V] {u v x y : V} (h : QualifyingBridge G u v)
    (hx : x ∈ deletedSide G u v u) (hy : y ∈ deletedSide G u v v) :
    pairCount G x y = rootedCount G (deletedSide G u v u) u {x} *
      rootedCount G (deletedSide G u v v) v {y} := by
  have hyn : y ∉ deletedSide G u v u := fun hh =>
    Set.disjoint_left.mp (qualifying_components h).2.2.1 hh hy
  rw [separation_pair_cross (bridge_separation h) x y hx (Set.mem_insert_of_mem _ hy) hyn]
  congr 1
  exact bridge_pendant_targets_count h {y} (Set.singleton_subset_iff.mpr hy) (Set.singleton_nonempty y)

theorem shift_right_pair_factor [Finite V] {u v y : V} (h : QualifyingBridge G u v)
    (hy : y ∈ deletedSide G u v v) (hyv : y ≠ v) :
    rootedCount (bridgeShift G u v) (insert u (deletedSide G u v v)) u {y} =
      2 * rootedCount G (deletedSide G u v v) v {y} := by
  have hyu : y ≠ u := fun he => (bridge_pendant_data h).2.1 (he ▸ hy)
  have ht := shift_right_rooted_count h {y} (by simp [hy])
  simp only [Set.image_singleton, Equiv.swap_apply_of_ne_of_ne hyu hyv] at ht
  dsimp only [rootedCount]
  rw [← ht]
  obtain ⟨hr, hl, he, hnbr, hexit⟩ := bridge_pendant_data h
  exact pendant_base_count hr hl he hnbr hexit {y} (Set.singleton_subset_iff.mpr hy)

/-- Cross-side counts after contraction, away from the newly attached leaf. -/
theorem shift_pair_cross [Finite V] {u v x y : V} (h : QualifyingBridge G u v)
    (hx : x ∈ deletedSide G u v u) (hy : y ∈ deletedSide G u v v) (hyv : y ≠ v) :
    pairCount (bridgeShift G u v) x y = rootedCount G (deletedSide G u v u) u {x} *
      (2 * rootedCount G (deletedSide G u v v) v {y}) := by
  have hyn : y ∉ deletedSide G u v u := fun hh =>
    Set.disjoint_left.mp (qualifying_components h).2.2.1 hh hy
  rw [separation_pair_cross (shift_separation h) x y hx (Set.mem_insert_of_mem _ hy) hyn]
  rw [← shift_left_rooted_count h {x} (Set.singleton_subset_iff.mpr hx), shift_right_pair_factor h hy hyv]

/-- The fresh-leaf target has only one pendant-edge choice, not two. -/
theorem shift_right_leaf_factor [Finite V] {u v : V} (h : QualifyingBridge G u v) :
    rootedCount (bridgeShift G u v) (insert u (deletedSide G u v v)) u {v} =
      rootedCount G (deletedSide G u v v) v ∅ := by
  have ht := shift_right_rooted_count h {u} (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  simp only [Set.image_singleton, Equiv.swap_apply_left] at ht
  dsimp only [rootedCount]
  rw [← ht, rooted_singleton_comm]
  rw [bridge_pendant_targets_count h {v} (Set.singleton_subset_iff.mpr Reachable.rfl)
    (Set.singleton_nonempty v)]
  exact rooted_targets_root {v} (Set.Subset.refl _)

/-- Counts against the fresh leaf, including the identified root as source. -/
theorem shift_pair_leaf [Finite V] {u v x : V} (h : QualifyingBridge G u v)
    (hx : x ∈ deletedSide G u v u) :
    pairCount (bridgeShift G u v) x v = rootedCount G (deletedSide G u v u) u {x} *
      rootedCount G (deletedSide G u v v) v ∅ := by
  have hvn : v ∉ deletedSide G u v u := fun hh =>
    Set.disjoint_left.mp (qualifying_components h).2.2.1 hh Reachable.rfl
  rw [separation_pair_cross (shift_separation h) x v hx
    (Set.mem_insert_of_mem _ Reachable.rfl) hvn]
  rw [← shift_left_rooted_count h {x} (Set.singleton_subset_iff.mpr hx), shift_right_leaf_factor h]


/-- Choosing the other endpoint as the contraction name merely swaps the two endpoint labels. -/
theorem bridgeShift_swap_adj (u v : V) (huv : u ≠ v) (x y : V) :
    (bridgeShift G u v).Adj x y ↔
      (bridgeShift G v u).Adj (Equiv.swap u v x) (Equiv.swap u v y) := by
  by_cases hxu : x = u <;> by_cases hxv : x = v <;>
    by_cases hyu : y = u <;> by_cases hyv : y = v <;>
    simp [Equiv.swap_apply_def, hxu, hxv, hyu, hyv, bridgeShift,
      huv, huv.symm, adj_comm] <;> simp_all [ne_comm, or_comm]

def bridgeShiftSwapIso (u v : V) (huv : u ≠ v) : bridgeShift G u v ≃g bridgeShift G v u where
  toEquiv := Equiv.swap u v
  map_rel_iff' := fun {x y} => (bridgeShift_swap_adj u v huv x y).symm

/-- Every non-root source on the first component improves against every new target,
including self, the identified root, the opposite component, and the fresh leaf. -/
theorem shift_left_all_targets [Finite V] {u v x : V} (h : QualifyingBridge G u v)
    (hx : x ∈ deletedSide G u v u) (_hxu : x ≠ u) :
    ∀ y, eccentricity G x < pairCount (bridgeShift G u v) x y := by
  have hp := qualifying_components h
  have hconn := bridge_component_connected h
  have hconnB : (G.induce (deletedSide G u v v)).Connected := by
    have hh := bridge_component_connected (qualifyingBridge_swap h)
    rw [deletedSide_swap (G := G) u v v] at hh
    exact hh
  obtain ⟨q, hq, hqb, hb, hqall, z, hz, hzv, hzq⟩ :=
    local_root_minimum (show v ∈ deletedSide G u v v from Reachable.rfl) hconnB hp.2.2.2.2.2.2
  have hU : 0 < rootedCount G (deletedSide G u v u) u {x} :=
    local_rooted_pos Reachable.rfl hconn {x} (Set.singleton_subset_iff.mpr hx)
  intro y
  by_cases hyv : y = v
  · subst y
    apply lt_of_le_of_lt (eccentricity_le_pairCount G x z)
    rw [bridge_pair_cross h hx hz, shift_pair_leaf h hx, hzq]
    exact Nat.mul_lt_mul_of_pos_left hqb hU
  · rcases hp.2.1 y with hy | hy
    · apply lt_of_le_of_lt (eccentricity_le_pairCount G x y)
      change countContaining G {x, y} < countContaining (bridgeShift G u v) {x, y}
      have hs : ({x, y} : Set V) ⊆ deletedSide G u v u := by
        intro z hz; rcases hz with rfl | hz
        · exact hx
        · exact Set.mem_singleton_iff.mp hz ▸ hy
      rw [bridge_same_side_count h {x, y} hs (Set.insert_nonempty _ _),
        shift_same_side_count h {x, y} hs (Set.insert_nonempty _ _)]
      have hQ := local_rooted_pos Reachable.rfl hconn {x, y} hs
      nlinarith
    · apply lt_of_le_of_lt (eccentricity_le_pairCount G x y)
      rw [bridge_pair_cross h hx hy, shift_pair_cross h hx hy hyv]
      have hV := local_rooted_pos (show v ∈ deletedSide G u v v from Reachable.rfl)
        hconnB {y} (Set.singleton_subset_iff.mpr hy)
      nlinarith

/-- Taking an attained minimum preserves the strict comparison against every new target. -/
theorem shift_left_eccentricity_strict [Finite V] {u v x : V} (h : QualifyingBridge G u v)
    (hx : x ∈ deletedSide G u v u) (hxu : x ≠ u) :
    eccentricity G x < eccentricity (bridgeShift G u v) x := by
  obtain ⟨y, hy⟩ := eccentricity_attained (bridgeShift G u v) x
  rw [← hy]
  exact shift_left_all_targets h hx hxu y

/-- The same proof applies to the opposite component via the endpoint-label isomorphism. -/
theorem shift_nonendpoint_strict [Finite V] {u v x : V} (h : QualifyingBridge G u v)
    (hxu : x ≠ u) (hxv : x ≠ v) :
    eccentricity G x < eccentricity (bridgeShift G u v) x := by
  rcases (qualifying_components h).2.1 x with hx | hx
  · exact shift_left_eccentricity_strict h hx hxu
  · have hh := shift_left_eccentricity_strict (qualifyingBridge_swap h)
      (by simpa only [deletedSide_swap] using hx) hxv
    have hi := eccentricity_iso (bridgeShiftSwapIso (G := G) u v (qualifying_components h).1.ne) x
    change eccentricity (bridgeShift G u v) x =
      eccentricity (bridgeShift G v u) (Equiv.swap u v x) at hi
    rw [Equiv.swap_apply_of_ne_of_ne hxu hxv] at hi
    exact hh.trans_eq hi.symm

end
end D5.S3.Combinatorics.Graph.Eccentric.DePatraCounting
