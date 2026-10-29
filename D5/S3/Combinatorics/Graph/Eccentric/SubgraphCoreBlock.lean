/- GID: D5/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Eccentric/SubgraphCoreBlock
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The entire subgraph core lies in one maximal connected subgraph without cut vertices. -/
import D5.S3.Combinatorics.Graph.Eccentric.DePatraCounting
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Eccentric.SubgraphCoreBlock

open SimpleGraph DePatraBridge DePatraCounting Classical
noncomputable section
variable {V : Type} {G : SimpleGraph V}

/-- The native number counts actual connected subgraphs, retaining their edges. -/
def subgraphNumber (G : SimpleGraph V) (v : V) : ℕ := countContaining G {v}

/-- Every maximizing vertex is included. -/
def subgraphCore (G : SimpleGraph V) : Set V :=
  {v | ∀ w, subgraphNumber G w ≤ subgraphNumber G v}

/-- Empty deletion is preconnected: it has no pair of disconnected remaining vertices. -/
def NoCut (H : G.Subgraph) : Prop :=
  H.Connected ∧ ∀ z : V, (restrict H ({z}ᶜ : Set V)).Preconnected

/-- A native block is maximal among connected subgraphs without cut vertices. -/
def NativeBlock (H : G.Subgraph) : Prop := Maximal NoCut H

private lemma attachment [Finite V] (hG : G.Connected) (H : G.Subgraph)
    (hH : H.Connected) (r x : V) (hr : r ∉ H.verts) (hx : x ∈ H.verts) :
    ∃ K L : G.Subgraph, K.Connected ∧ L.Connected ∧
      r ∈ K.verts ∧ x ∈ K.verts ∧ r ∈ L.verts ∧ x ∉ L.verts ∧
      restrict K (L.vertsᶜ) = H := by
  classical
  letI := Fintype.ofFinite V
  obtain ⟨p, hp⟩ := hG.exists_isPath r x
  obtain ⟨y, hy, hyp, hfirst⟩ :=
    p.exists_mem_support_forall_mem_support_imp_eq H.verts.toFinset
      (by exact ⟨x, Finset.mem_filter.mpr ⟨by simpa using hx, p.end_mem_support⟩⟩)
  have hyH : y ∈ H.verts := by simpa using hy
  let q := p.takeUntil y hyp
  have hq : q.IsPath := hp.takeUntil hyp
  have hn : ¬ q.Nil := fun he => hr (he.eq ▸ hyH)
  let L := q.dropLast.toSubgraph
  let K := H ⊔ q.toSubgraph
  have hsplit : q.dropLast.support ++ [y] = q.support := q.support_dropLast_concat hn
  have hyL : y ∉ L.verts := by
    change y ∉ q.dropLast.toSubgraph.verts
    rw [Walk.mem_verts_toSubgraph, q.support_dropLast hn]
    have hd := hq.support_nodup
    rw [← q.dropLast_support_concat] at hd
    intro hy
    have hh : ∀ a ∈ q.support.dropLast, a ≠ y := by simpa using (List.nodup_append.mp hd).2.2
    exact hh y hy rfl
  have hLH : ∀ z ∈ L.verts, z ∉ H.verts := by
    intro z hz hzH
    have hzq : z ∈ q.support := by
      rw [← hsplit]
      exact List.mem_append_left _ ((Walk.mem_verts_toSubgraph _).mp hz)
    have he : z = y := hfirst z (by simpa using hzH) hzq
    exact hyL (he ▸ hz)
  have hqv : ∀ z ∈ q.toSubgraph.verts, z ∈ L.verts ∨ z = y := by
    intro z hz
    have hz' := (Walk.mem_verts_toSubgraph _).mp hz
    rw [← hsplit, List.mem_append, List.mem_singleton] at hz'
    exact hz'.imp (fun h => (Walk.mem_verts_toSubgraph _).mpr h) id
  refine ⟨K, L, ?_, q.dropLast.toSubgraph_connected,
    Or.inr ((Walk.mem_verts_toSubgraph _).mpr q.start_mem_support),
    Or.inl hx, (Walk.mem_verts_toSubgraph _).mpr q.dropLast.start_mem_support,
    (hLH x · hx), ?_⟩
  · exact Subgraph.connected_sup hH.preconnected q.toSubgraph_connected.preconnected
      ⟨y, hyH, (Walk.mem_verts_toSubgraph _).mpr q.end_mem_support⟩
  · apply Subgraph.ext
    · ext z
      simp only [restrict, Subgraph.induce_verts, Set.mem_inter_iff, Set.mem_compl_iff, K,
        Subgraph.verts_sup, Set.mem_union]
      constructor
      · rintro ⟨hz | hz, hn⟩
        · exact hz
        · exact (hqv z hz).elim (fun h => False.elim (hn h)) (fun h => h ▸ hyH)
      · intro hz
        exact ⟨Or.inl hz, fun h => hLH z h hz⟩
    · funext a b
      apply propext
      simp only [restrict, Subgraph.induce_adj, Set.mem_inter_iff, Set.mem_compl_iff,
        K, Subgraph.verts_sup, Set.mem_union, Subgraph.sup_adj]
      constructor
      · rintro ⟨⟨_, ha⟩, ⟨_, hb⟩, hab | hab⟩
        · exact hab
        · have ea : a = y := (hqv a hab.fst_mem).resolve_left ha
          have eb : b = y := (hqv b hab.snd_mem).resolve_left hb
          exact False.elim (q.toSubgraph.loopless.irrefl a (by simpa [ea, eb] using hab))
      · intro hab
        exact ⟨⟨Or.inl hab.fst_mem, fun h => hLH a h hab.fst_mem⟩,
          ⟨Or.inl hab.snd_mem, fun h => hLH b h hab.snd_mem⟩, Or.inl hab⟩

private abbrev Both (G : SimpleGraph V) (r x : V) :=
  {K : G.Subgraph // K.Connected ∧ r ∈ K.verts ∧ x ∈ K.verts}
private abbrev Only (G : SimpleGraph V) (r x : V) :=
  {K : G.Subgraph // K.Connected ∧ r ∈ K.verts ∧ x ∉ K.verts}

private lemma only_le_product [Finite V] (hG : G.Connected) (r x : V) :
    Nat.card (Only G x r) ≤ Nat.card (Both G r x) * Nat.card (Only G r x) := by
  have hex (H : Only G x r) : ∃ P : Both G r x × Only G r x,
      restrict P.1.val (P.2.val.vertsᶜ) = H.val := by
    obtain ⟨K, L, hK, hL, hrK, hxK, hrL, hxL, he⟩ :=
      attachment hG H.val H.property.1 r x H.property.2.2 H.property.2.1
    exact ⟨⟨⟨K, hK, hrK, hxK⟩, ⟨L, hL, hrL, hxL⟩⟩, he⟩
  choose f hf using hex
  have hi : Function.Injective f := by
    intro H J he
    apply Subtype.ext
    rw [← hf H, ← hf J, he]
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hi

private lemma both_card (r x : V) : Nat.card (Both G r x) = pairCount G r x := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro K
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
  tauto

private lemma number_partition [Finite V] (r x : V) :
    subgraphNumber G r = Nat.card (Only G r x) + pairCount G r x := by
  rw [subgraphNumber, ← within_univ_count, within_count_partition G Set.univ {r} x]
  congr 1
  · apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro K
    simp only [Set.singleton_subset_iff, Set.subset_univ, and_true]
    tauto
  · rw [rooted_within_count, within_univ_count, Set.pair_comm]
    rfl

private lemma number_induce (S : Set V) (x : V) (hx : x ∈ S) :
    Nat.card (Within G S {x}) = subgraphNumber (G.induce S) ⟨x, hx⟩ := by
  rw [within_induce_count {x} (Set.singleton_subset_iff.mpr hx), subgraphNumber]
  congr 1
  ext z
  simp [Subtype.ext_iff]

private lemma rootless_induce [Finite V] (S : Set V) (r x : V)
    (hr : r ∈ S) (hx : x ∈ S) :
    rootlessCount G S r {x} = Nat.card (Only (G.induce S) ⟨x, hx⟩ ⟨r, hr⟩) := by
  have h₁ := within_count_partition G S {x} r
  rw [number_induce S x hx, rooted_count_iso_induce hr x hx] at h₁
  have h₂ := number_partition (G := G.induce S) ⟨x, hx⟩ ⟨r, hr⟩
  rw [pairCount_symm] at h₂
  omega

private lemma local_bound [Finite V] (S : Set V) (r x : V)
    (hr : r ∈ S) (hx : x ∈ S) (hS : (G.induce S).Connected) :
    rootlessCount G S r {x} ≤
      rootedCount G S r {x} * rootlessCount G S x {r} := by
  rw [rootless_induce S r x hr hx, rootless_induce S x r hx hr,
    rooted_count_iso_induce hr x hx]
  have h := only_le_product hS ⟨r, hr⟩ ⟨x, hx⟩
  rw [both_card] at h
  exact h

private lemma local_partition [Finite V] (S : Set V) (r x : V)
    (hr : r ∈ S) (hx : x ∈ S) :
    rootedCount G S r ∅ = rootlessCount G S x {r} + rootedCount G S r {x} := by
  have h := within_count_partition G S {r} x
  rw [rooted_count_iso_induce hx r hr, pairCount_symm,
    ← rooted_count_iso_induce hr x hx] at h
  rw [rooted_within_count, Set.insert_empty]
  exact h

private lemma side_connected (hG : G.Connected) (S : Set V) (r : V)
    (hr : r ∈ S)
    (he : ∀ a b, G.Adj a b → a ∈ S → b ∉ S → a = r) :
    (G.induce S).Connected := by
  have ht : (⊤ : G.Subgraph).Connected :=
    SimpleGraph.Connected.toSubgraph (G := G) le_rfl hG
  have h := restrict_connected (⊤ : G.Subgraph) S r ht (by trivial) hr he
  apply connected_induce_iff.mpr
  simpa only [restrict, Subgraph.verts_top, Set.univ_inter] using h

private lemma separation_swap {S T : Set V} {r : V}
    (h : RootSeparation G S T r) : RootSeparation G T S r :=
  ⟨h.root_right, h.root_left, fun x => (h.cover x).symm,
    fun x hx hy => h.inter x hy hx,
    fun x y he => (h.edges x y he).symm⟩

private lemma separation_root_number [Finite V] {S T : Set V} {r : V}
    (h : RootSeparation G S T r) :
    subgraphNumber G r = rootedCount G S r ∅ * rootedCount G T r ∅ := by
  have he : subgraphNumber G r = rootedCount G Set.univ r ∅ := by
    rw [rooted_within_count, Set.insert_empty, within_univ_count]
    rfl
  rw [he, h.rooted_count]
  simp

private lemma separation_number [Finite V] {S T : Set V} {r : V}
    (h : RootSeparation G S T r) (x : V) (hx : x ∈ S) :
    subgraphNumber G x = rootlessCount G S r {x} +
      rootedCount G S r {x} * rootedCount G T r ∅ := by
  have hi : ({x} : Set V) ∩ T ⊆ {r} := by
    intro z hz
    have he : z = x := Set.mem_singleton_iff.mp hz.1
    subst z
    exact Set.mem_singleton_iff.mpr (h.inter x hx hz.2)
  exact (h.within_count {x} (Set.singleton_subset_iff.mpr hx) ⟨x, rfl⟩).trans
    (by rw [rooted_targets_root _ hi])

private lemma separation_not_both_max [Finite V] (hG : G.Connected)
    {S T : Set V} {r x y : V} (h : RootSeparation G S T r)
    (hx : x ∈ S) (hy : y ∈ T) (hxr : x ≠ r) (hyr : y ≠ r)
    (hxm : x ∈ subgraphCore G) (hym : y ∈ subgraphCore G) : False := by
  have hs := side_connected hG S r h.root_left h.exit
  have ht := side_connected hG T r h.root_right (separation_swap h).exit
  have hdx := pairCount_lt_root (G.induce S)
    (show (⟨r, h.root_left⟩ : S) ≠ ⟨x, hx⟩ from fun he => hxr (congrArg Subtype.val he).symm)
  have hey := pairCount_lt_root (G.induce T)
    (show (⟨r, h.root_right⟩ : T) ≠ ⟨y, hy⟩ from fun he => hyr (congrArg Subtype.val he).symm)
  rw [← rooted_count_iso_induce h.root_left x hx,
    ← rooted_count_empty_induce h.root_left] at hdx
  rw [← rooted_count_iso_induce h.root_right y hy,
    ← rooted_count_empty_induce h.root_right] at hey
  have hcx := local_bound S r x h.root_left hx hs
  have hcy := local_bound T r y h.root_right hy ht
  have hax := local_partition S r x h.root_left hx
  have hby := local_partition T r y h.root_right hy
  have hmx := hxm r
  have hmy := hym r
  rw [separation_root_number h, separation_number h x hx] at hmx
  rw [separation_root_number h, separation_number (separation_swap h) y hy] at hmy
  have htx : 0 < rootlessCount G S x {r} := by omega
  have hty : 0 < rootlessCount G T y {r} := by omega
  have hb : rootedCount G T r ∅ ≤ rootedCount G S r {x} := by
    by_contra hn
    have hh : rootedCount G S r {x} + 1 ≤ rootedCount G T r ∅ := by omega
    nlinarith
  have ha : rootedCount G S r ∅ ≤ rootedCount G T r {y} := by
    by_contra hn
    have hh : rootedCount G T r {y} + 1 ≤ rootedCount G S r ∅ := by omega
    nlinarith
  omega

end
end D5.S3.Combinatorics.Graph.Eccentric.SubgraphCoreBlock
