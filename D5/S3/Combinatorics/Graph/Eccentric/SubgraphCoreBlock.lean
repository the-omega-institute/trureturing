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
  H.Connected ∧ ∀ z : V, (H.induce ({z}ᶜ : Set V)).Preconnected

/-- A native block is maximal among connected subgraphs without cut vertices. -/
def NativeBlock (H : G.Subgraph) : Prop := Maximal NoCut H

private lemma attachment [Finite V] (hG : G.Connected) (H : G.Subgraph)
    (hH : H.Connected) (r x : V) (hr : r ∉ H.verts) (hx : x ∈ H.verts) :
    ∃ K L : G.Subgraph, K.Connected ∧ L.Connected ∧
      r ∈ K.verts ∧ x ∈ K.verts ∧ r ∈ L.verts ∧ x ∉ L.verts ∧
      K.induce (L.vertsᶜ) = H := by
  classical
  letI := Fintype.ofFinite V
  obtain ⟨p, hp⟩ := hG.exists_isPath r x
  obtain ⟨y, hy, hyp, hfirst⟩ :=
    p.exists_mem_support_forall_mem_support_imp_eq H.verts.toFinset
      ⟨x, by simpa using hx, p.end_mem_support⟩
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
    simpa using (List.nodup_append.mp hd).2.2
  have hLH : ∀ z ∈ L.verts, z ∉ H.verts := by
    intro z hz hzH
    have hzq : z ∈ q.support := by
      rw [← hsplit]
      exact List.mem_append_left _ (Walk.mem_verts_toSubgraph.mp hz)
    have he : z = y := hfirst z (by simpa using hzH) hzq
    exact hyL (he ▸ hz)
  have hqv : ∀ z ∈ q.toSubgraph.verts, z ∈ L.verts ∨ z = y := by
    intro z hz
    have hz' := Walk.mem_verts_toSubgraph.mp hz
    rw [← hsplit, List.mem_append, List.mem_singleton] at hz'
    exact hz'.imp (fun h => Walk.mem_verts_toSubgraph.mpr h) id
  refine ⟨K, L, ?_, q.dropLast.toSubgraph_connected,
    Or.inr (Walk.mem_verts_toSubgraph.mpr q.start_mem_support),
    Or.inl hx, Walk.mem_verts_toSubgraph.mpr q.dropLast.start_mem_support,
    (hLH x · hx), ?_⟩
  · exact Subgraph.connected_sup hH.preconnected q.toSubgraph_connected.preconnected
      ⟨y, hyH, Walk.mem_verts_toSubgraph.mpr q.end_mem_support⟩
  · apply Subgraph.ext
    · ext z
      change ((z ∈ H.verts ∨ z ∈ q.toSubgraph.verts) ∧ z ∉ L.verts) ↔ z ∈ H.verts
      constructor
      · rintro ⟨hz | hz, hn⟩
        · exact hz
        · exact (hqv z hz).elim (fun h => False.elim (hn h)) (fun h => h ▸ hyH)
      · intro hz
        exact ⟨Or.inl hz, fun h => hLH z h hz⟩
    · funext a b
      apply propext
      change ((a ∉ L.verts ∧ b ∉ L.verts) ∧
        (H.Adj a b ∨ q.toSubgraph.Adj a b)) ↔ H.Adj a b
      constructor
      · rintro ⟨⟨ha, hb⟩, hab | hab⟩
        · exact hab
        · have ea : a = y := (hqv a hab.fst_mem).resolve_left ha
          have eb : b = y := (hqv b hab.snd_mem).resolve_left hb
          exact False.elim (q.toSubgraph.loopless a (eb.symm ▸ ea ▸ hab))
      · intro hab
        exact ⟨⟨fun h => hLH a h hab.fst_mem, fun h => hLH b h hab.snd_mem⟩,
          Or.inl hab⟩

private abbrev Both (G : SimpleGraph V) (r x : V) :=
  {K : G.Subgraph // K.Connected ∧ r ∈ K.verts ∧ x ∈ K.verts}
private abbrev Only (G : SimpleGraph V) (r x : V) :=
  {K : G.Subgraph // K.Connected ∧ r ∈ K.verts ∧ x ∉ K.verts}

private lemma only_le_product [Finite V] (hG : G.Connected) (r x : V) :
    Nat.card (Only G x r) ≤ Nat.card (Both G r x) * Nat.card (Only G r x) := by
  have hex (H : Only G x r) : ∃ P : Both G r x × Only G r x,
      P.1.val.induce (P.2.val.vertsᶜ) = H.val := by
    obtain ⟨K, L, hK, hL, hrK, hxK, hrL, hxL, he⟩ :=
      attachment hG H.val H.property.1 r x H.property.2.2 H.property.2.1
    exact ⟨⟨⟨K, hK, hrK, hxK⟩, ⟨L, hL, hrL, hxL⟩⟩, he⟩
  choose f hf using hex
  have hi : Function.Injective f := by
    intro H J he
    apply Subtype.ext
    rw [← hf H, ← hf J, he]
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hi

end
end D5.S3.Combinatorics.Graph.Eccentric.SubgraphCoreBlock
