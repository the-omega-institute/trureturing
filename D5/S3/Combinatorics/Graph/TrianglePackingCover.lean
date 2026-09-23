/- GID: D5/S3/Combinatorics/Graph/TrianglePackingCover
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/TrianglePackingCover
   mirror-E: none(waiver:graph-parameter-definitions)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: Triangle packing and covering numbers of a finite simple graph. -/

import Mathlib.Combinatorics.SimpleGraph.Clique

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.TrianglePackingCover

open Finset SimpleGraph

variable {α : Type*}

/-- A triangle packing of `G`: triangles that pairwise meet in at most one vertex, which for
distinct three-element sets is exactly sharing no edge. -/
def IsPacking [DecidableEq α] (G : SimpleGraph α) (P : Finset (Finset α)) : Prop :=
  (∀ t ∈ P, G.IsNClique 3 t) ∧ ∀ s ∈ P, ∀ t ∈ P, s ≠ t → (s ∩ t).card ≤ 1

/-- A triangle cover of `G`: a set of edges, each presented as a two-element clique, such that
every triangle contains one of them. Deleting them leaves no triangle. -/
def IsCover (G : SimpleGraph α) (F : Finset (Finset α)) : Prop :=
  (∀ e ∈ F, G.IsNClique 2 e) ∧ ∀ t : Finset α, G.IsNClique 3 t → ∃ e ∈ F, e ⊆ t

/-- The sizes of the triangle packings of `G`. -/
def packingSizes [DecidableEq α] (G : SimpleGraph α) : Set ℕ :=
  {k | ∃ P : Finset (Finset α), IsPacking G P ∧ P.card = k}

/-- The sizes of the triangle covers of `G`. -/
def coverSizes (G : SimpleGraph α) : Set ℕ :=
  {k | ∃ F : Finset (Finset α), IsCover G F ∧ F.card = k}

/-- The maximum number of pairwise edge-disjoint triangles of `G`. -/
noncomputable def nu [DecidableEq α] (G : SimpleGraph α) : ℕ := sSup (packingSizes G)

/-- The least number of edges whose deletion leaves `G` with no triangle. -/
noncomputable def tau (G : SimpleGraph α) : ℕ := sInf (coverSizes G)

/-- Tuza's inequality for a single graph. -/
def TuzaAt [DecidableEq α] (G : SimpleGraph α) : Prop := tau G ≤ 2 * nu G

/-- The empty packing, so the packing sizes are never empty. -/
theorem zero_mem_packingSizes [DecidableEq α] (G : SimpleGraph α) : 0 ∈ packingSizes G :=
  ⟨∅, ⟨fun t ht => absurd ht (notMem_empty t),
    fun s hs => absurd hs (notMem_empty s)⟩, rfl⟩

/-- On a finite vertex type a packing is a set of subsets, so the packing sizes are bounded. -/
theorem packingSizes_bddAbove [DecidableEq α] [Finite α] (G : SimpleGraph α) :
    BddAbove (packingSizes G) := by
  have : Fintype α := Fintype.ofFinite α
  refine ⟨(Finset.univ : Finset (Finset α)).card, ?_⟩
  rintro k ⟨P, -, rfl⟩
  exact card_le_card (subset_univ P)

/-- Every triangle contains an edge, so on a finite vertex type the set of all edges is a cover
and the cover sizes are never empty. -/
theorem coverSizes_nonempty [Finite α] (G : SimpleGraph α) :
    (coverSizes G).Nonempty := by
  classical
  have : Fintype α := Fintype.ofFinite α
  set E : Finset (Finset α) :=
    (Finset.univ : Finset (Finset α)).filter fun e => G.IsNClique 2 e with hE
  refine ⟨E.card, E, ⟨?_, ?_⟩, rfl⟩
  · intro e he
    exact (mem_filter.mp he).2
  · intro t ht
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht.card_eq
    have hadj : G.Adj a b := (is3Clique_triple_iff.mp ht).1
    have hedge : G.IsNClique 2 ({a, b} : Finset α) := by
      refine ⟨?_, ?_⟩
      · rw [Finset.coe_insert, Finset.coe_singleton]
        exact G.isClique_pair.mpr fun _ => hadj
      · rw [Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton]
    refine ⟨{a, b}, mem_filter.mpr ⟨mem_univ _, hedge⟩, ?_⟩
    intro x hx
    simp only [mem_insert, mem_singleton] at hx ⊢
    tauto

/-- In the complete graph every three-element set of vertices is a triangle. -/
theorem isNClique_three_top {t : Finset α} (h : t.card = 3) :
    (⊤ : SimpleGraph α).IsNClique 3 t :=
  ⟨fun _ _ _ _ hxy => by simpa using hxy, h⟩

/-- The complete graph on four vertices has no two edge-disjoint triangles. -/
theorem nu_top_fin_four : nu (⊤ : SimpleGraph (Fin 4)) = 1 := by
  have hmem : (1 : ℕ) ∈ packingSizes (⊤ : SimpleGraph (Fin 4)) := by
    refine ⟨{({0, 1, 2} : Finset (Fin 4))}, ⟨?_, ?_⟩, rfl⟩
    · intro t ht
      rw [Finset.mem_singleton] at ht
      subst ht
      exact isNClique_three_top (by decide)
    · intro s hs t ht hst
      rw [Finset.mem_singleton] at hs ht
      exact absurd (hs.trans ht.symm) hst
  have hub : ∀ k ∈ packingSizes (⊤ : SimpleGraph (Fin 4)), k ≤ 1 := by
    rintro k ⟨P, ⟨hTri, hDisj⟩, rfl⟩
    rw [Finset.card_le_one]
    intro s hs t ht
    by_contra hst
    have hs3 : s.card = 3 := (hTri s hs).card_eq
    have ht3 : t.card = 3 := (hTri t ht).card_eq
    have hu : (s ∪ t).card ≤ 4 := by simpa using Finset.card_le_univ (s ∪ t)
    have hiu := Finset.card_inter_add_card_union s t
    have hle := hDisj s hs t ht hst
    omega
  exact le_antisymm (csSup_le ⟨1, hmem⟩ hub)
    (le_csSup (packingSizes_bddAbove _) hmem)

/-- Two edges are needed to meet every triangle of the complete graph on four vertices, so the
inequality is tight there. -/
theorem tau_top_fin_four : tau (⊤ : SimpleGraph (Fin 4)) = 2 := by
  have hpair : ∀ a b : Fin 4, a ≠ b →
      (⊤ : SimpleGraph (Fin 4)).IsNClique 2 ({a, b} : Finset (Fin 4)) := by
    intro a b hab
    refine ⟨?_, ?_⟩
    · rw [Finset.coe_insert, Finset.coe_singleton]
      exact SimpleGraph.isClique_pair.mpr fun _ => by simpa using hab
    · rw [Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton]
  have hmem : (2 : ℕ) ∈ coverSizes (⊤ : SimpleGraph (Fin 4)) := by
    refine ⟨{({0, 1} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4))}, ⟨?_, ?_⟩, by decide⟩
    · intro e he
      rw [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact hpair 0 1 (by decide)
      · exact hpair 2 3 (by decide)
    · intro t ht
      have hsplit : ∀ u : Finset (Fin 4), u.card = 3 →
          ({0, 1} : Finset (Fin 4)) ⊆ u ∨ ({2, 3} : Finset (Fin 4)) ⊆ u := by decide
      rcases hsplit t ht.card_eq with h | h
      · exact ⟨{0, 1}, by simp, h⟩
      · exact ⟨{2, 3}, by simp, h⟩
  have hlb : ∀ k ∈ coverSizes (⊤ : SimpleGraph (Fin 4)), 2 ≤ k := by
    rintro k ⟨F, ⟨hE, hcov⟩, rfl⟩
    by_contra hlt
    have hcard : F.card ≤ 1 := by omega
    rcases Finset.eq_empty_or_nonempty F with rfl | ⟨e₀, he₀⟩
    · obtain ⟨e, he, -⟩ := hcov {0, 1, 2} (isNClique_three_top (by decide))
      exact absurd he (Finset.notMem_empty e)
    · have hF : F = {e₀} :=
        Finset.eq_singleton_iff_unique_mem.mpr
          ⟨he₀, fun x hx => Finset.card_le_one.mp hcard x hx e₀ he₀⟩
      have he₀card : e₀.card = 2 := (hE e₀ he₀).card_eq
      obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < e₀.card)
      have hterase : ((Finset.univ : Finset (Fin 4)).erase a).card = 3 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ a)]
        simp
      obtain ⟨e, he, hsub⟩ := hcov _ (isNClique_three_top hterase)
      rw [hF, Finset.mem_singleton] at he
      subst he
      exact absurd (hsub ha) (Finset.notMem_erase a _)
  exact le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨2, hmem⟩ hlb)

/-- The classical bound: the edges of a maximum packing already meet every triangle, because a
triangle disjoint from all of them could be added to the packing. -/
theorem tau_le_three_mul_nu [DecidableEq α] [Finite α] (G : SimpleGraph α) :
    tau G ≤ 3 * nu G := by
  have : Fintype α := Fintype.ofFinite α
  obtain ⟨P, hP, hPcard⟩ :=
    Nat.sSup_mem ⟨0, zero_mem_packingSizes G⟩ (packingSizes_bddAbove G)
  set F : Finset (Finset α) := P.biUnion (fun t => t.powersetCard 2) with hF
  have hedge : ∀ e ∈ F, G.IsNClique 2 e := by
    intro e he
    rw [hF, Finset.mem_biUnion] at he
    obtain ⟨t, htP, het⟩ := he
    rw [Finset.mem_powersetCard] at het
    exact ⟨(hP.1 t htP).1.subset (Finset.coe_subset.mpr het.1), het.2⟩
  have hmeet : ∀ t₀ : Finset α, G.IsNClique 3 t₀ →
      ∃ t ∈ P, 2 ≤ (t₀ ∩ t).card := by
    intro t₀ ht₀
    by_contra hcon
    have hsmall : ∀ t ∈ P, (t₀ ∩ t).card ≤ 1 := by
      intro t ht
      by_contra hle
      exact hcon ⟨t, ht, by omega⟩
    have hnot : t₀ ∉ P := by
      intro hmem
      have h1 := hsmall t₀ hmem
      rw [Finset.inter_self, ht₀.card_eq] at h1
      omega
    have hbig : IsPacking G (insert t₀ P) := by
      refine ⟨?_, ?_⟩
      · intro t ht
        rcases Finset.mem_insert.mp ht with rfl | htP
        · exact ht₀
        · exact hP.1 t htP
      · intro s hs t ht hst
        have hs' := Finset.mem_insert.mp hs
        have ht' := Finset.mem_insert.mp ht
        rcases hs' with rfl | hsP
        · rcases ht' with rfl | htP
          · exact absurd rfl hst
          · exact hsmall t htP
        · rcases ht' with rfl | htP
          · have h2 := hsmall s hsP
            rwa [Finset.inter_comm] at h2
          · exact hP.2 s hsP t htP hst
    have hmem : P.card + 1 ∈ packingSizes G :=
      ⟨insert t₀ P, hbig, by rw [Finset.card_insert_of_notMem hnot]⟩
    have hle := le_csSup (packingSizes_bddAbove G) hmem
    omega
  have hcov : ∀ t₀ : Finset α, G.IsNClique 3 t₀ → ∃ e ∈ F, e ⊆ t₀ := by
    intro t₀ ht₀
    obtain ⟨t, htP, hge⟩ := hmeet t₀ ht₀
    obtain ⟨e, hesub, hecard⟩ := Finset.exists_subset_card_eq hge
    refine ⟨e, ?_, hesub.trans Finset.inter_subset_left⟩
    rw [hF, Finset.mem_biUnion]
    exact ⟨t, htP,
      Finset.mem_powersetCard.mpr ⟨hesub.trans Finset.inter_subset_right, hecard⟩⟩
  have hFcard : F.card ≤ 3 * P.card := by
    calc F.card ≤ ∑ t ∈ P, (t.powersetCard 2).card := Finset.card_biUnion_le
      _ = ∑ _t ∈ P, 3 := by
          refine Finset.sum_congr rfl ?_
          intro t htP
          rw [Finset.card_powersetCard, (hP.1 t htP).card_eq]
          rfl
      _ = 3 * P.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hts : tau G ≤ F.card := Nat.sInf_le ⟨F, ⟨hedge, hcov⟩, rfl⟩
  have hnu : nu G = P.card := hPcard.symm
  omega

/-- `H` is `G` with the edges in `F` removed, each edge presented as a two-element clique. The
relation is stated rather than constructed, so the results below hold for any realisation of the
deletion. -/
def IsEdgeDeletion [DecidableEq α] (G H : SimpleGraph α) (F : Finset (Finset α)) : Prop :=
  ∀ x y, H.Adj x y ↔ G.Adj x y ∧ ({x, y} : Finset α) ∉ F

/-- A clique after removing edges is a clique before. -/
theorem isNClique_of_isEdgeDeletion [DecidableEq α] {G H : SimpleGraph α}
    {F : Finset (Finset α)} (hH : IsEdgeDeletion G H F) {n : ℕ} {t : Finset α}
    (h : H.IsNClique n t) : G.IsNClique n t :=
  ⟨fun _ hx _ hy hxy => ((hH _ _).mp (h.1 hx hy hxy)).1, h.2⟩

/-- Removing edges cannot increase the packing number. -/
theorem nu_le_of_isEdgeDeletion [DecidableEq α] [Finite α] {G H : SimpleGraph α}
    {F : Finset (Finset α)} (hH : IsEdgeDeletion G H F) : nu H ≤ nu G := by
  refine csSup_le ⟨0, zero_mem_packingSizes _⟩ ?_
  rintro k ⟨P, ⟨hTri, hDisj⟩, rfl⟩
  exact le_csSup (packingSizes_bddAbove G)
    ⟨P, ⟨fun t ht => isNClique_of_isEdgeDeletion hH (hTri t ht), hDisj⟩, rfl⟩

/-- Covering what is left after removing a set of edges, and then paying for those edges, covers
the original graph. -/
theorem tau_le_tau_add_card [DecidableEq α] [Finite α] {G H : SimpleGraph α}
    {F : Finset (Finset α)} (hH : IsEdgeDeletion G H F)
    (hF : ∀ e ∈ F, G.IsNClique 2 e) : tau G ≤ tau H + F.card := by
  obtain ⟨C, hC, hCcard⟩ := Nat.sInf_mem (coverSizes_nonempty H)
  have hcover : IsCover G (C ∪ F) := by
    refine ⟨?_, ?_⟩
    · intro e he
      rcases Finset.mem_union.mp he with heC | heF
      · exact isNClique_of_isEdgeDeletion hH (hC.1 e heC)
      · exact hF e heF
    · intro t ht
      by_cases hhit : ∃ e ∈ F, e ⊆ t
      · obtain ⟨e, heF, hesub⟩ := hhit
        exact ⟨e, Finset.mem_union_right _ heF, hesub⟩
      · have hmiss : ∀ e ∈ F, ¬ e ⊆ t := fun e he hsub => hhit ⟨e, he, hsub⟩
        have htH : H.IsNClique 3 t := by
          refine ⟨fun x hx y hy hxy => (hH x y).mpr ⟨ht.1 hx hy hxy, ?_⟩, ht.2⟩
          intro hmem
          refine hmiss _ hmem ?_
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact Finset.mem_coe.mp hx
          · rw [Finset.mem_singleton] at hz
            subst hz
            exact Finset.mem_coe.mp hy
        obtain ⟨e, heC, hesub⟩ := hC.2 t htH
        exact ⟨e, Finset.mem_union_left _ heC, hesub⟩
  calc tau G ≤ (C ∪ F).card := Nat.sInf_le ⟨C ∪ F, hcover, rfl⟩
    _ ≤ C.card + F.card := Finset.card_union_le C F
    _ = tau H + F.card := by
        simp only [tau]
        rw [hCcard]

/-- The reduction principle behind every reducible configuration: if removing a set of edges drops
the packing number by `k` while costing at most `2 * k` edges, Tuza's inequality transfers from the
smaller graph to the original. -/
theorem tuzaAt_of_edgeDeletion [DecidableEq α] [Finite α] {G H : SimpleGraph α}
    {F : Finset (Finset α)} (hH : IsEdgeDeletion G H F)
    (hF : ∀ e ∈ F, G.IsNClique 2 e) (k : ℕ) (hdrop : nu H + k ≤ nu G)
    (hcost : F.card ≤ 2 * k) (hsub : TuzaAt H) : TuzaAt G := by
  have h1 := tau_le_tau_add_card hH hF
  have h2 : tau H ≤ 2 * nu H := hsub
  unfold TuzaAt
  omega

/-- Any packing bounds the packing number from below. -/
theorem card_le_nu [DecidableEq α] [Finite α] {G : SimpleGraph α} {P : Finset (Finset α)}
    (hP : IsPacking G P) : P.card ≤ nu G :=
  le_csSup (packingSizes_bddAbove G) ⟨P, hP, rfl⟩

/-- The expensive half of the reduction principle, turned into an explicit obligation: it is
enough to extend one maximum packing of the smaller graph by `k` triangles of the larger one.
Bounding the packing number of the smaller graph from above is never needed. -/
theorem nu_add_le_nu_of_extends [DecidableEq α] [Finite α] {G H : SimpleGraph α} (k : ℕ)
    (hext : ∀ P : Finset (Finset α), IsPacking H P →
      ∃ Q : Finset (Finset α), IsPacking G Q ∧ P.card + k ≤ Q.card) :
    nu H + k ≤ nu G := by
  obtain ⟨P, hP, hPcard⟩ :=
    Nat.sSup_mem ⟨0, zero_mem_packingSizes H⟩ (packingSizes_bddAbove H)
  obtain ⟨Q, hQ, hQcard⟩ := hext P hP
  have hle := card_le_nu hQ
  have hnu : nu H = P.card := hPcard.symm
  omega

/-- The certificate schema for a reducible configuration. A triangle of the larger graph that the
deletion destroys, and that meets every surviving triangle in at most one vertex, can be added to
any packing of the smaller graph. So the deletion costs at most two edges and buys one triangle,
which is exactly the trade the reduction principle asks for. Each configuration in a census
instantiates this with its own triangle and edge set; nothing here enumerates. -/
theorem tuzaAt_of_reducibleTriangle [DecidableEq α] [Finite α]
    {G H : SimpleGraph α} {F : Finset (Finset α)} {t : Finset α}
    (hH : IsEdgeDeletion G H F) (hF : ∀ e ∈ F, G.IsNClique 2 e)
    (ht : G.IsNClique 3 t) (hgone : ¬ H.IsNClique 3 t)
    (hmeet : ∀ s : Finset α, H.IsNClique 3 s → (t ∩ s).card ≤ 1)
    (hcost : F.card ≤ 2) (hsub : TuzaAt H) : TuzaAt G := by
  refine tuzaAt_of_edgeDeletion hH hF 1 ?_ (by omega) hsub
  refine nu_add_le_nu_of_extends 1 ?_
  intro P hP
  have hnot : t ∉ P := fun hmem => hgone (hP.1 t hmem)
  refine ⟨insert t P, ⟨?_, ?_⟩, ?_⟩
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hsP
    · exact ht
    · exact isNClique_of_isEdgeDeletion hH (hP.1 s hsP)
  · intro s hs u hu hsu
    have hs' := Finset.mem_insert.mp hs
    have hu' := Finset.mem_insert.mp hu
    rcases hs' with rfl | hsP
    · rcases hu' with rfl | huP
      · exact absurd rfl hsu
      · exact hmeet u (hP.1 u huP)
    · rcases hu' with rfl | huP
      · have h2 := hmeet s (hP.1 s hsP)
        rwa [Finset.inter_comm] at h2
      · exact hP.2 s hsP u huP hsu
  · rw [Finset.card_insert_of_notMem hnot]

end D5.S3.Combinatorics.Graph.TrianglePackingCover
