/- GID: D5/S3/Combinatorics/Graph/Laman/Moves
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Laman/Moves
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: Credited combinatorial sparsity and Henneberg constructions. -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in
 docs/reports/licenses/laman-henneberg/LICENSE.txt.
Authors: Bryan Gin-ge Chen
Modified file: selected source declarations reorganized for trureturing;
receiver API adaptations, imports, and unused-declaration removal.
Source: CombinatorialRigidity@021c2284bc387efee3c3b20a18eb5f769638b578.
-/
import D5.S3.Combinatorics.Graph.Laman.SafeRepair

/-! # Moves: finite graph sparsity and Henneberg constructions -/

namespace Finset

variable {α : Type*}

theorem card_eraseNone_add_one_of_mem {s : Finset (Option α)} (h : none ∈ s) :
    s.eraseNone.card + 1 = s.card := by
  rw [card_eraseNone_of_mem h, Nat.sub_add_cancel (Finset.card_pos.mpr ⟨_, h⟩)]

end Finset

namespace Set

variable {α : Type*}

theorem ncard_pair_le (a b : α) : ({a, b} : Set α).ncard ≤ 2 :=
  (ncard_insert_le _ _).trans (by rw [ncard_singleton])

theorem ncard_triple_le (a b c : α) : ({a, b, c} : Set α).ncard ≤ 3 :=
  (ncard_insert_le _ _).trans (Nat.add_le_add_right (ncard_pair_le _ _) _)

end Set

namespace Sym2

variable {α : Type*}

lemma map_some_injective : Function.Injective (Sym2.map (some : α → Option α)) :=
  Sym2.map.injective (Option.some_injective α)

lemma notMem_map_some (e : Sym2 α) :
    none ∉ Sym2.map (some : α → Option α) e := by
  rw [Sym2.mem_map]
  rintro ⟨_, _, h⟩
  exact Option.some_ne_none _ h

theorem disjoint_image_map_some {S : Set (Sym2 α)} {T : Set (Sym2 (Option α))}
    (hT : ∀ e ∈ T, none ∈ e) : Disjoint (Sym2.map some '' S) T := by
  rw [Set.disjoint_left]
  rintro _ ⟨e, _, rfl⟩ heT
  exact notMem_map_some e (hT _ heT)

end Sym2

namespace SimpleGraph

variable {V : Type*}

def IsLaman (G : SimpleGraph V) : Prop := G.IsTight 2 3

theorem IsLaman.isSparse {G : SimpleGraph V} (h : G.IsLaman) : G.IsSparse 2 3 := h.1

theorem IsLaman.edgeSet_ncard {G : SimpleGraph V} (h : G.IsLaman) :
    G.edgeSet.ncard + 3 = 2 * Nat.card V := h.2

theorem IsLaman.two_le_degree [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsLaman)
    (hV : 3 ≤ Fintype.card V) (v : V) :
    2 ≤ G.degree v := by
  classical
  have hsparse := h.isSparse ({v} : Finset V)ᶜ (by simp only [Finset.card_compl, Finset.card_singleton]; omega)
  have hpart := G.ncard_edgesIn_compl_singleton_add_ncard_incidenceSet v
  have hE := h.edgeSet_ncard
  grind only [Finset.coe_compl, Finset.coe_singleton, Finset.card_compl, Finset.card_singleton,
    G.ncard_incidenceSet, Nat.card_eq_fintype_card]

theorem IsLaman.iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (h : G.IsLaman) : H.IsLaman :=
  IsTight.iso φ h

theorem IsLaman.eq_top_of_card_eq_two [Fintype V]
    {G : SimpleGraph V} (h : G.IsLaman) (hV : Fintype.card V = 2) : G = ⊤ := by
  rw [← edgeSet_inj]
  have hG_card : G.edgeSet.ncard = 1 := by
    grind only [h.edgeSet_ncard, Nat.card_eq_fintype_card]
  have hTop_card : ((⊤ : SimpleGraph V).edgeSet).ncard = 1 := by
    rw [ncard_edgeSet_top_eq_card_choose_two, hV]; rfl
  refine Set.eq_of_subset_of_ncard_le (edgeSet_subset_edgeSet.mpr le_top) ?_ ?_
  · rw [hTop_card, hG_card]
  · classical
    exact (Set.toFinite _)

theorem top_fin_two_isLaman : (⊤ : SimpleGraph (Fin 2)).IsLaman := by
  have hcard : ((⊤ : SimpleGraph (Fin 2)).edgeSet).ncard = 1 := by
    rw [ncard_edgeSet_top_eq_card_choose_two]; rfl
  refine ⟨fun s hs => ?_, by grind only [Nat.card_eq_fintype_card, Fintype.card_fin]⟩
  obtain rfl : s = Finset.univ :=
    s.eq_univ_of_card (by have := s.card_le_univ; grind only [Fintype.card_fin])
  grind only [!Finset.coe_univ, edgesIn_univ]

namespace Henneberg

def typeI (G : SimpleGraph V) (a b : V) : SimpleGraph (Option V) where
  Adj
    | some u, some v => G.Adj u v
    | some u, none => u = a ∨ u = b
    | none, some v => v = a ∨ v = b
    | none, none => False
  symm := ⟨by
    rintro (_ | u) (_ | v) h
    · exact h
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨fun
    | none => id
    | some u => G.loopless.irrefl u⟩

def typeII (G : SimpleGraph V) (a b c : V) : SimpleGraph (Option V) where
  Adj
    | some u, some v => G.Adj u v ∧ s(u, v) ≠ s(a, b)
    | some u, none => u = a ∨ u = b ∨ u = c
    | none, some v => v = a ∨ v = b ∨ v = c
    | none, none => False
  symm := ⟨by
    rintro (_ | u) (_ | v) h
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm, fun heq => h.2 (Sym2.eq_swap.trans heq)⟩⟩
  loopless := ⟨fun
    | none => id
    | some u => fun h => G.loopless.irrefl u h.1⟩

variable {G : SimpleGraph V} {a b c u v : V}

@[simp] lemma typeI_adj_some_some : (typeI G a b).Adj (some u) (some v) ↔ G.Adj u v := Iff.rfl

@[simp] lemma typeI_adj_some_none : (typeI G a b).Adj (some u) none ↔ u = a ∨ u = b := Iff.rfl

@[simp] lemma typeI_adj_none_some : (typeI G a b).Adj none (some v) ↔ v = a ∨ v = b := Iff.rfl

@[simp] lemma typeII_adj_some_some :
    (typeII G a b c).Adj (some u) (some v) ↔ G.Adj u v ∧ s(u, v) ≠ s(a, b) := Iff.rfl

@[simp] lemma typeII_adj_some_none :
    (typeII G a b c).Adj (some u) none ↔ u = a ∨ u = b ∨ u = c := Iff.rfl

@[simp] lemma typeII_adj_none_some :
    (typeII G a b c).Adj none (some v) ↔ v = a ∨ v = b ∨ v = c := Iff.rfl

private lemma fresh_sym2_ncard_eq_zero_of_none_notMem [Finite V] {s : Finset (Option V)}
    (hnone : none ∉ s) (xs : Set (Sym2 (Option V))) (h_xs : ∀ e ∈ xs, none ∈ e) :
    (xs ∩ ((↑s : Set (Option V)).sym2)).ncard = 0 := by
  rw [Set.ncard_eq_zero, Set.eq_empty_iff_forall_notMem]
  rintro e ⟨he, hsub⟩
  exact hnone (Set.mem_sym2_iff_subset.mp hsub (h_xs e he))

private lemma fresh_sym2_subset_singleton {s : Finset (Option V)} {w : V}
    (hw : s.eraseNone = {w})
    (xs : Set (Sym2 (Option V))) (h_xs : ∀ e ∈ xs, ∃ x : V, e = s(none, some x)) :
    xs ∩ ((↑s : Set (Option V)).sym2) ⊆ ({s(none, some w)} : Set _) := by
  rintro e ⟨he, hsub⟩
  obtain ⟨x, rfl⟩ := h_xs e he
  rw [Set.mem_sym2_iff_subset, Sym2.coe_mk] at hsub
  have hx : x ∈ s.eraseNone := Finset.mem_eraseNone.mpr (hsub (Or.inr rfl))
  rw [hw, Finset.mem_singleton] at hx
  exact hx ▸ rfl

private lemma fresh_sym2_triple_inter_ncard_le_two {s : Finset (Option V)}
    {x y z : V} (hx : x ∉ s.eraseNone) :
    (({s(none, some x), s(none, some y), s(none, some z)} : Set _) ∩
        ((↑s : Set (Option V)).sym2)).ncard ≤ 2 := by
  refine (Set.ncard_le_ncard (?_ : _ ⊆
      ({s(none, some y), s(none, some z)} : Set _))).trans (Set.ncard_pair_le _ _)
  rintro e ⟨hpair, hsub⟩
  have hsubV : (e : Set (Option V)) ⊆ ↑s := Set.mem_sym2_iff_subset.mp hsub
  rcases hpair with rfl | rfl | rfl
  · exact (hx (Finset.mem_eraseNone.mpr (hsubV (by simp)))).elim
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ rfl

lemma typeI_edgeSet (G : SimpleGraph V) (a b : V) :
    (typeI G a b).edgeSet =
      (Sym2.map some '' G.edgeSet) ∪ {s(none, some a), s(none, some b)} := by
  ext e
  induction e with | h x y => ?_
  rcases x with _ | u <;> rcases y with _ | v <;> simp

lemma typeI_edgeSet_ncard [Finite V] (G : SimpleGraph V) {a b : V} (hab : a ≠ b) :
    ((typeI G a b).edgeSet).ncard = G.edgeSet.ncard + 2 := by
  have hDisj : Disjoint (Sym2.map some '' G.edgeSet)
      ({s(none, some a), s(none, some b)} : Set (Sym2 (Option V))) :=
    Sym2.disjoint_image_map_some (by rintro e (rfl | rfl) <;> simp)
  rw [typeI_edgeSet, Set.ncard_union_eq hDisj,
    Set.ncard_image_of_injective _ Sym2.map_some_injective, Set.ncard_pair (by simp [hab])]

private lemma typeI_edgesIn_ncard_decomp [Finite V] (G : SimpleGraph V) (a b : V)
    (s : Finset (Option V)) :
    ((typeI G a b).edgesIn (↑s : Set (Option V))).ncard =
      (G.edgesIn (↑s.eraseNone : Set V)).ncard +
      (({s(none, some a), s(none, some b)} : Set (Sym2 (Option V))) ∩
        ((↑s : Set (Option V)).sym2)).ncard := by
  set T : Set (Sym2 (Option V)) :=
    ({s(none, some a), s(none, some b)} : Set _) ∩ ((↑s : Set (Option V)).sym2)
  have h_decomp : (typeI G a b).edgesIn (↑s : Set (Option V)) =
      Sym2.map some '' G.edgesIn (↑s.eraseNone : Set V) ∪ T := by
    ext e
    induction e with | h x y => ?_
    rcases x with _ | u <;> rcases y with _ | v <;> simp [edgesIn, T]
  have h_disj : Disjoint (Sym2.map some '' G.edgesIn (↑s.eraseNone : Set V)) T :=
    Sym2.disjoint_image_map_some fun _ ⟨hpair, _⟩ => by rcases hpair with rfl | rfl <;> simp
  rw [h_decomp, Set.ncard_union_eq h_disj,
    Set.ncard_image_of_injective _ Sym2.map_some_injective]

theorem typeI_isLaman [Finite V] {G : SimpleGraph V} (h : G.IsLaman)
    {a b : V} (hab : a ≠ b) : (typeI G a b).IsLaman := by
  have : Fintype V := Fintype.ofFinite V
  refine ⟨fun s hs_pre => ?_, ?_⟩
  · set s' : Finset V := s.eraseNone
    set T : Set (Sym2 (Option V)) :=
      ({s(none, some a), s(none, some b)} : Set _) ∩ ((↑s : Set (Option V)).sym2)
    have h_ncard : ((typeI G a b).edgesIn (↑s : Set (Option V))).ncard =
        (G.edgesIn (↑s' : Set V)).ncard + T.ncard :=
      typeI_edgesIn_ncard_decomp G a b s
    have hT_le_2 : T.ncard ≤ 2 :=
      (Set.ncard_le_ncard Set.inter_subset_left).trans (Set.ncard_pair_le _ _)
    by_cases hnone : none ∈ s
    · have hsc : s.card = s'.card + 1 := (Finset.card_eraseNone_add_one_of_mem hnone).symm
      rcases (show s'.card = 0 ∨ s'.card = 1 ∨ 2 ≤ s'.card from by omega)
        with h0 | h1 | hge
      · omega
      · obtain ⟨w, hw⟩ : ∃ w, s' = {w} := Finset.card_eq_one.mp h1
        have hG_empty : (G.edgesIn (↑s' : Set V)).ncard = 0 := by rw [hw]; simp
        have hT_sub : T ⊆ ({s(none, some w)} : Set _) :=
          fresh_sym2_subset_singleton hw _
            (by rintro e (rfl | rfl) <;> exact ⟨_, rfl⟩)
        have hT_le_1 : T.ncard ≤ 1 :=
          (Set.ncard_le_ncard hT_sub).trans (le_of_eq (Set.ncard_singleton _))
        omega
      · have hG := h.isSparse s' (by omega)
        omega
    · have hsc : s.card = s'.card := (Finset.card_eraseNone_of_notMem hnone).symm
      have hT_empty : T.ncard = 0 :=
        fresh_sym2_ncard_eq_zero_of_none_notMem hnone _ (by rintro e (rfl | rfl) <;> simp)
      have hG := h.isSparse s' (by omega)
      omega
  · grind only [!typeI_edgeSet_ncard, !Finite.card_option, h.edgeSet_ncard]

theorem typeI_reverse_isLaman [Finite V] {G : SimpleGraph V} {a b : V} (hab : a ≠ b)
    (h : (typeI G a b).IsLaman) : G.IsLaman := by
  classical
  refine ⟨fun s' hs' => ?_, ?_⟩
  · set s : Finset (Option V) := s'.image some
    have hs_card : s.card = s'.card :=
      Finset.card_image_of_injective s' (Option.some_injective _)
    have hnone : none ∉ s := by simp [s]
    have hT_zero : (({s(none, some a), s(none, some b)} : Set (Sym2 (Option V))) ∩
        ((↑s : Set (Option V)).sym2)).ncard = 0 :=
      fresh_sym2_ncard_eq_zero_of_none_notMem hnone _ (by rintro e (rfl | rfl) <;> simp)
    have h_decomp := typeI_edgesIn_ncard_decomp G a b s
    rw [Finset.eraseNone_image_some, hT_zero, add_zero] at h_decomp
    have hsparse := h.isSparse s (by rw [hs_card]; exact hs')
    rw [h_decomp, hs_card] at hsparse
    exact hsparse
  · grind only [!typeI_edgeSet_ncard, !Finite.card_option, h.edgeSet_ncard]

theorem typeI_isLaman_iff [Finite V] {G : SimpleGraph V} {a b : V} (hab : a ≠ b) :
    (typeI G a b).IsLaman ↔ G.IsLaman :=
  ⟨typeI_reverse_isLaman hab, fun h => typeI_isLaman h hab⟩

lemma typeII_edgeSet (G : SimpleGraph V) (a b c : V) :
    (typeII G a b c).edgeSet =
      (Sym2.map some '' (G.edgeSet \ {s(a, b)})) ∪
        {s(none, some a), s(none, some b), s(none, some c)} := by
  ext e
  induction e with | h x y => ?_
  rcases x with _ | u <;> rcases y with _ | v <;> simp

lemma typeII_edgeSet_ncard [Finite V] (G : SimpleGraph V) {a b c : V}
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    ((typeII G a b c).edgeSet).ncard = (G.edgeSet \ {s(a, b)}).ncard + 3 := by
  have hDisj : Disjoint (Sym2.map some '' (G.edgeSet \ {s(a, b)}))
      ({s(none, some a), s(none, some b), s(none, some c)} :
        Set (Sym2 (Option V))) :=
    Sym2.disjoint_image_map_some (by rintro e (rfl | rfl | rfl) <;> simp)
  rw [typeII_edgeSet, Set.ncard_union_eq hDisj,
    Set.ncard_image_of_injective _ Sym2.map_some_injective,
    Set.ncard_insert_of_notMem (by simp [hab, hca.symm]) (by simp),
    Set.ncard_pair (by simp [hcb.symm])]

private lemma typeII_edgesIn_ncard_decomp [Finite V] (G : SimpleGraph V) (a b c : V)
    (s : Finset (Option V)) :
    ((typeII G a b c).edgesIn (↑s : Set (Option V))).ncard =
      (G.edgesIn (↑s.eraseNone : Set V) \ {s(a, b)}).ncard +
      (({s(none, some a), s(none, some b), s(none, some c)} : Set (Sym2 (Option V))) ∩
        ((↑s : Set (Option V)).sym2)).ncard := by
  set T' : Set (Sym2 (Option V)) :=
    ({s(none, some a), s(none, some b), s(none, some c)} : Set _) ∩
      ((↑s : Set (Option V)).sym2)
  have h_decomp : (typeII G a b c).edgesIn (↑s : Set (Option V)) =
      Sym2.map some '' (G.edgesIn (↑s.eraseNone : Set V) \ {s(a, b)}) ∪ T' := by
    ext e
    induction e with | h x y => ?_
    rcases x with _ | u <;> rcases y with _ | v <;>
      (simp [edgesIn, T']; try tauto)
  have h_disj : Disjoint (Sym2.map some '' (G.edgesIn (↑s.eraseNone : Set V) \ {s(a, b)})) T' :=
    Sym2.disjoint_image_map_some
      fun _ ⟨hpair, _⟩ => by rcases hpair with rfl | rfl | rfl <;> simp
  rw [h_decomp, Set.ncard_union_eq h_disj,
    Set.ncard_image_of_injective _ Sym2.map_some_injective]

theorem typeII_isLaman [Finite V] {G : SimpleGraph V} (h : G.IsLaman) {a b c : V}
    (hca : c ≠ a) (hcb : c ≠ b) (hG_ab : G.Adj a b) :
    (typeII G a b c).IsLaman := by
  have : Fintype V := Fintype.ofFinite V
  refine ⟨fun s hs_pre => ?_, ?_⟩
  · set s' : Finset V := s.eraseNone
    set T' : Set (Sym2 (Option V)) :=
      ({s(none, some a), s(none, some b), s(none, some c)} : Set _) ∩
        ((↑s : Set (Option V)).sym2) with hT'_def
    have h_ncard : ((typeII G a b c).edgesIn (↑s : Set (Option V))).ncard =
        (G.edgesIn (↑s' : Set V) \ {s(a, b)}).ncard + T'.ncard :=
      typeII_edgesIn_ncard_decomp G a b c s
    have hT'_le_3 : T'.ncard ≤ 3 :=
      (Set.ncard_le_ncard Set.inter_subset_left).trans (Set.ncard_triple_le _ _ _)
    by_cases hnone : none ∈ s
    · have hsc : s.card = s'.card + 1 := (Finset.card_eraseNone_add_one_of_mem hnone).symm
      rcases (show s'.card = 0 ∨ s'.card = 1 ∨ 2 ≤ s'.card from by omega)
        with h0 | h1 | hge
      · omega
      · obtain ⟨w, hw⟩ : ∃ w, s' = {w} := Finset.card_eq_one.mp h1
        have hG_empty : (G.edgesIn (↑s' : Set V) \ {s(a, b)}).ncard = 0 := by
          rw [hw]; simp
        have hT'_sub : T' ⊆ ({s(none, some w)} : Set _) :=
          fresh_sym2_subset_singleton hw _
            (by rintro e (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩)
        have hT'_le_1 : T'.ncard ≤ 1 :=
          (Set.ncard_le_ncard hT'_sub).trans (le_of_eq (Set.ncard_singleton _))
        omega
      · have hG := h.isSparse s' (by omega)
        by_cases h_ab_in : s(a, b) ∈ G.edgesIn (↑s' : Set V)
        · have hdiff := Set.ncard_sdiff_singleton_of_mem h_ab_in (s := G.edgesIn (↑s' : Set V))
          have hG_ne_zero : (G.edgesIn (↑s' : Set V)).ncard ≠ 0 :=
            Set.ncard_ne_zero_of_mem h_ab_in
          omega
        · have hdiff : (G.edgesIn (↑s' : Set V) \ {s(a, b)}).ncard =
              (G.edgesIn (↑s' : Set V)).ncard := by
            rw [Set.sdiff_singleton_eq_self h_ab_in]
          have h_or : a ∉ s' ∨ b ∉ s' := by
            by_contra h_both
            push Not at h_both
            exact h_ab_in (G.mk_mem_edgesIn hG_ab h_both.1 h_both.2)
          have hT'_le_2 : T'.ncard ≤ 2 := by
            rcases h_or with ha | hb
            · exact fresh_sym2_triple_inter_ncard_le_two ha
            · rw [hT'_def, Set.insert_comm s(none, some a) s(none, some b)]
              exact fresh_sym2_triple_inter_ncard_le_two hb
          omega
    · have hsc : s.card = s'.card := (Finset.card_eraseNone_of_notMem hnone).symm
      have hT'_empty : T'.ncard = 0 :=
        fresh_sym2_ncard_eq_zero_of_none_notMem hnone _ (by rintro e (rfl | rfl | rfl) <;> simp)
      have hG := h.isSparse s' (by omega)
      have hdiff_le : (G.edgesIn (↑s' : Set V) \ {s(a, b)}).ncard ≤
          (G.edgesIn (↑s' : Set V)).ncard :=
        Set.ncard_sdiff_singleton_le _ _
      omega
  · have hab : a ≠ b := hG_ab.ne
    have hab_in : s(a, b) ∈ G.edgeSet := hG_ab
    grind only [!typeII_edgeSet_ncard, !Finite.card_option,
      !Set.ncard_sdiff_singleton_of_mem, h.edgeSet_ncard]

private def isoOfOptionSubtypeNe [DecidableEq V] {G : SimpleGraph V} (v : V)
    {H : SimpleGraph (Option {w : V // w ≠ v})}
    (hns : ∀ w (hw : w ≠ v), H.Adj none (some ⟨w, hw⟩) ↔ G.Adj v w)
    (hss : ∀ {u w} (hu : u ≠ v) (hw : w ≠ v),
        H.Adj (some ⟨u, hu⟩) (some ⟨w, hw⟩) ↔ G.Adj u w) :
    G ≃g H where
  toEquiv := (Equiv.optionSubtypeNe v).symm
  map_rel_iff' {u w} := by
    by_cases hu : u = v <;> by_cases hw : w = v
    · subst hu; subst hw
      simp
    · subst hu
      rw [Equiv.optionSubtypeNe_symm_self, Equiv.optionSubtypeNe_symm_of_ne hw]
      exact hns w hw
    · subst hw
      rw [Equiv.optionSubtypeNe_symm_of_ne hu, Equiv.optionSubtypeNe_symm_self,
        H.adj_comm, G.adj_comm]
      exact hns u hu
    · rw [Equiv.optionSubtypeNe_symm_of_ne hu, Equiv.optionSubtypeNe_symm_of_ne hw]
      exact hss hu hw

def isoTypeIOfTwoNeighbors [DecidableEq V] {G : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hN : ∀ w, G.Adj v w ↔ w = a ∨ w = b) :
    G ≃g typeI (G.comap (Subtype.val : {w : V // w ≠ v} → V))
      ⟨a, hva.symm⟩ ⟨b, hvb.symm⟩ :=
  isoOfOptionSubtypeNe v
    (fun w _ => by simp [hN])
    (fun _ _ => Iff.rfl)

def isoTypeIIOfThreeNeighbors [DecidableEq V] {G : SimpleGraph V} {v a b c : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hN : ∀ w, G.Adj v w ↔ w = a ∨ w = b ∨ w = c) (hnab : ¬ G.Adj a b) :
    G ≃g typeII (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
        fromEdgeSet ({s(⟨a, hva.symm⟩, ⟨b, hvb.symm⟩)} : Set (Sym2 _)))
      ⟨a, hva.symm⟩ ⟨b, hvb.symm⟩ ⟨c, hvc.symm⟩ :=
  isoOfOptionSubtypeNe v
    (fun w _ => by simp [hN])
    (fun {u w} _ _ => by
      rw [typeII_adj_some_some, sup_adj, comap_adj, fromEdgeSet_adj, Set.mem_singleton_iff]
      refine ⟨fun h => h.1.elim id (fun ⟨hL, _⟩ => absurd hL h.2),
        fun hadj => ⟨Or.inl hadj, fun heq => ?_⟩⟩
      have : s(u, w) = s(a, b) := by simpa using congrArg (Sym2.map Subtype.val) heq
      rcases Sym2.eq_iff.mp this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> grind [G.adj_symm])

theorem IsLaman.exists_typeI_or_typeII_reverse [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsLaman)
    (hV : 3 ≤ Fintype.card V) :
    ∃ v : V,
      (G.degree v = 2 ∧
        ∃ a b : {w : V // w ≠ v}, a ≠ b ∧
          (∀ w : V, G.Adj v w ↔ w = a.val ∨ w = b.val) ∧
          (G.comap (Subtype.val : {w : V // w ≠ v} → V)).IsLaman)
      ∨
      (G.degree v = 3 ∧
        ∃ x y c : {w : V // w ≠ v}, x ≠ y ∧ c ≠ x ∧ c ≠ y ∧
          (∀ w : V, G.Adj v w ↔ w = x.val ∨ w = y.val ∨ w = c.val) ∧
          ¬ G.Adj x.val y.val ∧
          (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
            fromEdgeSet ({s(x, y)} : Set _)).IsLaman) := by
  classical
  have hE : G.edgeSet.Nonempty := by
    have h_eq := h.edgeSet_ncard
    rw [Nat.card_eq_fintype_card] at h_eq
    exact Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨v, hbranch⟩ := h.isSparse.exists_typeI_or_typeII_reverse hE
  refine ⟨v, ?_⟩
  rcases hbranch with
    ⟨hdeg1, _, _, _⟩ |
    ⟨hdeg2, a, b, hab, hN_iff, hG'sparse⟩ |
    ⟨hdeg3, x, y, c, hxy, hcx, hcy, hN, hnxy, hG'sparse⟩
  · exact absurd hdeg1 (by have := h.two_le_degree hV v; omega)
  · have ha_adj : G.Adj v a.val := (hN_iff a.val).mpr (Or.inl rfl)
    have hb_adj : G.Adj v b.val := (hN_iff b.val).mpr (Or.inr rfl)
    have hG'_laman : (G.comap (Subtype.val : {w : V // w ≠ v} → V)).IsLaman :=
      (typeI_isLaman_iff hab).mp
        (IsLaman.iso (isoTypeIOfTwoNeighbors (G.ne_of_adj ha_adj) (G.ne_of_adj hb_adj)
          hN_iff) h)
    exact Or.inl ⟨hdeg2, a, b, hab, hN_iff, hG'_laman⟩
  · refine Or.inr ⟨hdeg3, x, y, c, hxy, hcx, hcy, hN, hnxy, ?_⟩
    set G' : SimpleGraph {w : V // w ≠ v} :=
      G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
        fromEdgeSet ({s(x, y)} : Set _) with hG'_def
    have h_iso : G ≃g typeII G' x y c :=
      isoTypeIIOfThreeNeighbors x.property.symm y.property.symm c.property.symm hN hnxy
    have h_typeII_laman : (typeII G' x y c).IsLaman := IsLaman.iso h_iso h
    have h_count := h_typeII_laman.edgeSet_ncard
    rw [typeII_edgeSet_ncard G' hxy hcx hcy, Finite.card_option] at h_count
    have hbridge : s(x, y) ∈ G'.edgeSet := by
      change G'.Adj x y
      rw [hG'_def, sup_adj]
      exact Or.inr ((fromEdgeSet_adj _).mpr ⟨rfl, hxy⟩)
    have h_diff : (G'.edgeSet \ {s(x, y)}).ncard + 1 = G'.edgeSet.ncard :=
      Set.ncard_sdiff_singleton_add_one hbridge (Set.toFinite _)
    exact ⟨hG'sparse, by omega⟩

end Henneberg

end SimpleGraph
