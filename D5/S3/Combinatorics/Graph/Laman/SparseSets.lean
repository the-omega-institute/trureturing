/- GID: D5/S3/Combinatorics/Graph/Laman/SparseSets
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Laman/SparseSets
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
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Sym.Sym2
import Mathlib.Logic.Equiv.Option

/-! # SparseSets: finite graph sparsity and Henneberg constructions -/

namespace Finset

variable {α : Type*}

lemma eq_singleton_of_mem_of_card_le_one {s : Finset α} {z : α}
    (hz : z ∈ s) (h : s.card ≤ 1) : s = {z} :=
  (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hz)
    (h.trans_eq (Finset.card_singleton z).symm)).symm

lemma mul_card_union_add_mul_card_inter [DecidableEq α] (s t : Finset α) (k : ℕ) :
    k * s.card + k * t.card = k * (s ∪ t).card + k * (s ∩ t).card := by
  rw [← Nat.mul_add, ← Nat.mul_add, Finset.card_union_add_card_inter]


end Finset

namespace Sym2

variable {α β : Type*}

@[simp]
lemma exists_and_map_eq_mk_iff {f : α → β} {P : Sym2 α → Prop} {x y : β} :
    (∃ e, P e ∧ Sym2.map f e = s(x, y)) ↔ ∃ p q, f p = x ∧ f q = y ∧ P s(p, q) := by
  constructor
  · rintro ⟨e, hP, hmap⟩
    induction e with | h α' β' => ?_
    rw [Sym2.map_mk, Sym2.eq_iff] at hmap
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hmap
    · exact ⟨_, _, rfl, rfl, hP⟩
    · exact ⟨_, _, rfl, rfl, by rwa [Sym2.eq_swap]⟩
  · rintro ⟨p, q, rfl, rfl, hP⟩
    exact ⟨s(p, q), hP, by rw [Sym2.map_mk]⟩

lemma mk_mem_image_map_iff {f : α → β} {S : Set (Sym2 α)} {x y : β} :
    s(x, y) ∈ Sym2.map f '' S ↔ ∃ p q, f p = x ∧ f q = y ∧ s(p, q) ∈ S := by
  rw [Set.mem_image]
  exact exists_and_map_eq_mk_iff

end Sym2

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

def edgesIn (s : Set V) : Set (Sym2 V) := G.edgeSet ∩ s.sym2

variable {G}

@[simp] lemma mem_edgesIn {e : Sym2 V} {s : Set V} :
    e ∈ G.edgesIn s ↔ e ∈ G.edgeSet ∧ (e : Set V) ⊆ s := by
  rw [edgesIn, Set.mem_inter_iff, Set.mem_sym2_iff_subset]

lemma mk_mem_edgesIn {x y : V} {s : Set V} (h : G.Adj x y) (hx : x ∈ s) (hy : y ∈ s) :
    s(x, y) ∈ G.edgesIn s :=
  mem_edgesIn.mpr ⟨h, by
    rw [Sym2.coe_mk]
    exact Set.insert_subset_iff.mpr ⟨hx, Set.singleton_subset_iff.mpr hy⟩⟩

lemma notMem_edgesIn_mk_of_left_notMem {x y : V} {s : Set V} (hxs : x ∉ s) :
    s(x, y) ∉ G.edgesIn s := fun hmem => by
  rw [mem_edgesIn, Sym2.coe_mk] at hmem
  exact hxs (hmem.2 (Set.mem_insert _ _))

lemma notMem_edgesIn_mk_of_right_notMem {x y : V} {s : Set V} (hys : y ∉ s) :
    s(x, y) ∉ G.edgesIn s := fun hmem => by
  rw [mem_edgesIn, Sym2.coe_mk] at hmem
  exact hys (hmem.2 (Set.mem_insert_of_mem _ rfl))

@[gcongr]
lemma edgesIn_mono {s t : Set V} (h : s ⊆ t) : G.edgesIn s ⊆ G.edgesIn t :=
  fun _ ⟨he₁, he₂⟩ ↦ ⟨he₁, (Set.mem_sym2_iff_subset.mp he₂).trans h |> Set.mem_sym2_iff_subset.mpr⟩

@[simp] lemma edgesIn_univ : G.edgesIn Set.univ = G.edgeSet := by
  simp [edgesIn]


@[simp] lemma edgesIn_singleton (G : SimpleGraph V) (v : V) : G.edgesIn ({v} : Set V) = ∅ := by
  ext e
  refine e.ind fun x y => ?_
  simp only [mem_edgesIn, mem_edgeSet, Set.mem_empty_iff_false, iff_false, not_and]
  intro hadj hsub
  have hx : x = v := hsub (Sym2.mem_mk_left x y)
  have hy : y = v := hsub (Sym2.mem_mk_right x y)
  rw [hx, hy] at hadj
  exact G.loopless.irrefl _ hadj

lemma edgesIn_finite (G : SimpleGraph V) (s : Finset V) : (G.edgesIn ↑s).Finite := by
  refine s.sym2.finite_toSet.subset ?_
  rw [Finset.coe_sym2]
  exact Set.inter_subset_right

lemma edgesIn_eq_image_induce_edgeSet (G : SimpleGraph V) (S : Set V) :
    G.edgesIn S = Sym2.map (Subtype.val : ↥S → V) '' (G.induce S).edgeSet := by
  ext e
  simp only [mem_edgesIn, Set.mem_image]
  refine ⟨fun ⟨he_adj, he_sub⟩ => ?_, ?_⟩
  · induction e with | h u v =>
      rw [Sym2.coe_mk, Set.insert_subset_iff, Set.singleton_subset_iff] at he_sub
      exact ⟨s(⟨u, he_sub.1⟩, ⟨v, he_sub.2⟩), he_adj, rfl⟩
  · rintro ⟨e', he', rfl⟩
    refine e'.ind (fun u v he' => ?_) he'
    refine ⟨he', ?_⟩
    rw [Sym2.map_mk, Sym2.coe_mk, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨u.2, v.2⟩

lemma ncard_edgesIn_eq_ncard_induce_edgeSet (G : SimpleGraph V) (S : Set V) :
    (G.edgesIn S).ncard = (G.induce S).edgeSet.ncard := by
  rw [edgesIn_eq_image_induce_edgeSet,
    Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]

lemma mem_edgesIn_compl_singleton {v : V} {e : Sym2 V} :
    e ∈ G.edgesIn ({v}ᶜ : Set V) ↔ e ∈ G.edgeSet ∧ v ∉ e := by
  rw [mem_edgesIn, Set.subset_compl_singleton_iff]
  rfl

lemma edgesIn_compl_singleton (v : V) :
    G.edgesIn ({v}ᶜ : Set V) = G.edgeSet \ G.incidenceSet v := by
  ext e
  grind [mem_edgesIn_compl_singleton, incidenceSet]

lemma ncard_edgesIn_compl_singleton_add_ncard_incidenceSet [Finite V] (v : V) :
    (G.edgesIn ({v}ᶜ : Set V)).ncard + (G.incidenceSet v).ncard = G.edgeSet.ncard := by
  rw [edgesIn_compl_singleton]
  exact Set.ncard_sdiff_add_ncard_of_subset (G.incidenceSet_subset v) G.edgeSet.toFinite

lemma edgesIn_inter (S T : Set V) :
    G.edgesIn (S ∩ T) = G.edgesIn S ∩ G.edgesIn T := by
  ext e
  simp only [Set.mem_inter_iff, mem_edgesIn, Set.subset_inter_iff]
  tauto

lemma edgesIn_ncard_add_le [Finite V] (S T : Set V) :
    (G.edgesIn S).ncard + (G.edgesIn T).ncard ≤
      (G.edgesIn (S ∪ T)).ncard + (G.edgesIn (S ∩ T)).ncard := by
  have h_union : G.edgesIn S ∪ G.edgesIn T ⊆ G.edgesIn (S ∪ T) :=
    Set.union_subset (edgesIn_mono Set.subset_union_left)
                     (edgesIn_mono Set.subset_union_right)
  calc (G.edgesIn S).ncard + (G.edgesIn T).ncard
      = (G.edgesIn S ∪ G.edgesIn T).ncard + (G.edgesIn S ∩ G.edgesIn T).ncard :=
        (Set.ncard_union_add_ncard_inter _ _).symm
    _ = (G.edgesIn S ∪ G.edgesIn T).ncard + (G.edgesIn (S ∩ T)).ncard := by
        rw [← edgesIn_inter]
    _ ≤ (G.edgesIn (S ∪ T)).ncard + (G.edgesIn (S ∩ T)).ncard :=
        Nat.add_le_add_right (Set.ncard_le_ncard h_union) _

theorem ncard_edgeSet_eq_card_edgeFinset (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeSet.ncard = G.edgeFinset.card := by
  rw [← Set.ncard_coe_finset, coe_edgeFinset]

theorem ncard_edgeSet_top_eq_card_choose_two [Fintype V] :
    ((⊤ : SimpleGraph V).edgeSet).ncard = (Fintype.card V).choose 2 := by
  classical
  rw [ncard_edgeSet_eq_card_edgeFinset, card_edgeFinset_top_eq_card_choose_two]

variable (G)

def IsSparse (k ℓ : ℕ) : Prop :=
  ∀ s : Finset V, ℓ ≤ k * s.card → (G.edgesIn ↑s).ncard + ℓ ≤ k * s.card

def IsTight (k ℓ : ℕ) : Prop :=
  G.IsSparse k ℓ ∧ G.edgeSet.ncard + ℓ = k * Nat.card V

def IsTightOn (k ℓ : ℕ) (s : Finset V) : Prop :=
  (G.edgesIn (↑s : Set V)).ncard + ℓ = k * s.card

variable {G}

theorem IsSparse.exists_one_le_degree_le_three [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsSparse 2 3)
    (hE : G.edgeSet.Nonempty) :
    ∃ v, 1 ≤ G.degree v ∧ G.degree v ≤ 3 := by
  classical
  by_contra hcontra
  push Not at hcontra
  set S : Finset V := Finset.univ.filter (fun v => 1 ≤ G.degree v) with hS_def
  obtain ⟨e, he⟩ := hE
  induction e with | h u v => ?_
  rw [mem_edgeSet] at he
  have huv : u ≠ v := G.ne_of_adj he
  have hdu : 1 ≤ G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨v, he⟩
  have hdv : 1 ≤ G.degree v := (G.degree_pos_iff_exists_adj v).mpr ⟨u, he.symm⟩
  have hu_in : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdu⟩
  have hv_in : v ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdv⟩
  have hS_ge2 : 2 ≤ S.card := by
    rw [show (2 : ℕ) = ({u, v} : Finset V).card from (Finset.card_pair huv).symm]
    refine Finset.card_le_card ?_
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have h_edgesIn : G.edgesIn (↑S : Set V) = G.edgeSet := by
    refine Set.eq_of_subset_of_subset (fun _ he => he.1) (fun e he => mem_edgesIn.mpr ⟨he, ?_⟩)
    induction e with | h x y => ?_
    rw [mem_edgeSet] at he
    rw [Sym2.coe_mk]
    rintro w (rfl | rfl)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (G.degree_pos_iff_exists_adj _).mpr ⟨_, he⟩⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (G.degree_pos_iff_exists_adj _).mpr ⟨_, he.symm⟩⟩)
  have h_deg_4 : ∀ w ∈ S, 4 ≤ G.degree w := fun w hw => by
    have h1 := (Finset.mem_filter.mp hw).2
    have := hcontra w h1; omega
  have h_sum_4 : (∑ _ ∈ S, (4 : ℕ)) ≤ ∑ w ∈ S, G.degree w :=
    Finset.sum_le_sum h_deg_4
  simp at h_sum_4
  have h_sum_eq : ∑ w ∈ S, G.degree w = ∑ w, G.degree w := by
    rw [hS_def]; exact Finset.sum_filter_of_ne fun w _ hw => by omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hEcoe := G.ncard_edgeSet_eq_card_edgeFinset
  have h_sparse_S := h S (by omega)
  rw [h_edgesIn] at h_sparse_S
  omega

theorem IsSparse.exists_nonadj_among_three_neighbors [Finite V]
    {G : SimpleGraph V} (h : G.IsSparse 2 3) {v a b c : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ G.Adj a b ∨ ¬ G.Adj a c ∨ ¬ G.Adj b c := by
  classical
  have : Fintype V := Fintype.ofFinite V
  by_contra hall
  push Not at hall
  obtain ⟨hab_e, hac_e, hbc_e⟩ := hall
  have hva : v ≠ a := G.ne_of_adj ha
  have hvb : v ≠ b := G.ne_of_adj hb
  have hvc : v ≠ c := G.ne_of_adj hc
  have hs_card : ({v, a, b, c} : Finset V).card = 4 := by
    grind [Finset.card_insert_of_notMem, Finset.card_singleton]
  set E : Finset (Sym2 V) :=
    {s(v, a), s(v, b), s(v, c), s(a, b), s(a, c), s(b, c)} with hE_def
  have hE_card : E.card = 6 := by
    rw [hE_def]
    grind [Finset.card_insert_of_notMem, Finset.card_singleton, Sym2.eq_iff]
  have hE_sub : (↑E : Set (Sym2 V)) ⊆ G.edgesIn (↑({v, a, b, c} : Finset V) : Set V) := by
    intro e he
    simp only [hE_def, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
               Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact mem_edgesIn.mpr ⟨by rwa [mem_edgeSet],
        by rw [Sym2.coe_mk]; rintro _ (rfl | rfl) <;> simp⟩
  have hsparse := h {v, a, b, c} (by omega)
  have h6_le : 6 ≤ (G.edgesIn (↑({v, a, b, c} : Finset V) : Set V)).ncard := by
    rw [← hE_card, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hE_sub
  omega

namespace Iso

variable {W : Type*} {H : SimpleGraph W}

lemma image_edgesIn (φ : G ≃g H) (s : Set V) :
    Sym2.map φ '' G.edgesIn s = H.edgesIn (φ '' s) := by
  ext e
  induction e with | h u v => ?_
  simp only [Sym2.mk_mem_image_map_iff, mem_edgesIn, mem_edgeSet, Sym2.coe_mk]
  constructor
  · rintro ⟨p, q, rfl, rfl, h_adj, hsub⟩
    refine ⟨φ.map_adj_iff.mpr h_adj, ?_⟩
    rintro x (rfl | rfl)
    · exact ⟨p, hsub (Or.inl rfl), rfl⟩
    · exact ⟨q, hsub (Or.inr rfl), rfl⟩
  · rintro ⟨h_adj, hsub⟩
    obtain ⟨p, hp, rfl⟩ := hsub (Or.inl rfl)
    obtain ⟨q, hq, rfl⟩ := hsub (Or.inr rfl)
    exact ⟨p, q, rfl, rfl, φ.map_adj_iff.mp h_adj,
      fun x hx => by rcases hx with rfl | rfl <;> assumption⟩

end Iso

lemma image_edgesIn_comap (G : SimpleGraph V) {V' : Type*} (f : V' → V) (s' : Set V') :
    Sym2.map f '' ((G.comap f).edgesIn s') = G.edgesIn (f '' s') := by
  ext e
  refine e.ind fun p q => ?_
  rw [Sym2.mk_mem_image_map_iff]
  simp only [mem_edgesIn, mem_edgeSet, comap_adj, Sym2.coe_mk, Set.insert_subset_iff,
             Set.singleton_subset_iff, Set.mem_image]
  constructor
  · rintro ⟨u, w, rfl, rfl, hadj, hu, hw⟩
    exact ⟨hadj, ⟨u, hu, rfl⟩, ⟨w, hw, rfl⟩⟩
  · rintro ⟨hadj, ⟨u, hu, rfl⟩, ⟨w, hw, rfl⟩⟩
    exact ⟨u, w, rfl, rfl, hadj, hu, hw⟩

lemma ncard_edgesIn_comap [DecidableEq V] {V' : Type*} (G : SimpleGraph V)
    {f : V' → V} (hf : Function.Injective f) (s' : Finset V') :
    ((G.comap f).edgesIn (↑s' : Set V')).ncard =
      (G.edgesIn (↑(s'.image f) : Set V)).ncard := by
  rw [Finset.coe_image, ← image_edgesIn_comap,
      Set.ncard_image_of_injective _ (Sym2.map.injective hf)]

theorem IsSparse.iso {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) {k ℓ : ℕ} (h : G.IsSparse k ℓ) : H.IsSparse k ℓ := by
  classical
  intro s hs
  set s' : Finset V := s.image φ.symm
  have hs'_card : s'.card = s.card :=
    Finset.card_image_of_injective s φ.symm.toEquiv.injective
  have h_eq : (H.edgesIn (↑s : Set W)).ncard = (G.edgesIn (↑s' : Set V)).ncard := by
    rw [show (↑s' : Set V) = φ.symm '' ↑s from Finset.coe_image, ← Iso.image_edgesIn φ.symm,
      Set.ncard_image_of_injective _ (Sym2.map.injective φ.symm.injective)]
  rw [h_eq, ← hs'_card]
  exact h s' (hs'_card ▸ hs)

theorem IsTight.iso {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) {k ℓ : ℕ} (h : G.IsTight k ℓ) : H.IsTight k ℓ := by
  refine ⟨h.1.iso φ, ?_⟩
  have hE : H.edgeSet.ncard = G.edgeSet.ncard := by
    simp only [← Nat.card_coe_set_eq]
    exact Nat.card_congr φ.mapEdgeSet.symm
  have hV : Nat.card W = Nat.card V := Nat.card_congr φ.toEquiv.symm
  grind only [h.2]

theorem IsSparse.comap {V' : Type*} {G : SimpleGraph V} {k ℓ : ℕ} (h : G.IsSparse k ℓ)
    {f : V' → V} (hf : Function.Injective f) : (G.comap f).IsSparse k ℓ := by
  classical
  intro s' hs'
  set S : Finset V := s'.image f
  have hS_card : S.card = s'.card := Finset.card_image_of_injective s' hf
  have h_link : ((G.comap f).edgesIn (↑s' : Set V')).ncard = (G.edgesIn (↑S : Set V)).ncard :=
    G.ncard_edgesIn_comap hf s'
  rw [h_link, ← hS_card]
  exact h S (hS_card ▸ hs')

theorem IsSparse.isTightOn_of_le {G : SimpleGraph V} {k ℓ : ℕ}
    (hG : G.IsSparse k ℓ) {s : Finset V} (hs : ℓ ≤ k * s.card)
    (h_le : k * s.card ≤ (G.edgesIn ↑s).ncard + ℓ) :
    G.IsTightOn k ℓ s := by
  grind only [IsTightOn, hG s hs]

theorem IsTightOn.union_inter [Finite V] [DecidableEq V] {G : SimpleGraph V} {k ℓ : ℕ}
    {s t : Finset V} (hs : G.IsTightOn k ℓ s) (ht : G.IsTightOn k ℓ t)
    (hG : G.IsSparse k ℓ) (h_inter : ℓ ≤ k * (s ∩ t).card) :
    G.IsTightOn k ℓ (s ∪ t) ∧ G.IsTightOn k ℓ (s ∩ t) := by
  have h_super := G.edgesIn_ncard_add_le (↑s : Set V) (↑t : Set V)
  rw [← Finset.coe_union, ← Finset.coe_inter] at h_super
  have h_sparse_inter := hG (s ∩ t) h_inter
  have h_sparse_union := hG (s ∪ t)
    (h_inter.trans (Nat.mul_le_mul_left k (Finset.card_le_card Finset.inter_subset_union)))
  have h_card_mul := Finset.mul_card_union_add_mul_card_inter s t k
  grind only [IsTightOn]

theorem IsTightOn.union_with_bonus [Finite V] [DecidableEq V] {G : SimpleGraph V} {k ℓ : ℕ}
    {S₁ S₂ : Finset V} (h₁ : G.IsTightOn k ℓ S₁) (h₂ : G.IsTightOn k ℓ S₂)
    (hG : G.IsSparse k ℓ) {F : Set (Sym2 V)}
    (hF_sub : F ⊆ G.edgesIn (↑(S₁ ∪ S₂) : Set V))
    (hF_disj : Disjoint F (G.edgesIn (↑S₁ : Set V) ∪ G.edgesIn (↑S₂ : Set V)))
    (h_close : (G.edgesIn (↑(S₁ ∩ S₂) : Set V)).ncard + ℓ ≤
               F.ncard + k * (S₁ ∩ S₂).card) :
    G.IsTightOn k ℓ (S₁ ∪ S₂) := by
  have h_un_sub :
      G.edgesIn (↑S₁ : Set V) ∪ G.edgesIn (↑S₂ : Set V) ⊆ G.edgesIn (↑(S₁ ∪ S₂) : Set V) := by
    rw [Finset.coe_union]
    exact Set.union_subset (edgesIn_mono Set.subset_union_left)
                           (edgesIn_mono Set.subset_union_right)
  have h_combined_sub :
      G.edgesIn (↑S₁ : Set V) ∪ G.edgesIn (↑S₂ : Set V) ∪ F ⊆ G.edgesIn (↑(S₁ ∪ S₂) : Set V) :=
    Set.union_subset h_un_sub hF_sub
  have h_inter_eq : G.edgesIn (↑S₁ : Set V) ∩ G.edgesIn (↑S₂ : Set V) =
                    G.edgesIn (↑(S₁ ∩ S₂) : Set V) := by
    rw [Finset.coe_inter]; exact (edgesIn_inter _ _).symm
  have h_un_card :
      (G.edgesIn (↑S₁ : Set V) ∪ G.edgesIn (↑S₂ : Set V)).ncard +
        (G.edgesIn (↑(S₁ ∩ S₂) : Set V)).ncard =
        (G.edgesIn (↑S₁ : Set V)).ncard + (G.edgesIn (↑S₂ : Set V)).ncard := by
    rw [← h_inter_eq]; exact Set.ncard_union_add_ncard_inter _ _
  have h_combined_card :
      (G.edgesIn (↑S₁ : Set V) ∪ G.edgesIn (↑S₂ : Set V) ∪ F).ncard =
        (G.edgesIn (↑S₁ : Set V) ∪ G.edgesIn (↑S₂ : Set V)).ncard + F.ncard :=
    Set.ncard_union_eq hF_disj.symm
      ((G.edgesIn_finite S₁).union (G.edgesIn_finite S₂)) ((G.edgesIn_finite _).subset hF_sub)
  have h_le_union :=
    Set.ncard_le_ncard h_combined_sub (G.edgesIn_finite (S₁ ∪ S₂))
  have h_card_mul := Finset.mul_card_union_add_mul_card_inter S₁ S₂ k
  have h_S1_size : ℓ ≤ k * S₁.card := by grind only [IsTightOn]
  have h_union_size : ℓ ≤ k * (S₁ ∪ S₂).card :=
    h_S1_size.trans (Nat.mul_le_mul_left k (Finset.card_le_card Finset.subset_union_left))
  refine hG.isTightOn_of_le h_union_size ?_
  grind only [IsTightOn]

theorem IsTightOn.insert_vertex_with_edges [DecidableEq V] {G : SimpleGraph V}
    {k ℓ : ℕ} {S : Finset V} (h : G.IsTightOn k ℓ S) (hG : G.IsSparse k ℓ)
    {w : V} (hw : w ∉ S) {F : Set (Sym2 V)}
    (hF_sub : F ⊆ G.edgesIn (↑(insert w S) : Set V))
    (hF_disj : Disjoint F (G.edgesIn (↑S : Set V))) (h_card : k ≤ F.ncard) :
    G.IsTightOn k ℓ (insert w S) := by
  have h_S_sub : G.edgesIn (↑S : Set V) ⊆ G.edgesIn (↑(insert w S) : Set V) := by
    refine edgesIn_mono ?_; rw [Finset.coe_insert]; exact Set.subset_insert _ _
  have h_combined_sub :
      G.edgesIn (↑S : Set V) ∪ F ⊆ G.edgesIn (↑(insert w S) : Set V) :=
    Set.union_subset h_S_sub hF_sub
  have h_combined_card :
      (G.edgesIn (↑S : Set V) ∪ F).ncard = (G.edgesIn (↑S : Set V)).ncard + F.ncard :=
    Set.ncard_union_eq hF_disj.symm (G.edgesIn_finite S) ((G.edgesIn_finite _).subset hF_sub)
  have h_le := Set.ncard_le_ncard h_combined_sub (G.edgesIn_finite (insert w S))
  have h_card_insert : (insert w S).card = S.card + 1 := Finset.card_insert_of_notMem hw
  have h_size : ℓ ≤ k * (insert w S).card := by
    unfold IsTightOn at h
    rw [h_card_insert, Nat.mul_add, Nat.mul_one]; omega
  refine hG.isTightOn_of_le h_size ?_
  rw [h_card_insert, Nat.mul_add, Nat.mul_one] at h_size ⊢
  grind only [IsTightOn]

end SimpleGraph
