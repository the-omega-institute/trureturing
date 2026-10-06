/- GID: D5/S3/Combinatorics/Graph/PairSelectionRerouting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PairSelectionRerouting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset, mathlib/module/Mathlib.Data.Finset.Max]
   utility: none
   digest: Pair selections in hereditarily sparse indexed graphs have only rigid four-cliques. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Choose

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PairSelectionRerouting

open Finset

variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]

/-- Each indexed owner selects two distinct vertices from its own support. -/
def Selects (R e : I → Finset V) : Prop :=
  ∀ i, e i ⊆ R i ∧ (e i).card = 2

/-- Every vertex set contains at most three halves as many indexed edges as vertices.
Owners with the same selected pair are counted separately. -/
def Sparse (e : I → Finset V) : Prop :=
  ∀ S : Finset V, 2 * (univ.filter (fun i => e i ⊆ S)).card ≤ 3 * S.card

/-- Four-cliques of the underlying simple graph, counted by their vertex sets. -/
def cliques (e : I → Finset V) : Finset (Finset V) :=
  (univ.powersetCard 4).filter fun C => C.powersetCard 2 ⊆ univ.image e

private theorem mem_cliques (e : I → Finset V) (C : Finset V) :
    C ∈ cliques e ↔ C.card = 4 ∧ C.powersetCard 2 ⊆ univ.image e := by
  simp [cliques]

omit [Fintype V] in
private theorem edge_family_density (e : I → Finset V) (hs : Sparse e)
    (S : Finset V) (E : Finset (Finset V))
    (hE : ∀ a ∈ E, a ∈ univ.image e ∧ a ⊆ S) : 2 * E.card ≤ 3 * S.card := by
  have hsub : E ⊆ (univ.filter (fun i => e i ⊆ S)).image e := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := mem_image.mp (hE a ha).1
    exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ i, (hE _ ha).2⟩, rfl⟩
  have hc := (card_le_card hsub).trans card_image_le
  have hd := hs S
  omega

private theorem owner_unique_of_clique (e : I → Finset V) (hs : Sparse e)
    (C : Finset V) (hC : C ∈ cliques e) (i j : I)
    (hi : e i ⊆ C) (hj : e j ⊆ C) (he : e i = e j) : i = j := by
  obtain ⟨hC4, hCp⟩ := (mem_cliques e C).mp hC
  let owners := univ.filter (fun i => e i ⊆ C)
  have hsub : C.powersetCard 2 ⊆ owners.image e := by
    intro a ha
    obtain ⟨k, _, rfl⟩ := mem_image.mp (hCp ha)
    exact mem_image.mpr ⟨k, mem_filter.mpr ⟨mem_univ k,
      (mem_powersetCard.mp ha).1⟩, rfl⟩
  have hlow : 6 ≤ (owners.image e).card := by
    simpa [card_powersetCard, hC4, Nat.choose] using card_le_card hsub
  have hd := hs C
  change 2 * owners.card ≤ 3 * C.card at hd
  have him := card_image_le (s := owners) (f := e)
  have heq : (owners.image e).card = owners.card := by omega
  exact card_image_iff.mp heq (by simpa [owners] using hi)
    (by simpa [owners] using hj) he

omit [Fintype V] in
private theorem near_clique_incompatible (e : I → Finset V) (hs : Sparse e)
    (C D a : Finset V) (hC4 : C.card = 4) (hD4 : D.card = 4)
    (hint : (C ∩ D).Nonempty) (hout : ¬D ⊆ C)
    (ha : a ∈ C.powersetCard 2)
    (hC : (C.powersetCard 2).erase a ⊆ univ.image e)
    (hD : D.powersetCard 2 ⊆ univ.image e) : False := by
  let A := (C.powersetCard 2).erase a
  let B := D.powersetCard 2
  have hAc : A.card = 5 := by simp [A, card_erase_of_mem ha, card_powersetCard, hC4, Nat.choose]
  have hBc : B.card = 6 := by simp [B, card_powersetCard, hD4, Nat.choose]
  have hsub : A ∩ B ⊆ (C ∩ D).powersetCard 2 := by
    intro b hb
    obtain ⟨hbA, hbB⟩ := mem_inter.mp hb
    have hbc := mem_powersetCard.mp (mem_erase.mp hbA).2
    have hbd := mem_powersetCard.mp hbB
    exact mem_powersetCard.mpr ⟨subset_inter hbc.1 hbd.1, hbc.2⟩
  have hcap := card_le_card hsub
  rw [card_powersetCard] at hcap
  have hpos : 1 ≤ (C ∩ D).card := card_pos.mpr hint
  have hlt : (C ∩ D).card < 4 := by
    have hle := card_le_card (inter_subset_right : C ∩ D ⊆ D)
    by_contra h
    have heq : C ∩ D = D := eq_of_subset_of_card_le inter_subset_right (by omega)
    exact hout (heq ▸ inter_subset_left)
  have hcunion := card_union_add_card_inter C D
  have heunion := card_union_add_card_inter A B
  have hd := edge_family_density e hs (C ∪ D) (A ∪ B) (by
    intro b hb
    rcases mem_union.mp hb with hb | hb
    · exact ⟨hC hb, (mem_powersetCard.mp (mem_erase.mp hb).2).1.trans subset_union_left⟩
    · exact ⟨hD hb, (mem_powersetCard.mp hb).1.trans subset_union_right⟩)
  have hcases : (C ∩ D).card = 1 ∨ (C ∩ D).card = 2 ∨ (C ∩ D).card = 3 := by omega
  rcases hcases with ht | ht | ht
  · rw [ht, show Nat.choose 1 2 = 0 by decide] at hcap
    omega
  · rw [ht, show Nat.choose 2 2 = 1 by decide] at hcap
    omega
  · rw [ht, show Nat.choose 3 2 = 3 by decide] at hcap
    omega

variable [DecidableEq I]

private theorem reroute_decreases (e : I → Finset V) (he : ∀ i, (e i).card = 2)
    (hs : Sparse e) (C : Finset V) (hC : C ∈ cliques e)
    (i : I) (u v w : V) (hei : e i = {u, v}) (hiC : e i ⊆ C)
    (hwu : w ≠ u) (hwv : w ≠ v)
    (hs' : Sparse (Function.update e i {u, w})) :
    cliques (Function.update e i {u, w}) ⊂ cliques e := by
  let e' := Function.update e i {u, w}
  obtain ⟨hC4, hCp⟩ := (mem_cliques e C).mp hC
  have huC : u ∈ C := hiC (by simp [hei])
  have heiC : e i ∈ C.powersetCard 2 := mem_powersetCard.mpr ⟨hiC, he i⟩
  have hpersist : (C.powersetCard 2).erase (e i) ⊆ univ.image e' := by
    intro a ha
    obtain ⟨j, _, hja⟩ := mem_image.mp (hCp (mem_erase.mp ha).2)
    have hji : j ≠ i := by
      intro h
      subst j
      exact (mem_erase.mp ha).1 hja.symm
    exact mem_image.mpr ⟨j, mem_univ j, by simpa [e', hji] using hja⟩
  have hgone : C ∉ cliques e' := by
    intro hC'
    obtain ⟨j, _, hj⟩ := mem_image.mp (((mem_cliques e' C).mp hC').2 heiC)
    by_cases hji : j = i
    · subst j
      have heq : ({u, w} : Finset V) = {u, v} := by simpa [e', hei] using hj
      have hw : w ∈ ({u, v} : Finset V) := heq ▸ (by simp)
      simp [hwu, hwv] at hw
    · have heq : e j = e i := by simpa [e', hji] using hj
      exact hji (owner_unique_of_clique e hs C hC j i (heq ▸ hiC) hiC heq)
  have hsub : cliques e' ⊆ cliques e := by
    intro D hD
    obtain ⟨hD4, hDp⟩ := (mem_cliques e' D).mp hD
    by_cases hwC : w ∈ C
    · apply (mem_cliques e D).mpr
      refine ⟨hD4, ?_⟩
      intro a ha
      obtain ⟨j, _, hja⟩ := mem_image.mp (hDp ha)
      by_cases hji : j = i
      · subst j
        have hnewC : ({u, w} : Finset V) ∈ C.powersetCard 2 :=
          mem_powersetCard.mpr ⟨by
            simpa only [insert_subset_iff, singleton_subset_iff] using And.intro huC hwC,
            card_pair (Ne.symm hwu)⟩
        have haeq : ({u, w} : Finset V) = a := by simpa [e'] using hja
        exact haeq ▸ hCp hnewC
      · exact mem_image.mpr ⟨j, mem_univ j, by simpa [e', hji] using hja⟩
    · by_cases hnewD : ({u, w} : Finset V) ⊆ D
      · exfalso
        apply near_clique_incompatible e' hs' C D (e i) hC4 hD4
        · exact ⟨u, mem_inter.mpr ⟨huC, hnewD (by simp)⟩⟩
        · intro hDC
          exact hwC (hDC (hnewD (by simp)))
        · exact heiC
        · exact hpersist
        · exact hDp
      · apply (mem_cliques e D).mpr
        refine ⟨hD4, ?_⟩
        intro a ha
        obtain ⟨j, _, hja⟩ := mem_image.mp (hDp ha)
        have hji : j ≠ i := by
          intro h
          subst j
          have haeq : ({u, w} : Finset V) = a := by simpa [e'] using hja
          exact hnewD (haeq ▸ (mem_powersetCard.mp ha).1)
        exact mem_image.mpr ⟨j, mem_univ j, by simpa [e', hji] using hja⟩
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by intro h; exact hgone (h.symm ▸ hC)⟩

omit [DecidableEq I] in
/-- In a selection with the fewest four-cliques, every owner whose edge is inside a
four-clique has a support of exactly two vertices. Sparsity must hold for all legal
selections, including the one obtained by rerouting a single edge. -/
theorem minimal_selection_rigid (R e : I → Finset V) (he : Selects R e)
    (hs : ∀ f, Selects R f → Sparse f)
    (hmin : ∀ f, Selects R f → (cliques e).card ≤ (cliques f).card) :
    ∀ C ∈ cliques e, ∀ i, e i ⊆ C → (R i).card = 2 := by
  classical
  intro C hC i hiC
  obtain ⟨u, v, huv, hei⟩ := card_eq_two.mp (he i).2
  by_contra hRi
  have hnot : ¬R i ⊆ e i := by
    intro hsub
    have hlow := card_le_card (he i).1
    have hupp := card_le_card hsub
    have htwo := (he i).2
    omega
  obtain ⟨w, hwR, hwn⟩ := not_subset.mp hnot
  have hwu : w ≠ u := by intro h; exact hwn (by simp [hei, h])
  have hwv : w ≠ v := by intro h; exact hwn (by simp [hei, h])
  let f := Function.update e i {u, w}
  have hf : Selects R f := by
    intro j
    by_cases hji : j = i
    · subst j
      have huR : u ∈ R i := (he i).1 (by simp [hei])
      simp only [f, Function.update_self]
      exact ⟨by simpa only [insert_subset_iff, singleton_subset_iff] using And.intro huR hwR,
        card_pair (Ne.symm hwu)⟩
    · simpa only [f, Function.update_of_ne hji] using he j
  have hlt := card_lt_card (reroute_decreases e (fun j => (he j).2)
    (hs e he) C hC i u v w hei hiC hwu hwv (hs f hf))
  change (cliques f).card < (cliques e).card at hlt
  have hle := hmin f hf
  omega

omit [DecidableEq I] in
/-- If all legal pair selections satisfy hereditary indexed sparsity, there is a
selection whose four-cliques use only owners with two-element supports. -/
theorem exists_rigid_selection (R : I → Finset V) (hR : ∀ i, 2 ≤ (R i).card)
    (hs : ∀ e, Selects R e → Sparse e) :
    ∃ e, Selects R e ∧ ∀ C ∈ cliques e, ∀ i, e i ⊆ C → (R i).card = 2 := by
  classical
  choose e0 he0 using fun i => exists_subset_card_eq (hR i)
  let choices : Finset (I → Finset V) := univ.filter (Selects R)
  have hn : choices.Nonempty := ⟨e0, mem_filter.mpr ⟨mem_univ e0, he0⟩⟩
  obtain ⟨e, he, hmin⟩ := choices.exists_min_image (fun e => (cliques e).card) hn
  have hsel : Selects R e := (mem_filter.mp he).2
  refine ⟨e, hsel, minimal_selection_rigid R e hsel hs ?_⟩
  intro f hf
  exact hmin f (mem_filter.mpr ⟨mem_univ f, hf⟩)

end D5.S3.Combinatorics.Graph.PairSelectionRerouting
