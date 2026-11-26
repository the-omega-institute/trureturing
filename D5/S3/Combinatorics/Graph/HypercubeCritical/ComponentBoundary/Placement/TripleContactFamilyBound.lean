/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/TripleContactFamilyBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/TripleContactFamilyBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: A triple family with three extensions per pair is complete on five axes or has at least fifteen members. -/

module

public import Mathlib.Data.Finset.Powerset

import all D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.MinimumContactDisplacementCount

import Batteries.Tactic.OpenPrivate

/-! Near-minimal triple families with at least three extensions per pair. -/

set_option linter.style.longLine false
set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.TripleContactFamilyBound

open Finset
open scoped BigOperators
open private axes extensions link mem_axes mem_extensions mem_link extensions_link sum_link_card
  weight_count from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.MinimumContactDisplacementCount

variable {α : Type*} [DecidableEq α]

private theorem subset_axes_powersetCard {F : Finset (Finset α)} {d : ℕ}
    (hsize : ∀ T ∈ F, T.card = d) : F ⊆ (axes F).powersetCard d := by
  intro T hT
  exact Finset.mem_powersetCard.mpr ⟨fun i hi => mem_axes.mpr ⟨T, hT, hi⟩, hsize T hT⟩

private theorem mem_axes_link {F : Finset (Finset α)} {a b : α} :
    b ∈ axes (link F a) ↔ a ≠ b ∧ ∃ T ∈ F, a ∈ T ∧ b ∈ T := by
  constructor
  · intro hb
    obtain ⟨S, hS, hbS⟩ := mem_axes.mp hb
    obtain ⟨haS, hT⟩ := mem_link.mp hS
    exact ⟨fun hab => haS (hab.symm ▸ hbS), insert a S, hT,
      Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hbS⟩
  · rintro ⟨hab, T, hT, haT, hbT⟩
    refine mem_axes.mpr ⟨T.erase a, mem_link.mpr ⟨Finset.notMem_erase _ _, ?_⟩,
      Finset.mem_erase.mpr ⟨hab.symm, hbT⟩⟩
    rwa [Finset.insert_erase haT]

private theorem mem_axes_link_symm {F : Finset (Finset α)} {a b : α}
    (hb : b ∈ axes (link F a)) : a ∈ axes (link F b) := by
  obtain ⟨hab, T, hT, haT, hbT⟩ := mem_axes_link.mp hb
  exact mem_axes_link.mpr ⟨hab.symm, T, hT, hbT, haT⟩

private theorem axes_link_subset_erase {F : Finset (Finset α)} {a : α} :
    axes (link F a) ⊆ (axes F).erase a := by
  intro b hb
  obtain ⟨hab, T, hT, _, hbT⟩ := mem_axes_link.mp hb
  exact Finset.mem_erase.mpr ⟨hab.symm, mem_axes.mpr ⟨T, hT, hbT⟩⟩

private theorem triple_link_card_bounds {F : Finset (Finset α)}
    (hsize : ∀ T ∈ F, T.card = 3)
    (hthree : ∀ T ∈ F, ∀ i ∈ T, 3 ≤ (extensions F (T.erase i)).card)
    (a : α) (ha : a ∈ axes F) :
    (∀ S ∈ link F a, S.card = 2) ∧ 6 ≤ (link F a).card ∧
      4 ≤ (axes (link F a)).card ∧ 3 * (axes (link F a)).card ≤ 2 * (link F a).card := by
  obtain ⟨T, hT, haT⟩ := mem_axes.mp ha
  have hne : (link F a).Nonempty := by
    refine ⟨T.erase a, mem_link.mpr ⟨Finset.notMem_erase _ _, ?_⟩⟩
    rwa [Finset.insert_erase haT]
  have hsize' (S : Finset α) (hS : S ∈ link F a) : S.card = 2 := by
    obtain ⟨haS, hSF⟩ := mem_link.mp hS
    have h := hsize _ hSF
    rw [Finset.card_insert_of_notMem haS] at h
    omega
  have hthree' (S : Finset α) (hS : S ∈ link F a) (j : α) (hj : j ∈ S) :
      3 ≤ (extensions (link F a) (S.erase j)).card := by
    obtain ⟨haS, hSF⟩ := mem_link.mp hS
    have haj : a ≠ j := fun h => haS (h.symm ▸ hj)
    have h := hthree _ hSF j (Finset.mem_insert_of_mem hj)
    rw [Finset.erase_insert_of_ne haj] at h
    rwa [extensions_link (fun hh => haS (Finset.mem_of_mem_erase hh))]
  obtain ⟨hcard, h⟩ := weight_count 2 _ hne hsize' hthree'
  obtain ⟨haxes, hdouble⟩ := h (by decide)
  refine ⟨hsize', hcard, haxes, ?_⟩
  rw [Nat.mul_comm 3]
  exact hdouble

private theorem sum_triple_link_card {F : Finset (Finset α)}
    (hsize : ∀ T ∈ F, T.card = 3) :
    (∑ i ∈ axes F, (link F i).card) = 3 * F.card := by
  calc
    _ = ∑ T ∈ F, T.card := sum_link_card F
    _ = ∑ _T ∈ F, (3 : ℕ) := Finset.sum_congr rfl hsize
    _ = _ := by simp [Nat.mul_comm]

private theorem six_axes_triple_family {F : Finset (Finset α)}
    (hsize : ∀ T ∈ F, T.card = 3)
    (hthree : ∀ T ∈ F, ∀ i ∈ T, 3 ≤ (extensions F (T.erase i)).card)
    (hA : (axes F).card = 6) :
    15 ≤ F.card ∧ ((axes F).powersetCard 3 \ F).card ≤ 5 := by
  -- An occurring pair needs three of its four possible extensions.
  have absent_of_two {a b u v : α} (hu : u ∈ axes F) (hv : v ∈ axes F) (huv : u ≠ v)
      (huS : u ∉ ({a, b} : Finset α)) (hvS : v ∉ ({a, b} : Finset α))
      (hFu : insert u ({a, b} : Finset α) ∉ F) (hFv : insert v ({a, b} : Finset α) ∉ F) :
      b ∉ axes (link F a) := by
    intro hb
    obtain ⟨hab, T, hT, haT, hbT⟩ := mem_axes_link.mp hb
    let S : Finset α := {a, b}
    have hST : S ⊆ T :=
      Finset.insert_subset_iff.mpr ⟨haT, Finset.singleton_subset_iff.mpr hbT⟩
    have hSA : S ⊆ axes F := fun _ hx => mem_axes.mpr ⟨T, hT, hST hx⟩
    have hS : S.card = 2 := Finset.card_pair hab
    have hTc := hsize T hT
    have hproper : S ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hST, fun heq => by
      have hc := congrArg Finset.card heq
      omega⟩
    obtain ⟨k, hkT, hkS⟩ := Finset.exists_of_ssubset hproper
    have herase : S = T.erase k := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        exact Finset.mem_erase.mpr ⟨fun heq => hkS (heq ▸ hx), hST hx⟩
      · have hc := Finset.card_erase_add_one hkT
        omega
    have hext : 3 ≤ (extensions F S).card := by
      rw [herase]
      exact hthree T hT k hkT
    let P := axes F \ S
    have hP : P.card = 4 := by
      change ((axes F) \ S).card = 4
      rw [Finset.card_sdiff_of_subset hSA, hA, hS]
    have huP : u ∈ P := Finset.mem_sdiff.mpr ⟨hu, huS⟩
    have hvP : v ∈ P.erase u :=
      Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_sdiff.mpr ⟨hv, hvS⟩⟩
    have hsub : extensions F S ⊆ (P.erase u).erase v := by
      intro x hx
      obtain ⟨hxS, hxF⟩ := mem_extensions.mp hx
      have hxu : x ≠ u := fun h => hFu (h ▸ hxF)
      have hxv : x ≠ v := fun h => hFv (h ▸ hxF)
      exact Finset.mem_erase.mpr ⟨hxv, Finset.mem_erase.mpr ⟨hxu,
        Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hx).1, hxS⟩⟩⟩
    have hle := Finset.card_le_card hsub
    have hcu := Finset.card_erase_add_one huP
    have hcv := Finset.card_erase_add_one hvP
    omega
  have forbidden {a b : α} {T : Finset α} (hab : a ≠ b) (habs : b ∉ axes (link F a))
      (haT : a ∈ T) (hbT : b ∈ T) : T ∉ F :=
    fun hT => habs (mem_axes_link.mpr ⟨hab, T, hT, haT, hbT⟩)
  -- Two absent pairs at one axis would rule out every neighbor of that axis.
  have no_shared {a b c : α} (ha : a ∈ axes F) (hb : b ∈ axes F) (hc : c ∈ axes F)
      (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (habs : b ∉ axes (link F a)) (habs' : c ∉ axes (link F a)) : False := by
    have hdeg := (triple_link_card_bounds hsize hthree a ha).2.2.1
    obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < (axes (link F a)).card by omega)
    have heb : e ≠ b := fun h => habs (h ▸ he)
    have hec : e ≠ c := fun h => habs' (h ▸ he)
    exact (absent_of_two (a := a) (b := e) hb hc hbc
      (by simp [hab.symm, heb.symm]) (by simp [hac.symm, hec.symm])
      (forbidden hab habs (by simp) (by simp)) (forbidden hac habs' (by simp) (by simp))) he
  have hlarge {i : α} (hi : i ∈ axes F) (hfull : (axes F).erase i ⊆ axes (link F i)) :
      8 ≤ (link F i).card := by
    have herase := Finset.card_erase_add_one hi
    have hdeg := Finset.card_le_card hfull
    have hdouble := (triple_link_card_bounds hsize hthree i hi).2.2.2
    omega
  have hsum := sum_triple_link_card hsize
  have hbound : 15 ≤ F.card := by
    by_cases hmissing : ∃ a ∈ axes F, ∃ b ∈ (axes F).erase a, b ∉ axes (link F a)
    · obtain ⟨a, ha, b, hba, habs⟩ := hmissing
      obtain ⟨hne, hb⟩ := Finset.mem_erase.mp hba
      have hab := hne.symm
      have habs' : a ∉ axes (link F b) := fun h => habs (mem_axes_link_symm h)
      have hfull (i : α) (hi : i ∈ axes F) (hia : i ≠ a) (hib : i ≠ b) :
          (axes F).erase i ⊆ axes (link F i) := by
        have hai : i ∈ axes (link F a) := by
          by_contra h
          exact no_shared ha hb hi hab hia.symm hib.symm habs h
        have hbi : i ∈ axes (link F b) := by
          by_contra h
          exact no_shared hb ha hi hne hib.symm hia.symm habs' h
        intro j hj
        obtain ⟨hji, hjA⟩ := Finset.mem_erase.mp hj
        by_contra hij
        have hja : j ≠ a := by
          intro h
          subst j
          exact hij (mem_axes_link_symm hai)
        have hbj : b ≠ j := by
          intro h
          subst j
          exact hij (mem_axes_link_symm hbi)
        -- The missing pairs ab and ij would remove two extensions of ai.
        exact (absent_of_two (a := a) (b := i) hb hjA hbj
          (by simp [hne, hib.symm]) (by simp [hja, hji])
          (forbidden hab habs (by simp) (by simp))
          (forbidden hji.symm hij (by simp) (by simp))) hai
      let B := ((axes F).erase a).erase b
      have htail : 8 * B.card ≤ ∑ i ∈ B, (link F i).card := by
        calc
          _ = ∑ _i ∈ B, (8 : ℕ) := by simp [Nat.mul_comm]
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro i hi
            obtain ⟨hib, hi'⟩ := Finset.mem_erase.mp hi
            obtain ⟨hia, hiA⟩ := Finset.mem_erase.mp hi'
            exact hlarge hiA (hfull i hiA hia hib)
      have ha6 := (triple_link_card_bounds hsize hthree a ha).2.1
      have hb6 := (triple_link_card_bounds hsize hthree b hb).2.1
      have hca := Finset.card_erase_add_one ha
      have hcb := Finset.card_erase_add_one hba
      have hsa := Finset.sum_erase_add (axes F) (fun i => (link F i).card) ha
      have hsb := Finset.sum_erase_add ((axes F).erase a) (fun i => (link F i).card) hba
      change 8 * (((axes F).erase a).erase b).card ≤
        ∑ i ∈ ((axes F).erase a).erase b, (link F i).card at htail
      omega
    · have hall : 8 * (axes F).card ≤ ∑ i ∈ axes F, (link F i).card := by
        calc
          _ = ∑ _i ∈ axes F, (8 : ℕ) := by simp [Nat.mul_comm]
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro i hi
            apply hlarge hi
            intro j hj
            by_contra hij
            exact hmissing ⟨i, hi, j, hj, hij⟩
      omega
  refine ⟨hbound, ?_⟩
  rw [Finset.card_sdiff_of_subset (subset_axes_powersetCard hsize), Finset.card_powersetCard, hA]
  change 20 - F.card ≤ 5
  omega

private theorem seven_axes_triple_family {F : Finset (Finset α)}
    (hsize : ∀ T ∈ F, T.card = 3)
    (hthree : ∀ T ∈ F, ∀ i ∈ T, 3 ≤ (extensions F (T.erase i)).card)
    (hA : (axes F).card = 7) : 15 ≤ F.card := by
  by_contra hbound
  have hsum := sum_triple_link_card hsize
  have hmin (i : α) (hi : i ∈ axes F) : 6 ≤ (link F i).card :=
    (triple_link_card_bounds hsize hthree i hi).2.1
  have h6 (i : α) (hi : i ∈ axes F) : (link F i).card = 6 := by
    by_contra h
    have hlt : 6 < (link F i).card := by
      have hle := hmin i hi
      omega
    have hsum' : (∑ _j ∈ axes F, (6 : ℕ)) < ∑ j ∈ axes F, (link F j).card :=
      Finset.sum_lt_sum hmin ⟨i, hi, hlt⟩
    simp [hA] at hsum'
    omega
  have h4 (i : α) (hi : i ∈ axes F) : (axes (link F i)).card = 4 := by
    obtain ⟨_, _, hlo, hhi⟩ := triple_link_card_bounds hsize hthree i hi
    have hc := h6 i hi
    omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < (axes F).card by omega)
  have hcomplete : link F a = (axes (link F a)).powersetCard 2 := by
    apply Finset.eq_of_subset_of_card_le
      (subset_axes_powersetCard (triple_link_card_bounds hsize hthree a ha).1)
    rw [Finset.card_powersetCard, h4 a ha, h6 a ha] <;> decide
  let C := insert a (axes (link F a))
  have hC : C ⊆ axes F := Finset.insert_subset_iff.mpr
    ⟨ha, fun i hi => Finset.mem_of_mem_erase (axes_link_subset_erase hi)⟩
  have hCa' : a ∉ axes (link F a) := fun h => (mem_axes_link.mp h).1 rfl
  have hCcard : C.card = 5 := by
    change (insert a (axes (link F a))).card = 5
    rw [Finset.card_insert_of_notMem hCa', h4 a ha]
  have hclique {j k : α} (hj : j ∈ C) (hk : k ∈ C) (hjk : j ≠ k) :
      k ∈ axes (link F j) := by
    rcases Finset.mem_insert.mp hj with hja | hj
    · subst j
      exact (Finset.mem_insert.mp hk).resolve_left hjk.symm
    rcases Finset.mem_insert.mp hk with hka | hk
    · subst k
      exact mem_axes_link_symm hj
    have hpair : ({j, k} : Finset α) ∈ link F a := by
      rw [hcomplete]
      exact Finset.mem_powersetCard.mpr ⟨Finset.insert_subset_iff.mpr
        ⟨hj, Finset.singleton_subset_iff.mpr hk⟩, Finset.card_pair hjk⟩
    exact mem_axes_link.mpr ⟨hjk, _, (mem_link.mp hpair).2, by simp, by simp⟩
  have hclosed (j : α) (hj : j ∈ C) : axes (link F j) = C.erase j := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      obtain ⟨hkj, hkC⟩ := Finset.mem_erase.mp hk
      exact hclique hj hkC hkj.symm
    · have hc := Finset.card_erase_add_one hj
      have hd := h4 j (hC hj)
      omega
  have hproper : C ⊂ axes F := Finset.ssubset_iff_subset_ne.mpr ⟨hC, fun heq => by
    have hc := congrArg Finset.card heq
    omega⟩
  obtain ⟨b, hb, hbC⟩ := Finset.exists_of_ssubset hproper
  have hsub : axes (link F b) ⊆ axes F \ C := by
    intro j hj
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase (axes_link_subset_erase hj), ?_⟩
    intro hjC
    have h := mem_axes_link_symm hj
    rw [hclosed j hjC] at h
    exact hbC (Finset.mem_of_mem_erase h)
  have hle := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hC, hA, hCcard, h4 b hb] at hle
  omega

/-- A nonempty triple family with at least three extensions of each occurring pair either
contains all triples on five axes or has at least fifteen members. -/
public theorem eq_five_axis_powerset_or_card_ge_fifteen_of_three_extensions
    (F : Finset (Finset α)) (hne : F.Nonempty) (hsize : ∀ T ∈ F, T.card = 3)
    (hthree : ∀ T ∈ F, ∀ i ∈ T,
      ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        (∀ j ∈ ({a, b, c} : Finset α), j ∉ T.erase i ∧ insert j (T.erase i) ∈ F)) :
    (∃ A : Finset α, A.card = 5 ∧ F = A.powersetCard 3) ∨ 15 ≤ F.card := by
  have hext (T : Finset α) (hT : T ∈ F) (i : α) (hi : i ∈ T) :
      3 ≤ (extensions F (T.erase i)).card := by
    obtain ⟨a, b, c, hab, hac, hbc, he⟩ := hthree T hT i hi
    have hsub : ({a, b, c} : Finset α) ⊆ extensions F (T.erase i) :=
      fun j hj => mem_extensions.mpr (he j hj)
    simpa [hab, hac, hbc] using Finset.card_le_card hsub
  obtain ⟨hmin, h⟩ := weight_count 3 F hne hsize hext
  obtain ⟨haxes, hdouble⟩ := h (by decide)
  change 10 ≤ F.card at hmin
  change 5 ≤ (axes F).card at haxes
  change (axes F).card * 6 ≤ 3 * F.card at hdouble
  by_cases h5 : (axes F).card = 5
  · refine Or.inl ⟨axes F, h5, ?_⟩
    apply Finset.eq_of_subset_of_card_le (subset_axes_powersetCard hsize)
    rw [Finset.card_powersetCard, h5]
    exact hmin
  by_cases h6 : (axes F).card = 6
  · exact Or.inr (six_axes_triple_family hsize hext h6).1
  by_cases h7 : (axes F).card = 7
  · exact Or.inr (seven_axes_triple_family hsize hext h7)
  exact Or.inr (by omega)

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.TripleContactFamilyBound
