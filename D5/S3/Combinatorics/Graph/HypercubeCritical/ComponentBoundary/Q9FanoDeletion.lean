/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FanoDeletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FanoDeletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: A tight Fano deletion requires at least seven link edges. -/

module

public import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SingletonFiveMask
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! Deletion incidence counts constrain extensions of tight seven-point triple covers. -/

set_option autoImplicit false

public section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FanoDeletion

open Finset
open Q9SingletonFiveMask (trace trace_uniform double_cover_trace seven_point_pair_degree)
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- The triples containing a specified vertex. -/
abbrev q9Star (F : Finset (Finset α)) (x : α) : Finset (Finset α) :=
  F.filter (x ∈ ·)

/-- The triples containing all members of a specified subset. -/
abbrev q9Through (F : Finset (Finset α)) (p : Finset α) : Finset (Finset α) :=
  F.filter (p ⊆ ·)

private theorem q9_sum_pair_degrees_at {F : Finset (Finset α)} {S : Finset α}
    (hF : F ⊆ S.powersetCard 3) (x : α) :
    (∑ y ∈ S.erase x, (q9Through F {x, y}).card) = (q9Star F x).card * 2 := by
  let r := fun (y : α) (t : Finset α) => y ∈ t
  have habove (y : α) : (q9Star F x).bipartiteAbove r y = q9Through F {x, y} := by
    ext t
    simp only [bipartiteAbove, r, q9Star, q9Through, mem_filter, insert_subset_iff,
      singleton_subset_iff]
    tauto
  calc
    _ = ∑ t ∈ q9Star F x, ((S.erase x).bipartiteBelow r t).card := by
      simpa only [habove] using
        (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (s := S.erase x) (t := q9Star F x) r)
    _ = ∑ _t ∈ q9Star F x, 2 := by
      apply sum_congr rfl
      intro t ht
      obtain ⟨htF, hxt⟩ := mem_filter.mp ht
      obtain ⟨htS, htc⟩ := mem_powersetCard.mp (hF htF)
      have he : (S.erase x).bipartiteBelow r t = t.erase x := by
        ext y
        simp only [mem_bipartiteBelow, r, mem_erase]
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, htS h.2⟩, h.2⟩⟩
      rw [he, card_erase_of_mem hxt, htc]
    _ = _ := by simp

private theorem q9_trace_sdiff_add_card {F : Finset (Finset α)} {S p : Finset α}
    (hF : F ⊆ S.powersetCard 3) :
    (trace F (S \ p)).card + (F.filter (fun t => ∃ x ∈ p, x ∈ t)).card = F.card := by
  classical
  let meets := fun t : Finset α => ∃ x ∈ p, x ∈ t
  have he : trace F (S \ p) = F.filter (fun t => ¬meets t) := by
    ext t
    simp only [trace, mem_filter]
    constructor
    · intro ⟨htF, ht⟩
      exact ⟨htF, fun ⟨x, hxp, hxt⟩ => (mem_sdiff.mp (ht hxt)).2 hxp⟩
    · intro ⟨htF, ht⟩
      exact ⟨htF, fun x hxt => mem_sdiff.mpr
        ⟨(mem_powersetCard.mp (hF htF)).1 hxt, fun hxp => ht ⟨x, hxp, hxt⟩⟩⟩
  rw [he, Nat.add_comm]
  exact card_filter_add_card_filter_not meets

/-- Count surviving triples after deleting two points by inclusion-exclusion. -/
theorem q9_trace_sdiff_pair {F : Finset (Finset α)} {S : Finset α}
    (hF : F ⊆ S.powersetCard 3) (a b : α) :
    (trace F (S \ {a, b})).card + (q9Star F a).card + (q9Star F b).card =
      F.card + (q9Through F {a, b}).card := by
  classical
  have hu : (F.filter fun t => ∃ x ∈ ({a, b} : Finset α), x ∈ t) =
      q9Star F a ∪ q9Star F b := by
    ext t
    simp only [q9Star, mem_union, mem_filter, mem_insert, mem_singleton,
      or_and_right, exists_or, exists_eq_left]
    tauto
  have hi : q9Star F a ∩ q9Star F b = q9Through F {a, b} := by
    ext t
    simp only [q9Star, q9Through, mem_inter, mem_filter, insert_subset_iff,
      singleton_subset_iff]
    tauto
  have ht := q9_trace_sdiff_add_card (p := {a, b}) hF
  have hc := card_union_add_card_inter (q9Star F a) (q9Star F b)
  rw [hu] at ht
  rw [hi] at hc
  omega

/-- Count surviving triples after deleting three points by inclusion-exclusion. -/
theorem q9_trace_sdiff_triple {F : Finset (Finset α)} {S : Finset α}
    (hF : F ⊆ S.powersetCard 3) (a b c : α) :
    (trace F (S \ {a, b, c})).card + (q9Star F a).card + (q9Star F b).card +
      (q9Star F c).card + (q9Through F {a, b, c}).card =
      F.card + (q9Through F {a, b}).card + (q9Through F {a, c}).card +
        (q9Through F {b, c}).card := by
  classical
  let A := q9Star F a
  let B := q9Star F b
  let C := q9Star F c
  have hu : (F.filter fun t => ∃ x ∈ ({a, b, c} : Finset α), x ∈ t) = (A ∪ B) ∪ C := by
    ext t
    simp only [A, B, C, q9Star, mem_union, mem_filter, mem_insert, mem_singleton,
      or_and_right, exists_or, exists_eq_left]
    tauto
  have hp (x y : α) : q9Star F x ∩ q9Star F y = q9Through F {x, y} := by
    ext t
    simp only [q9Star, q9Through, mem_inter, mem_filter, insert_subset_iff,
      singleton_subset_iff]
    tauto
  have hi : (A ∩ C) ∩ (B ∩ C) = q9Through F {a, b, c} := by
    ext t
    simp only [A, B, C, q9Star, q9Through, mem_inter, mem_filter, insert_subset_iff,
      singleton_subset_iff]
    tauto
  have hd : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
    ext t
    simp only [mem_inter, mem_union]
    tauto
  have ht := q9_trace_sdiff_add_card (p := {a, b, c}) hF
  rw [hu] at ht
  have h₁ := card_union_add_card_inter A B
  have h₂ := card_union_add_card_inter (A ∪ B) C
  have h₃ := card_union_add_card_inter (A ∩ C) (B ∩ C)
  rw [hd] at h₂
  rw [hi] at h₃
  have hab : A ∩ B = q9Through F {a, b} := hp a b
  have hac : A ∩ C = q9Through F {a, c} := hp a c
  have hbc : B ∩ C = q9Through F {b, c} := hp b c
  rw [hab] at h₁
  rw [hac, hbc] at h₂ h₃
  change _ + A.card + B.card + C.card + _ = _
  omega

/-- A triple in a uniform family has exactly one extension in that family. -/
theorem q9_through_triple_card {F : Finset (Finset α)} {S t : Finset α}
    (hF : F ⊆ S.powersetCard 3) (ht : t ∈ F) :
    (q9Through F t).card = 1 := by
  have he : q9Through F t = {t} := by
    ext u
    simp only [q9Through, mem_filter, mem_singleton]
    constructor
    · intro ⟨hu, htu⟩
      exact (eq_of_subset_of_card_le htu (by
        rw [(mem_powersetCard.mp (hF hu)).2, (mem_powersetCard.mp (hF ht)).2])).symm
    · rintro rfl
      exact ⟨ht, Subset.rfl⟩
  rw [he, card_singleton]

/-- Each complementary four-set of a Fano line needs two link edges, and
each link edge belongs to exactly two of these four-sets. -/
theorem q9_degree_ge_seven_of_fano_deletion
    {F : Finset (Finset α)} {S : Finset α} {z : α}
    (hS : S.card = 8) (hF : F ⊆ S.powersetCard 3) (hz : z ∈ S)
    (hcover : ∀ U ∈ S.powersetCard 5, 2 ≤ (trace F U).card)
    (htight : (trace F (S.erase z)).card = 7) :
    7 ≤ (q9Star F z).card := by
  classical
  let V := S.erase z
  let L := trace F V
  let K := q9Star F z
  have hV : V.card = 7 := by rw [show V = S.erase z from rfl, card_erase_of_mem hz, hS]
  have hLV : L ⊆ V.powersetCard 3 := trace_uniform hF
  have hpair {a b : α} (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b) :
      (q9Through L {a, b}).card = 1 :=
    seven_point_pair_degree hV hLV htight
      (double_cover_trace hcover (erase_subset z S))
      (insert_subset_iff.mpr ⟨ha, singleton_subset_iff.mpr hb⟩) (card_pair hab)
  have hdeg (a : α) (ha : a ∈ V) : (q9Star L a).card = 3 := by
    have hs := q9_sum_pair_degrees_at hLV a
    have hone (b : α) (hb : b ∈ V.erase a) : (q9Through L {a, b}).card = 1 :=
      hpair ha (mem_erase.mp hb).2 (mem_erase.mp hb).1.symm
    rw [sum_congr rfl hone, sum_const, card_erase_of_mem ha, hV] at hs
    change 6 = (q9Star L a).card * 2 at hs
    omega
  have hfree (l : Finset α) (hl : l ∈ L) : (trace L (V \ l)).card = 0 := by
    obtain ⟨hlV, hlc⟩ := mem_powersetCard.mp (hLV hl)
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hlc
    have ha : a ∈ V := hlV (by simp)
    have hb : b ∈ V := hlV (by simp)
    have hc : c ∈ V := hlV (by simp)
    have hf := q9_trace_sdiff_triple hLV a b c
    rw [hdeg a ha, hdeg b hb, hdeg c hc, q9_through_triple_card hLV hl,
      hpair ha hb hab, hpair ha hc hac, hpair hb hc hbc] at hf
    change L.card = 7 at htight
    omega
  let r := fun (t l : Finset α) => t.erase z ⊆ V \ l
  have htwo (t : Finset α) (ht : t ∈ K) : (L.bipartiteAbove r t).card = 2 := by
    obtain ⟨htF, hzt⟩ := mem_filter.mp ht
    obtain ⟨htS, htc⟩ := mem_powersetCard.mp (hF htF)
    have hpV : t.erase z ⊆ V := by
      intro x hx
      obtain ⟨hxz, hxt⟩ := mem_erase.mp hx
      exact mem_erase.mpr ⟨hxz, htS hxt⟩
    have hpc : (t.erase z).card = 2 := by rw [card_erase_of_mem hzt, htc]
    obtain ⟨a, b, hab, hp⟩ := card_eq_two.mp hpc
    have ha : a ∈ V := hpV (by rw [hp]; simp)
    have hb : b ∈ V := hpV (by rw [hp]; simp)
    have he : L.bipartiteAbove r t = trace L (V \ t.erase z) := by
      ext l
      simp only [mem_bipartiteAbove, trace, mem_filter, r]
      constructor
      · intro ⟨hl, h⟩
        exact ⟨hl, fun x hxl => mem_sdiff.mpr
          ⟨(mem_powersetCard.mp (hLV hl)).1 hxl, fun hxt => (mem_sdiff.mp (h hxt)).2 hxl⟩⟩
      · intro ⟨hl, h⟩
        exact ⟨hl, fun x hxt => mem_sdiff.mpr
          ⟨hpV hxt, fun hxl => (mem_sdiff.mp (h hxl)).2 hxt⟩⟩
    rw [he, hp]
    have h := q9_trace_sdiff_pair hLV a b
    rw [hdeg a ha, hdeg b hb, hpair ha hb hab] at h
    change L.card = 7 at htight
    omega
  have hneed (l : Finset α) (hl : l ∈ L) : 2 ≤ (K.bipartiteBelow r l).card := by
    obtain ⟨hlV, hlc⟩ := mem_powersetCard.mp (hLV hl)
    let U := insert z (V \ l)
    have hzU : z ∉ V \ l := fun h => notMem_erase z S (mem_sdiff.mp h).1
    have hUS : U ⊆ S := insert_subset_iff.mpr
      ⟨hz, sdiff_subset.trans (erase_subset z S)⟩
    have hUc : U.card = 5 := by
      change (insert z (V \ l)).card = 5
      rw [card_insert_of_notMem hzU, card_sdiff_of_subset hlV, hV, hlc]
    have hsub : trace F U ⊆ K.bipartiteBelow r l := by
      intro t ht
      obtain ⟨htF, htU⟩ := mem_filter.mp ht
      have hzt : z ∈ t := by
        by_contra hznot
        have htcomp : t ⊆ V \ l := (subset_insert_iff_of_notMem hznot).mp htU
        have htL : t ∈ L := mem_filter.mpr ⟨htF, htcomp.trans sdiff_subset⟩
        have hmem : t ∈ trace L (V \ l) := mem_filter.mpr ⟨htL, htcomp⟩
        have hpos := card_pos.mpr ⟨t, hmem⟩
        have hzcount := hfree l hl
        omega
      simp only [mem_bipartiteBelow, r]
      exact
        ⟨mem_filter.mpr ⟨htF, hzt⟩, subset_insert_iff.mp htU⟩
    exact (hcover U (mem_powersetCard.mpr ⟨hUS, hUc⟩)).trans (card_le_card hsub)
  have hcount := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := K) (t := L) r
  rw [sum_congr rfl htwo] at hcount
  have hlow := sum_le_sum hneed
  rw [← hcount] at hlow
  change L.card = 7 at htight
  simp only [sum_const, nsmul_eq_mul, Nat.cast_id, htight] at hlow
  change 7 ≤ K.card
  omega

#print axioms q9_degree_ge_seven_of_fano_deletion

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FanoDeletion
