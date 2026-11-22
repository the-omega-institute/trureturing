/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SingletonFiveMask
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SingletonFiveMask
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Overlap of tight Fano incidences forces a singly covered five-axis mask. -/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Powerset
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fintype.Card

/-! Tight seven-point deletions constrain how triples can overlap on eight points. -/

set_option autoImplicit false

public section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SingletonFiveMask

open Finset
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- The members of a family contained in the specified subset. -/
abbrev trace (F : Finset (Finset α)) (U : Finset α) : Finset (Finset α) :=
  F.filter (· ⊆ U)

private theorem trace_trace (F : Finset (Finset α)) {U V : Finset α} (hUV : U ⊆ V) :
    trace (trace F V) U = trace F U := by
  ext t
  simp only [trace, mem_filter]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hUV⟩, h.2⟩⟩

/-- Restricting a triple family to a subset preserves uniformity. -/
theorem trace_uniform {F : Finset (Finset α)} {S U : Finset α}
    (hF : F ⊆ S.powersetCard 3) :
    trace F U ⊆ U.powersetCard 3 := by
  intro t ht
  obtain ⟨htF, htU⟩ := mem_filter.mp ht
  exact mem_powersetCard.mpr ⟨htU, (mem_powersetCard.mp (hF htF)).2⟩

/-- Double coverage persists when the ground set is restricted. -/
theorem double_cover_trace {F : Finset (Finset α)} {S U : Finset α}
    (hcover : ∀ V ∈ S.powersetCard 5, 2 ≤ (trace F V).card) (hUS : U ⊆ S) :
    ∀ V ∈ U.powersetCard 5, 2 ≤ (trace (trace F U) V).card := by
  intro V hV
  obtain ⟨hVU, hVc⟩ := mem_powersetCard.mp hV
  rw [trace_trace F hVU]
  exact hcover V (mem_powersetCard.mpr ⟨hVU.trans hUS, hVc⟩)

/-- Count incidences between triples and their containing subsets of size `k`. -/
theorem trace_card_sum {S : Finset α} {F : Finset (Finset α)} {k : ℕ}
    (hF : F ⊆ S.powersetCard 3) (hk : 3 ≤ k) :
    (∑ U ∈ S.powersetCard k, (trace F U).card) =
      F.card * (S.card - 3).choose (k - 3) := by
  calc
    _ = ∑ t ∈ F, ((S.powersetCard k).filter (t ⊆ ·)).card := by
      simpa only [trace, bipartiteAbove, bipartiteBelow] using
        (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (s := F) (t := S.powersetCard k) (fun (t U : Finset α) => t ⊆ U)).symm
    _ = ∑ _t ∈ F, (S.card - 3).choose (k - 3) := by
      apply sum_congr rfl
      intro t ht
      obtain ⟨htS, htc⟩ := mem_powersetCard.mp (hF ht)
      have htk : t.card ≤ k := by simpa only [htc] using hk
      rw [card_filter_powersetCard_subset t S k htS htk, htc]
    _ = _ := by simp

/-- The total triple incidence count bounds a double five-set cover. -/
theorem double_cover_bound {S : Finset α} {F : Finset (Finset α)}
    (hF : F ⊆ S.powersetCard 3)
    (hcover : ∀ U ∈ S.powersetCard 5, 2 ≤ (trace F U).card) :
    S.card.choose 5 * 2 ≤ F.card * (S.card - 3).choose 2 := by
  calc
    _ = ∑ _U ∈ S.powersetCard 5, 2 := by simp [card_powersetCard]
    _ ≤ ∑ U ∈ S.powersetCard 5, (trace F U).card := sum_le_sum hcover
    _ = _ := trace_card_sum hF (by decide)

private theorem trace_erase_card_sum {S : Finset α} {F : Finset (Finset α)}
    (hF : F ⊆ S.powersetCard 3) :
    (∑ x ∈ S, (trace F (S.erase x)).card) = F.card * (S.card - 3) := by
  let r := fun (t : Finset α) (x : α) => x ∉ t
  have habove (t : Finset α) : S.bipartiteAbove r t = S \ t := by
    ext x
    simp [r]
  have hbelow (x : α) : F.bipartiteBelow r x = trace F (S.erase x) := by
    ext t
    simp only [mem_bipartiteBelow, trace, mem_filter, subset_erase, r]
    exact ⟨fun h => ⟨h.1, (mem_powersetCard.mp (hF h.1)).1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  calc
    _ = ∑ t ∈ F, (S \ t).card := by
      simpa only [habove, hbelow] using
        (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := F) (t := S) r).symm
    _ = ∑ _t ∈ F, (S.card - 3) := by
      apply sum_congr rfl
      intro t ht
      obtain ⟨htS, htc⟩ := mem_powersetCard.mp (hF ht)
      rw [card_sdiff_of_subset htS, htc]
    _ = _ := by simp

/-- Deleting a point partitions the family into its trace and the triples through the point. -/
theorem erase_trace_add_degree {S : Finset α} {F : Finset (Finset α)}
    (hFS : ∀ t ∈ F, t ⊆ S) (x : α) :
    (trace F (S.erase x)).card + (F.filter (x ∈ ·)).card = F.card := by
  have he : trace F (S.erase x) = F.filter (x ∉ ·) := by
    ext t
    simp only [trace, mem_filter, subset_erase]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hFS t h.1, h.2⟩⟩
  rw [he, Nat.add_comm]
  exact card_filter_add_card_filter_not (x ∈ ·)

/-- Each pair lies in exactly one triple of a tight seven-point double cover. -/
theorem seven_point_pair_degree {S p : Finset α} {F : Finset (Finset α)}
    (hS : S.card = 7) (hF : F ⊆ S.powersetCard 3) (hFc : F.card = 7)
    (hcover : ∀ U ∈ S.powersetCard 5, 2 ≤ (trace F U).card)
    (hpS : p ⊆ S) (hp : p.card = 2) : (F.filter (p ⊆ ·)).card = 1 := by
  have hsum := trace_card_sum hF (k := 5) (by decide)
  rw [hS, hFc] at hsum
  change (∑ U ∈ S.powersetCard 5, (trace F U).card) = 42 at hsum
  have hexact (U : Finset α) (hU : U ∈ S.powersetCard 5) :
      (trace F U).card = 2 := by
    by_contra hne
    have hlt : (∑ _V ∈ S.powersetCard 5, 2) <
        ∑ V ∈ S.powersetCard 5, (trace F V).card :=
      sum_lt_sum hcover ⟨U, hU, by have := hcover U hU; omega⟩
    rw [hsum] at hlt
    simp [card_powersetCard, hS, show Nat.choose 7 5 = 21 by decide] at hlt
  have hfour (x : α) (hx : x ∈ S) : (trace F (S.erase x)).card = 4 := by
    have hsize : (S.erase x).card = 6 := by rw [card_erase_of_mem hx, hS]
    have hlocal := trace_card_sum (trace_uniform (U := S.erase x) hF) (k := 5) (by decide)
    rw [hsize] at hlocal
    change (∑ U ∈ (S.erase x).powersetCard 5, (trace (trace F (S.erase x)) U).card) =
      (trace F (S.erase x)).card * 3 at hlocal
    have hlocalExact (U : Finset α) (hU : U ∈ (S.erase x).powersetCard 5) :
        (trace (trace F (S.erase x)) U).card = 2 := by
      obtain ⟨hUsub, hUc⟩ := mem_powersetCard.mp hU
      rw [trace_trace F hUsub]
      exact hexact U (mem_powersetCard.mpr ⟨hUsub.trans (erase_subset _ _), hUc⟩)
    rw [sum_congr rfl hlocalExact, sum_const, card_powersetCard, hsize] at hlocal
    change 12 = (trace F (S.erase x)).card * 3 at hlocal
    omega
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hp
  have hx : x ∈ S := hpS (by simp)
  have hy : y ∈ S := hpS (by simp)
  let A := trace F (S.erase x)
  let B := trace F (S.erase y)
  have hinter : A ∩ B = trace F ((S.erase x).erase y) := by
    ext t
    simp only [A, B, trace, mem_inter, mem_filter, subset_erase]
    tauto
  have hunion : A ∪ B = F.filter (fun t => ¬ ({x, y} : Finset α) ⊆ t) := by
    ext t
    simp only [A, B, trace, mem_union, mem_filter, subset_erase, insert_subset_iff,
      singleton_subset_iff]
    have hsub (ht : t ∈ F) := (mem_powersetCard.mp (hF ht)).1
    tauto
  have hyx : y ∈ S.erase x := mem_erase.mpr ⟨hxy.symm, hy⟩
  have hU : (S.erase x).erase y ∈ S.powersetCard 5 := by
    refine mem_powersetCard.mpr ⟨(erase_subset _ _).trans (erase_subset _ _), ?_⟩
    rw [card_erase_of_mem hyx, card_erase_of_mem hx, hS]
  have hsumAB := card_union_add_card_inter A B
  have hA : A.card = 4 := hfour x hx
  have hB : B.card = 4 := hfour y hy
  rw [hinter, hunion, hexact _ hU, hA, hB] at hsumAB
  have hpartition := card_filter_add_card_filter_not (s := F) (({x, y} : Finset α) ⊆ ·)
  omega

/-- A pair avoided by at least three tight deletions has no extension through
a vertex of any of those deletions. -/
private theorem no_extension_through_tight_deletions
    {S H p : Finset α} {F : Finset (Finset α)}
    (hF : F ⊆ S.powersetCard 3) (hp : p.card = 2)
    (hpair : ∀ x ∈ H \ p, ((trace F (S.erase x)).filter (p ⊆ ·)).card = 1)
    (hmany : 3 ≤ (H \ p).card) :
    ∀ x ∈ H \ p, insert x p ∉ F := by
  let E := F.filter (p ⊆ ·)
  have hsplit (x : α) (hx : x ∈ H \ p) :
      1 + (E.filter (x ∈ ·)).card = E.card := by
    have he : trace E (S.erase x) = (trace F (S.erase x)).filter (p ⊆ ·) := by
      ext t
      simp only [E, trace, mem_filter]
      tauto
    have h := erase_trace_add_degree (F := E) (S := S)
      (fun t ht => (mem_powersetCard.mp (hF (mem_filter.mp ht).1)).1) x
    rwa [he, hpair x hx] at h
  have hfiber (x : α) (hx : x ∈ H \ p) :
      E.filter (x ∈ ·) ⊆ {insert x p} := by
    intro t ht
    obtain ⟨htE, hxt⟩ := mem_filter.mp ht
    obtain ⟨htF, hpt⟩ := mem_filter.mp htE
    apply mem_singleton.mpr
    symm
    apply eq_of_subset_of_card_le (insert_subset_iff.mpr ⟨hxt, hpt⟩)
    rw [(mem_powersetCard.mp (hF htF)).2, card_insert_of_notMem (mem_sdiff.mp hx).2, hp]
  intro x hx hxF
  have hxE : insert x p ∈ E.filter (x ∈ ·) :=
    mem_filter.mpr ⟨mem_filter.mpr ⟨hxF, subset_insert _ _⟩, mem_insert_self _ _⟩
  have hpos := card_pos.mpr ⟨insert x p, hxE⟩
  have hmax := card_le_card (hfiber x hx)
  rw [card_singleton] at hmax
  have hE : E.card = 2 := by have := hsplit x hx; omega
  have hmap : (H \ p).card ≤ E.card := by
    apply card_le_card_of_injOn (fun y => insert y p)
    · intro y hy
      change y ∈ H \ p at hy
      have hcard : (E.filter (y ∈ ·)).card = 1 := by have := hsplit y hy; omega
      obtain ⟨t, ht⟩ := card_pos.mp (by omega : 0 < (E.filter (y ∈ ·)).card)
      have htEq := mem_singleton.mp (hfiber y hy ht)
      change insert y p ∈ E
      rw [← htEq]
      exact (mem_filter.mp ht).1
    · intro y hy z _hz he
      change insert y p = insert z p at he
      have hmem : y ∈ insert z p := he ▸ mem_insert_self y p
      exact (mem_insert.mp hmem).resolve_right (mem_sdiff.mp (show y ∈ H \ p from hy)).2
  omega

/-- On eight points, double coverage of every five-set requires at least
thirteen distinct triples. -/
theorem thirteen_le_card_of_double_five_cover {S : Finset α} {F : Finset (Finset α)}
    (hS : S.card = 8) (hF : F ⊆ S.powersetCard 3)
    (hcover : ∀ U ∈ S.powersetCard 5, 2 ≤ (F.filter (· ⊆ U)).card) :
    13 ≤ F.card := by
  by_contra hsmall
  have hbound := double_cover_bound hF hcover
  rw [hS] at hbound
  change 112 ≤ F.card * 10 at hbound
  have hFc : F.card = 12 := by omega
  have herase (x : α) (hx : x ∈ S) : (S.erase x).card = 7 := by
    rw [card_erase_of_mem hx, hS]
  have hseven (x : α) (hx : x ∈ S) : 7 ≤ (trace F (S.erase x)).card := by
    have h := double_cover_bound (trace_uniform (U := S.erase x) hF)
      (double_cover_trace hcover (erase_subset x S))
    rw [herase x hx] at h
    change 42 ≤ (trace F (S.erase x)).card * 6 at h
    omega
  let tight := S.filter (fun x => (trace F (S.erase x)).card = 7)
  have htight : 4 ≤ tight.card := by
    have hsum := trace_erase_card_sum hF
    rw [hS, hFc] at hsum
    change (∑ x ∈ S, (trace F (S.erase x)).card) = 60 at hsum
    have hrest (x : α) (hx : x ∈ S.filter (fun x => ¬ (trace F (S.erase x)).card = 7)) :
        8 ≤ (trace F (S.erase x)).card := by
      have ⟨hxS, hx7⟩ := mem_filter.mp hx
      have := hseven x hxS
      omega
    have hsplit := sum_filter_add_sum_filter_not S
      (fun x => (trace F (S.erase x)).card = 7) (fun x => (trace F (S.erase x)).card)
    have hcards := card_filter_add_card_filter_not (s := S)
      (fun x => (trace F (S.erase x)).card = 7)
    have ht : (∑ x ∈ tight, (trace F (S.erase x)).card) = tight.card * 7 := by
      calc
        _ = ∑ _x ∈ tight, 7 := sum_congr rfl (fun _ hx => (mem_filter.mp hx).2)
        _ = _ := by simp
    have hlower := sum_le_sum hrest
    simp only [sum_const, nsmul_eq_mul, Nat.cast_id] at hlower
    change (∑ x ∈ tight, (trace F (S.erase x)).card) +
      (∑ x ∈ S.filter (fun x => ¬ (trace F (S.erase x)).card = 7),
        (trace F (S.erase x)).card) = _ at hsplit
    change tight.card + _ = S.card at hcards
    rw [ht, hsum] at hsplit
    rw [hS] at hcards
    omega
  obtain ⟨H, hH, hHc⟩ := exists_subset_card_eq htight
  have hHS : H ⊆ S := hH.trans (filter_subset _ _)
  have htrap {x : α} (hx : x ∈ H) {t : Finset α} (ht : t ∈ F) (hxt : x ∈ t) :
      t ⊆ H := by
    intro y hyt
    by_contra hy
    let p := t.erase x
    have hty := mem_powersetCard.mp (hF ht)
    have hp : p.card = 2 := by rw [card_erase_of_mem hxt, hty.2]
    have hxp : x ∉ p := notMem_erase _ _
    have hyp : y ∈ p := mem_erase.mpr ⟨fun h => hy (h.symm ▸ hx), hyt⟩
    have hinter : H ∩ p ⊆ p.erase y := by
      intro z hz
      obtain ⟨hzH, hzp⟩ := mem_inter.mp hz
      exact mem_erase.mpr ⟨fun h => hy (h ▸ hzH), hzp⟩
    have hcap := card_le_card hinter
    rw [card_erase_of_mem hyp, hp] at hcap
    have hdiff := card_sdiff_add_card_inter H p
    have hmany : 3 ≤ (H \ p).card := by omega
    have hpair (z : α) (hz : z ∈ H \ p) :
        ((trace F (S.erase z)).filter (p ⊆ ·)).card = 1 := by
      obtain ⟨hzH, hzp⟩ := mem_sdiff.mp hz
      have hzS := hHS hzH
      exact seven_point_pair_degree (herase z hzS) (trace_uniform hF)
        (mem_filter.mp (hH hzH)).2 (double_cover_trace hcover (erase_subset _ _))
        (subset_erase.mpr ⟨(erase_subset _ _).trans hty.1, hzp⟩) hp
    apply no_extension_through_tight_deletions hF hp hpair hmany x (mem_sdiff.mpr ⟨hx, hxp⟩)
    rwa [insert_erase hxt]
  obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < H.card)
  have hpartition := erase_trace_add_degree
    (fun t ht => (mem_powersetCard.mp (hF ht)).1) x
  have hxT : (trace F (S.erase x)).card = 7 := (mem_filter.mp (hH hx)).2
  have hdegree : (F.filter (x ∈ ·)).card = 5 := by omega
  have hsub : F.filter (x ∈ ·) ⊆ (H.powersetCard 3).filter (({x} : Finset α) ⊆ ·) := by
    intro t ht
    obtain ⟨htF, hxt⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨mem_powersetCard.mpr
      ⟨htrap hx htF hxt, (mem_powersetCard.mp (hF htF)).2⟩, singleton_subset_iff.mpr hxt⟩
  have hcap := card_le_card hsub
  rw [card_filter_powersetCard_subset {x} H 3 (singleton_subset_iff.mpr hx) (by simp),
    card_singleton, hHc, hdegree] at hcap
  exact (by decide : ¬ (5 ≤ (4 - 1).choose (3 - 1))) hcap

/-- If every five-axis mask contains a triple from a family of at most
nineteen triples on nine axes, some mask contains exactly one family member. -/
theorem exists_singleton_five_mask (F : Finset (Finset (Fin 9)))
    (hF : ∀ t ∈ F, t.card = 3) (hFc : F.card ≤ 19)
    (hcover : ∀ U : Finset (Fin 9), U.card = 5 → 1 ≤ (F.filter (· ⊆ U)).card) :
    ∃ U : Finset (Fin 9), U.card = 5 ∧ (F.filter (· ⊆ U)).card = 1 := by
  let S : Finset (Fin 9) := univ
  have hS : S.card = 9 := by simp [S]
  have hFS : F ⊆ S.powersetCard 3 := by
    intro t ht
    exact mem_powersetCard.mpr ⟨subset_univ _, hF t ht⟩
  by_contra hnone
  have hdouble (U : Finset (Fin 9)) (hU : U ∈ S.powersetCard 5) :
      2 ≤ (trace F U).card := by
    have hUc := (mem_powersetCard.mp hU).2
    have hne : (trace F U).card ≠ 1 := fun he => hnone ⟨U, hUc, he⟩
    exact Nat.succ_le_of_lt (lt_of_le_of_ne (hcover U hUc) hne.symm)
  have hlarge (V : Finset (Fin 9)) (hV : V ∈ S.powersetCard 8) :
      13 ≤ (trace F V).card := by
    obtain ⟨hVS, hVc⟩ := mem_powersetCard.mp hV
    exact thirteen_le_card_of_double_five_cover hVc (trace_uniform hFS)
      (double_cover_trace hdouble hVS)
  have hlower := sum_le_sum hlarge
  simp only [sum_const, nsmul_eq_mul, Nat.cast_id, card_powersetCard, hS] at hlower
  have hsum := trace_card_sum hFS (k := 8) (by decide)
  rw [hS] at hsum
  change (∑ U ∈ S.powersetCard 8, (trace F U).card) = F.card * 6 at hsum
  rw [hsum] at hlower
  change 117 ≤ F.card * 6 at hlower
  omega

#print axioms thirteen_le_card_of_double_five_cover
#print axioms exists_singleton_five_mask

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SingletonFiveMask
