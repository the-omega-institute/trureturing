/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronEleven
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronEleven
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: A capped tetrahedral support without a singleton triangle coface has no order eleven. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SparseCocycleSupport
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TetrahedronLinkBound
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Order.Interval.Finset.Nat

/-! The eleven-facet gap in the support of a capped tetrahedral cycle. -/

set_option autoImplicit false

namespace Q9SevenVertexCocycle

open Finset

private abbrev Face := Finset (Fin 6)
private abbrev OptionFace := Finset (Option (Fin 6))
private abbrev Family := Finset OptionFace

private abbrev pivotEmbedding : Face ↪ OptionFace :=
  (Finset.insertNone : Face ↪o OptionFace).toEmbedding

private abbrev outsideEmbedding : Face ↪ OptionFace :=
  (Finset.mapEmbedding Function.Embedding.some).toEmbedding

private def pivotEdges (C : Family) : Finset Face :=
  (C.filter fun s => none ∈ s).image fun s => s.eraseNone

private def outsideFaces (C : Family) : Finset Face :=
  (C.filter fun s => none ∉ s).image fun s => s.eraseNone

private theorem restorePivot {s : OptionFace} (hs : none ∈ s) :
    insertNone s.eraseNone = s :=
  (insertNone_eraseNone s).trans (insert_eq_of_mem hs)

private theorem restoreOutside {s : OptionFace} (hs : none ∉ s) :
    s.eraseNone.map Function.Embedding.some = s :=
  (map_some_eraseNone s).trans (erase_eq_of_notMem hs)

private theorem none_notMem_map_some (t : Face) :
    none ∉ t.map Function.Embedding.some := by
  intro h
  obtain ⟨v, _, hv⟩ := mem_map.mp h
  exact Option.some_ne_none v (show some v = none from hv)

private theorem mem_pivotEdges {C : Family} {e : Face} :
    e ∈ pivotEdges C ↔ insertNone e ∈ C := by
  unfold pivotEdges
  constructor
  · intro he
    obtain ⟨s, hs, rfl⟩ := mem_image.mp he
    obtain ⟨hsC, hsPivot⟩ := mem_filter.mp hs
    rw [restorePivot hsPivot]
    exact hsC
  · intro he
    exact mem_image.mpr
      ⟨insertNone e, mem_filter.mpr ⟨he, none_mem_insertNone⟩, eraseNone_insertNone e⟩

private theorem mem_outsideFaces {C : Family} {t : Face} :
    t ∈ outsideFaces C ↔ t.map Function.Embedding.some ∈ C := by
  unfold outsideFaces
  constructor
  · intro ht
    obtain ⟨s, hs, rfl⟩ := mem_image.mp ht
    obtain ⟨hsC, hsOutside⟩ := mem_filter.mp hs
    rw [restoreOutside hsOutside]
    exact hsC
  · intro ht
    exact mem_image.mpr
      ⟨t.map Function.Embedding.some, mem_filter.mpr ⟨ht, none_notMem_map_some t⟩,
        eraseNone_map_some t⟩

private theorem card_pivotEdges (C : Family) :
    (pivotEdges C).card = (C.filter fun s => none ∈ s).card := by
  unfold pivotEdges
  apply card_image_of_injOn
  intro s hs u hu h
  have hsPivot := (mem_filter.mp (mem_coe.mp hs)).2
  have huPivot := (mem_filter.mp (mem_coe.mp hu)).2
  calc
    s = insertNone s.eraseNone := (restorePivot hsPivot).symm
    _ = insertNone u.eraseNone := congrArg (fun e : Face => insertNone e) h
    _ = u := restorePivot huPivot

private theorem card_outsideFaces (C : Family) :
    (outsideFaces C).card = (C.filter fun s => none ∉ s).card := by
  unfold outsideFaces
  apply card_image_of_injOn
  intro s hs u hu h
  have hsOutside := (mem_filter.mp (mem_coe.mp hs)).2
  have huOutside := (mem_filter.mp (mem_coe.mp hu)).2
  calc
    s = s.eraseNone.map Function.Embedding.some := (restoreOutside hsOutside).symm
    _ = u.eraseNone.map Function.Embedding.some :=
      congrArg (fun t : Face => t.map Function.Embedding.some) h
    _ = u := restoreOutside huOutside

private theorem eraseNone_subset_of_subset_insertNone {s : OptionFace} {t : Face}
    (h : s ⊆ insertNone t) : s.eraseNone ⊆ t :=
  fun _ hv => some_mem_insertNone.mp (h (mem_eraseNone.mp hv))

private theorem map_some_subset_insertNone (t : Face) :
    t.map Function.Embedding.some ⊆ insertNone t := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := mem_map.mp hv
  exact some_mem_insertNone.mpr hu

private theorem card_triples_in_pivot_four (C : Family)
    (htriple : ∀ s ∈ C, s.card = 3) (t : Face) (ht : t.card = 3) :
    (C.filter (· ⊆ insertNone t)).card =
      ((pivotEdges C).filter (· ⊆ t)).card + (if t ∈ outsideFaces C then 1 else 0) := by
  let P := ((pivotEdges C).filter (· ⊆ t)).map pivotEmbedding
  let N : Family := {t.map Function.Embedding.some}
  have hsplit : C.filter (· ⊆ insertNone t) = P ∪ N.filter (· ∈ C) := by
    ext s
    constructor
    · intro hs
      obtain ⟨hsC, hst⟩ := mem_filter.mp hs
      have herase := eraseNone_subset_of_subset_insertNone hst
      by_cases hsPivot : none ∈ s
      · have he : s.eraseNone ∈ pivotEdges C := mem_pivotEdges.mpr (by
          rw [restorePivot hsPivot]
          exact hsC)
        exact mem_union.mpr (Or.inl
          (mem_map.mpr ⟨s.eraseNone, mem_filter.mpr ⟨he, herase⟩, restorePivot hsPivot⟩))
      · have hcard : s.eraseNone.card = t.card :=
          (card_eraseNone_of_notMem hsPivot).trans ((htriple s hsC).trans ht.symm)
        have heq := eq_of_subset_of_card_le herase hcard.ge
        have hsEq : s = t.map Function.Embedding.some := by
          rw [← heq, restoreOutside hsPivot]
        exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_singleton.mpr hsEq, hsC⟩))
    · intro hs
      rcases mem_union.mp hs with hsP | hsN
      · obtain ⟨e, he, rfl⟩ := mem_map.mp hsP
        obtain ⟨heE, het⟩ := mem_filter.mp he
        exact mem_filter.mpr ⟨mem_pivotEdges.mp heE, Finset.insertNone.monotone het⟩
      · obtain ⟨hsN, hsC⟩ := mem_filter.mp hsN
        have hsEq : s = t.map Function.Embedding.some := mem_singleton.mp hsN
        subst s
        exact mem_filter.mpr ⟨hsC, map_some_subset_insertNone t⟩
  have hdisjoint : Disjoint P (N.filter (· ∈ C)) := by
    apply disjoint_left.mpr
    intro s hsP hsN
    obtain ⟨e, _, rfl⟩ := mem_map.mp hsP
    have heq : insertNone e = t.map Function.Embedding.some :=
      mem_singleton.mp (mem_filter.mp hsN).1
    exact none_notMem_map_some t (heq ▸ none_mem_insertNone)
  have hN : (N.filter (· ∈ C)).card = if t ∈ outsideFaces C then 1 else 0 := by
    by_cases htB : t ∈ outsideFaces C
    · have htC := mem_outsideFaces.mp htB
      simp [N, filter_singleton, htB, htC]
    · have htC : t.map Function.Embedding.some ∉ C := fun h => htB (mem_outsideFaces.mpr h)
      simp [N, filter_singleton, htB, htC]
  rw [hsplit, card_union_of_disjoint hdisjoint, hN]
  simp only [P, card_map]

/-- A capped family of triples with the four-set singleton exclusion and a
nonempty pivot link of size at most four has size nine or twelve. In the
twelve-triple case the pivot triples use the four cycle edges, and the other
triples extend those same edges by the two vertices off the cycle. -/
theorem card_eq_nine_or_twelve_with_pivot (C : Finset (Finset (Option (Fin 6))))
    (htriple : ∀ s ∈ C, s.card = 3)
    (hfour : ∀ s : Finset (Option (Fin 6)), s.card = 4 → (C.filter (· ⊆ s)).card ≠ 1)
    (hpair : ∀ p : Finset (Option (Fin 6)), p.card = 2 → (C.filter (p ⊆ ·)).card ≤ 3)
    (hmin : 1 ≤ (C.filter fun s => none ∈ s).card)
    (hmax : (C.filter fun s => none ∈ s).card ≤ 4) :
    C.card = 9 ∨
      (C.card = 12 ∧ ∃ a b c d : Fin 6, ({a, b, c, d} : Finset (Fin 6)).card = 4 ∧
        let cycle : Finset (Finset (Fin 6)) := {{a, b}, {b, c}, {c, d}, {d, a}}
        (∀ e : Finset (Fin 6), insertNone e ∈ C ↔ e ∈ cycle) ∧
        (∀ t : Finset (Fin 6), t.map Function.Embedding.some ∈ C ↔
          ∃ e ∈ cycle, ∃ v ∉ ({a, b, c, d} : Finset (Fin 6)), t = insert v e)) := by
  let E := pivotEdges C
  let B := outsideFaces C
  have hedge (e : Face) (he : e ∈ E) : e.card = 2 := by
    change e ∈ (C.filter fun s => none ∈ s).image (fun s => s.eraseNone) at he
    obtain ⟨s, hs, rfl⟩ := mem_image.mp he
    obtain ⟨hsC, hsPivot⟩ := mem_filter.mp hs
    rw [card_eraseNone_of_mem hsPivot, htriple s hsC]
  have hdegree (v : Fin 6) : (E.filter (v ∈ ·)).card ≤ 3 := by
    let p : OptionFace := insertNone ({v} : Face)
    have hp : p.card = 2 := by simp [p]
    have hsub : (E.filter (v ∈ ·)).map pivotEmbedding ⊆ C.filter (p ⊆ ·) := by
      intro s hs
      obtain ⟨e, he, rfl⟩ := mem_map.mp hs
      obtain ⟨heE, hve⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨mem_pivotEdges.mp heE,
        Finset.insertNone.monotone (singleton_subset_iff.mpr hve)⟩
    simpa only [card_map] using (card_le_card hsub).trans (hpair p hp)
  have hcap (e : Face) (he : e ∈ E) : (B.filter (e ⊆ ·)).card ≤ 2 := by
    let p := e.map Function.Embedding.some
    let F := (B.filter (e ⊆ ·)).map outsideEmbedding
    have hp : p.card = 2 := by simpa only [p, card_map] using hedge e he
    have hnot : insertNone e ∉ F := by
      intro h
      obtain ⟨t, _, ht⟩ := mem_map.mp h
      have ht' : t.map Function.Embedding.some = insertNone e := ht
      exact none_notMem_map_some t (ht'.symm ▸ none_mem_insertNone)
    have hsub : insert (insertNone e) F ⊆ C.filter (p ⊆ ·) := by
      apply insert_subset_iff.mpr
      refine ⟨mem_filter.mpr ⟨mem_pivotEdges.mp he, map_some_subset_insertNone e⟩, ?_⟩
      intro s hs
      obtain ⟨t, ht, rfl⟩ := mem_map.mp hs
      obtain ⟨htB, het⟩ := mem_filter.mp ht
      exact mem_filter.mpr ⟨mem_outsideFaces.mp htB, map_subset_map.mpr het⟩
    have hbound := (card_le_card hsub).trans (hpair p hp)
    rw [card_insert_of_notMem hnot] at hbound
    have hbound' : (B.filter (e ⊆ ·)).card + 1 ≤ 3 := by
      simpa only [F, card_map] using hbound
    exact Nat.le_of_succ_le_succ hbound'
  have hcount (t : Face) (ht : t.card = 3) :
      (E.filter (· ⊆ t)).card + (if t ∈ B then 1 else 0) ≠ 1 := by
    have ht4 : (insertNone t).card = 4 := by rw [card_insertNone, ht]
    have h := hfour _ ht4
    rw [card_triples_in_pivot_four C htriple t ht] at h
    exact h
  have hforced : Q9SparseCocycleSupport.singleEdgeTriples E ⊆ B := by
    intro t ht
    change t ∈ ((univ : Face).powersetCard 3).filter
      (fun r => (E.filter (· ⊆ r)).card = 1) at ht
    obtain ⟨ht3, hone⟩ := mem_filter.mp ht
    by_cases htB : t ∈ B
    · exact htB
    · exact (hcount t (mem_powersetCard.mp ht3).2
        (by rw [hone, if_neg htB, Nat.add_zero])).elim
  have hsupported (t : Face) (ht : t ∈ B) : ∃ e ∈ E, e ⊆ t := by
    have ht3 : t.card = 3 := by
      have h := htriple _ (mem_outsideFaces.mp ht)
      rwa [card_map] at h
    by_cases hempty : E.filter (· ⊆ t) = ∅
    · exact (hcount t ht3 (by rw [hempty, card_empty, if_pos ht, Nat.zero_add])).elim
    · obtain ⟨e, he⟩ := nonempty_iff_ne_empty.mpr hempty
      exact ⟨e, (mem_filter.mp he).1, (mem_filter.mp he).2⟩
  have hECard : E.card = (C.filter fun s => none ∈ s).card := card_pivotEdges C
  have hBCard : B.card = (C.filter fun s => none ∉ s).card := card_outsideFaces C
  have hsum : E.card + B.card = C.card := by
    rw [hECard, hBCard]
    exact card_filter_add_card_filter_not (fun s => none ∈ s)
  obtain ⟨_, hcases⟩ := Q9SparseCocycleSupport.sparse_cocycle_support_classification E B hedge
    (hECard.symm ▸ hmin) (hECard.symm ▸ hmax) hdegree hforced hsupported hcap
  rcases hcases with ⟨hE, _, hB⟩ | ⟨hE, hB, a, b, c, d, hvertices, hcycle, houtside⟩
  · exact Or.inl (by rw [← hsum, hE, hB])
  · refine Or.inr ⟨by rw [← hsum, hE, hB], a, b, c, d, hvertices, ?_, ?_⟩
    · intro e
      have he : e ∈ E ↔ insertNone e ∈ C := mem_pivotEdges
      rw [hcycle] at he
      exact he.symm
    · intro t
      have ht : t ∈ B ↔ t.map Function.Embedding.some ∈ C := mem_outsideFaces
      have h := ht.symm.trans (houtside t)
      rw [hcycle] at h
      exact h

/-- A capped family of triples with the four-set singleton exclusion and a
nonempty pivot link of size at most four has size nine or twelve. -/
theorem card_eq_nine_or_twelve (C : Finset (Finset (Option (Fin 6))))
    (htriple : ∀ s ∈ C, s.card = 3)
    (hfour : ∀ s : Finset (Option (Fin 6)), s.card = 4 → (C.filter (· ⊆ s)).card ≠ 1)
    (hpair : ∀ p : Finset (Option (Fin 6)), p.card = 2 → (C.filter (p ⊆ ·)).card ≤ 3)
    (hmin : 1 ≤ (C.filter fun s => none ∈ s).card)
    (hmax : (C.filter fun s => none ∈ s).card ≤ 4) :
    C.card = 9 ∨ C.card = 12 := by
  rcases card_eq_nine_or_twelve_with_pivot C htriple hfour hpair hmin hmax with h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

private theorem card_complement_filter (T : Family) (p : OptionFace → Prop) [DecidablePred p] :
    ((T.image fun s => sᶜ).filter p).card = (T.filter fun s => p sᶜ).card := by
  have h : (T.image fun s => sᶜ).filter p = (T.filter fun s => p sᶜ).image (·ᶜ) := by
    ext s
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hp⟩
      exact ⟨t, ⟨ht, hp⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hp⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, hp⟩
  rw [h, card_image_of_injective _ compl_injective]

/-- Taking complements turns the triangle coface condition and five-set cap
for tetrahedra into the four-set singleton exclusion and pair cap for triples. -/
theorem tetrahedra_card_eq_nine_or_twelve (T : Finset (Finset (Option (Fin 6))))
    (htetra : ∀ s ∈ T, s.card = 4)
    (hthree : ∀ s : Finset (Option (Fin 6)), s.card = 3 → (T.filter (s ⊆ ·)).card ≠ 1)
    (hfive : ∀ s : Finset (Option (Fin 6)), s.card = 5 → (T.filter (· ⊆ s)).card ≤ 3)
    (hmin : 1 ≤ (T.filter fun s => none ∉ s).card)
    (hmax : (T.filter fun s => none ∉ s).card ≤ 4) :
    T.card = 9 ∨ T.card = 12 := by
  let C := T.image (fun s => sᶜ)
  have hseven : Fintype.card (Option (Fin 6)) = 7 := by
    rw [Fintype.card_option, Fintype.card_fin]
  have htriple (s : OptionFace) (hs : s ∈ C) : s.card = 3 := by
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
    rw [card_compl, hseven, htetra t ht]
  have hfour (s : OptionFace) (hs : s.card = 4) : (C.filter (· ⊆ s)).card ≠ 1 := by
    have hcard : sᶜ.card = 3 := by rw [card_compl, hseven, hs]
    have hdual (t : OptionFace) : tᶜ ⊆ s ↔ sᶜ ⊆ t := by
      simpa only [compl_compl] using (compl_subset_compl (s := t) (t := sᶜ))
    have hfilter : (T.filter fun t => tᶜ ⊆ s) = T.filter (sᶜ ⊆ ·) :=
      filter_congr (fun t _ => hdual t)
    change ((T.image fun t => tᶜ).filter (· ⊆ s)).card ≠ 1
    rw [card_complement_filter, hfilter]
    exact hthree sᶜ hcard
  have hpair (p : OptionFace) (hp : p.card = 2) : (C.filter (p ⊆ ·)).card ≤ 3 := by
    have hcard : pᶜ.card = 5 := by rw [card_compl, hseven, hp]
    have hfilter : (T.filter fun t => p ⊆ tᶜ) = T.filter (· ⊆ pᶜ) :=
      filter_congr (fun _ _ => subset_compl_comm)
    change ((T.image fun t => tᶜ).filter (p ⊆ ·)).card ≤ 3
    rw [card_complement_filter, hfilter]
    exact hfive pᶜ hcard
  have hpivot : (C.filter fun s => none ∈ s).card = (T.filter fun s => none ∉ s).card := by
    have hfilter : (T.filter fun s => none ∈ sᶜ) = T.filter (none ∉ ·) :=
      filter_congr (fun _ _ => mem_compl)
    change ((T.image fun s => sᶜ).filter fun s => none ∈ s).card = _
    rw [card_complement_filter, hfilter]
  have hC : C.card = T.card := card_image_of_injective T compl_injective
  rw [← hC]
  exact card_eq_nine_or_twelve C htriple hfour hpair
    (hpivot.symm ▸ hmin) (hpivot.symm ▸ hmax)

/-- Eleven tetrahedra on seven vertices cannot satisfy both the
three-face incidence condition and the five-set cap. Counting incidences
gives a pivot, which is moved to `none` by a vertex permutation. -/
theorem tetrahedra_card_ne_eleven_on_seven_vertices (T : Finset (Finset (Option (Fin 6))))
    (htetra : ∀ s ∈ T, s.card = 4)
    (hthree : ∀ s : Finset (Option (Fin 6)), s.card = 3 → (T.filter (s ⊆ ·)).card ≠ 1)
    (hfive : ∀ s : Finset (Option (Fin 6)), s.card = 5 → (T.filter (· ⊆ s)).card ≤ 3) :
    T.card ≠ 11 := by
  intro hEleven
  have hseven : Fintype.card (Option (Fin 6)) = 7 := by
    rw [Fintype.card_option, Fintype.card_fin]
  have hpivot : ∃ v : Option (Fin 6), 7 ≤ (T.filter (v ∈ ·)).card := by
    by_contra h
    have hbound (v : Option (Fin 6)) : (T.filter (v ∈ ·)).card ≤ 6 := by
      by_contra hle
      exact h ⟨v, by omega⟩
    have hsum : T.card * 4 ≤ (univ : OptionFace).card * 6 := by
      refine card_mul_le_card_mul (fun (s : OptionFace) v => v ∈ s) ?_ ?_
      · intro s hs
        change 4 ≤ (univ.filter (· ∈ s)).card
        simpa using (htetra s hs).ge
      · intro v _
        exact hbound v
    rw [card_univ, hseven, hEleven] at hsum
    omega
  obtain ⟨v, hv⟩ := hpivot
  let e : Option (Fin 6) ≃ Option (Fin 6) := Equiv.swap v none
  let f := e.finsetCongr
  let U := T.map f.toEmbedding
  have hUcard : U.card = 11 := by simpa [U] using hEleven
  have hUrank (s : OptionFace) (hs : s ∈ U) : s.card = 4 := by
    obtain ⟨t, ht, rfl⟩ := mem_map.mp hs
    simpa [f] using htetra t ht
  have hUthree (s : OptionFace) (hs : s.card = 3) : (U.filter (s ⊆ ·)).card ≠ 1 := by
    obtain ⟨t, rfl⟩ := f.surjective s
    have ht : t.card = 3 := by simpa [f] using hs
    change ((T.map f.toEmbedding).filter (f t ⊆ ·)).card ≠ 1
    rw [filter_map, card_map]
    simpa [Function.comp_def, f] using hthree t ht
  have hUfive (s : OptionFace) (hs : s.card = 5) : (U.filter (· ⊆ s)).card ≤ 3 := by
    obtain ⟨t, rfl⟩ := f.surjective s
    have ht : t.card = 5 := by simpa [f] using hs
    change ((T.map f.toEmbedding).filter (· ⊆ f t)).card ≤ 3
    rw [filter_map, card_map]
    simpa [Function.comp_def, f] using hfive t ht
  have hneg : (U.filter (none ∉ ·)).card ≤ 4 := by
    have hpos : 7 ≤ (U.filter (none ∈ ·)).card := by
      change 7 ≤ ((T.map f.toEmbedding).filter (none ∈ ·)).card
      rw [filter_map, card_map]
      have hmove : e v = none := Equiv.swap_apply_left v none
      simpa [Function.comp_def, f, ← hmove] using hv
    have htotal := card_filter_add_card_filter_not (s := U) (none ∈ ·)
    omega
  have hmin : 1 ≤ (U.filter (none ∉ ·)).card := by
    by_contra h
    have hEmpty : U.filter (none ∉ ·) = ∅ := card_eq_zero.mp (by omega)
    have hnone (s : OptionFace) (hs : s ∈ U) : none ∈ s := by
      by_contra hm
      have hf : s ∈ U.filter (none ∉ ·) := mem_filter.mpr ⟨hs, hm⟩
      simp [hEmpty] at hf
    obtain ⟨s, hs⟩ : U.Nonempty := card_pos.mp (by omega)
    have hRank : (s.erase none).card = 3 := by
      rw [card_erase_of_mem (hnone s hs), hUrank s hs]
    have hf : U.filter (s.erase none ⊆ ·) = {s} := by
      ext t
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨ht, hsub⟩
        apply (eq_of_subset_of_card_le ?_ (by rw [hUrank s hs, hUrank t ht])).symm
        rw [← insert_erase (hnone s hs)]
        exact insert_subset (hnone t ht) hsub
      · rintro rfl
        exact ⟨hs, erase_subset _ _⟩
    exact hUthree (s.erase none) hRank (by simp [hf])
  have h := tetrahedra_card_eq_nine_or_twelve U hUrank hUthree hUfive hmin hneg
  omega

end Q9SevenVertexCocycle

namespace Q9TetrahedronEleven

open Finset

private theorem transport {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (e : X ≃ Y) (C : Finset (Finset X))
    (hRank : ∀ t ∈ C, t.card = 4)
    (hNo : ∀ s : Finset X, s.card = 3 → (C.filter (s ⊆ ·)).card ≠ 1)
    (hCap : ∀ W : Finset X, W.card = 5 → (C.filter (· ⊆ W)).card ≤ 3) :
    let D := C.map e.finsetCongr.toEmbedding
    (∀ t ∈ D, t.card = 4) ∧
      (∀ s : Finset Y, s.card = 3 → (D.filter (s ⊆ ·)).card ≠ 1) ∧
      (∀ W : Finset Y, W.card = 5 → (D.filter (· ⊆ W)).card ≤ 3) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := mem_map.mp ht
    simpa using hRank s hs
  · intro s hs
    obtain ⟨t, rfl⟩ := e.finsetCongr.surjective s
    rw [filter_map, card_map]
    simpa [Function.comp_def] using hNo t (by simpa using hs)
  · intro W hW
    obtain ⟨S, rfl⟩ := e.finsetCongr.surjective W
    rw [filter_map, card_map]
    simpa [Function.comp_def] using hCap S (by simpa using hW)

private theorem on_six_or_seven {X : Type*} [Fintype X] [DecidableEq X]
    (hSize : Fintype.card X = 6 ∨ Fintype.card X = 7) (C : Finset (Finset X))
    (hRank : ∀ t ∈ C, t.card = 4)
    (hNo : ∀ s : Finset X, s.card = 3 → (C.filter (s ⊆ ·)).card ≠ 1)
    (hCap : ∀ W : Finset X, W.card = 5 → (C.filter (· ⊆ W)).card ≤ 3) :
    C.card ≠ 11 := by
  rcases hSize with hs | hs
  · intro hEleven
    have hCount : C.card * 2 ≤ (univ : Finset X).card * 3 := by
      refine card_mul_le_card_mul (fun (t : Finset X) v => v ∉ t) ?_ ?_
      · intro t ht
        have hSplit := card_filter_add_card_filter_not (s := (univ : Finset X)) (· ∈ t)
        change 2 ≤ (univ.filter (· ∉ t)).card
        simp [hs, hRank t ht] at hSplit
        omega
      · intro v _
        have hFive : ((univ : Finset X).erase v).card = 5 := by
          rw [card_erase_of_mem (mem_univ v), card_univ, hs]
        apply (le_of_eq ?_).trans (hCap _ hFive)
        congr 1
        ext t
        simp [bipartiteBelow, subset_iff]
    rw [hEleven, card_univ, hs] at hCount
    omega
  · have hOption : Fintype.card (Option (Fin 6)) = 7 := by simp
    let e := (Fintype.equivFinOfCardEq hs).trans (Fintype.equivFinOfCardEq hOption).symm
    obtain ⟨hr, hn, hc⟩ := transport e C hRank hNo hCap
    have h := Q9SevenVertexCocycle.tetrahedra_card_ne_eleven_on_seven_vertices _ hr hn hc
    simpa only [card_map] using h

/-- No family of exactly eleven tetrahedra can satisfy the five-set cap and
avoid singleton three-face incidences. The statement depends only on the
support, and applies to oriented cycles over the reals. -/
theorem tetrahedra_card_ne_eleven_on_small_support {V : Type*} [DecidableEq V]
    (C : Finset (Finset V)) (hRank : ∀ t ∈ C, t.card = 4)
    (hNo : ∀ s : Finset V, s.card = 3 → (C.filter (s ⊆ ·)).card ≠ 1)
    (hCap : ∀ W : Finset V, W.card ≤ 5 → (C.filter (· ⊆ W)).card ≤ 3)
    (hSize : (Q9TriangleSupportReduction.support C).card = 6 ∨
      (Q9TriangleSupportReduction.support C).card = 7) :
    C.card ≠ 11 := by
  classical
  intro hEleven
  let X := Q9TriangleSupportReduction.support C
  let liftVertex : X ↪ V := Function.Embedding.subtype _
  let liftFace := (mapEmbedding liftVertex).toEmbedding
  let restrict (t : Finset V) : Finset X := t.subtype (· ∈ X)
  let D := C.image restrict
  have hlift (t : Finset V) (ht : t ∈ C) : liftFace (restrict t) = t := by
    change (t.subtype (· ∈ X)).map (Function.Embedding.subtype _) = t
    apply subtype_map_of_mem
    exact subset_biUnion_of_mem id ht
  have hmap : D.map liftFace = C := by
    ext t
    constructor
    · intro ht
      obtain ⟨s, hs, rfl⟩ := mem_map.mp ht
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hs
      rwa [hlift a ha]
    · intro ht
      exact mem_map.mpr ⟨restrict t, mem_image.mpr ⟨t, ht, rfl⟩, hlift t ht⟩
  have hDcard : D.card = C.card := by rw [← hmap, card_map]
  have hDRank : ∀ t ∈ D, t.card = 4 := by
    intro t ht
    have hm : t.map liftVertex ∈ C := by
      rw [← hmap]
      exact mem_map.mpr ⟨t, ht, rfl⟩
    simpa using hRank (t.map liftVertex) hm
  have hDNo (s : Finset X) (hs : s.card = 3) : (D.filter (s ⊆ ·)).card ≠ 1 := by
    have hfilter : C.filter (s.map liftVertex ⊆ ·) = (D.filter (s ⊆ ·)).map liftFace := by
      rw [← hmap, filter_map]
      congr 1
      ext t
      simp [Function.comp_def, liftFace]
    have h := hNo (s.map liftVertex) (by simpa)
    rwa [hfilter, card_map] at h
  have hDCap (W : Finset X) (hW : W.card = 5) : (D.filter (· ⊆ W)).card ≤ 3 := by
    have hfilter : C.filter (· ⊆ W.map liftVertex) = (D.filter (· ⊆ W)).map liftFace := by
      rw [← hmap, filter_map]
      congr 1
      ext t
      simp [Function.comp_def, liftFace]
    have h := hCap (W.map liftVertex) (by simp [hW])
    rwa [hfilter, card_map] at h
  have hCardX : Fintype.card X = 6 ∨ Fintype.card X = 7 := by simpa using hSize
  exact on_six_or_seven hCardX D hDRank hDNo hDCap (hDcard.trans hEleven)

/-- There is no eleven-facet tetrahedral support with the five-set cap
and without a singleton triangle coface. -/
theorem tetrahedra_card_ne_eleven {V : Type*} [DecidableEq V]
    (C : Finset (Finset V)) (hRank : ∀ t ∈ C, t.card = 4)
    (hNo : ∀ s : Finset V, s.card = 3 → (C.filter (s ⊆ ·)).card ≠ 1)
    (hCap : ∀ W : Finset V, W.card ≤ 5 → (C.filter (· ⊆ W)).card ≤ 3) :
    C.card ≠ 11 := by
  intro hEleven
  have ⟨hl, hu⟩ := Q9TetrahedronLinkBound.support_card_bounds_of_eleven hRank hNo hCap hEleven
  exact tetrahedra_card_ne_eleven_on_small_support C hRank hNo hCap (by omega) hEleven

end Q9TetrahedronEleven
