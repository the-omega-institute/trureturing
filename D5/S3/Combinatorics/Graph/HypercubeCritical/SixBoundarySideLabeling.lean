/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideLabeling
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideLabeling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Private local finite graph arguments for the six-boundary side gap. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideCore

/-! Local neighbor counts, rather than graph enumeration, obstruct the exceptional
seven-vertex auxiliary graph and label the eight-vertex auxiliary cube. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideGap

open scoped BigOperators Classical
open SimpleGraph
open GirthSliceCounting
attribute [local instance] Classical.propDecidable
open private eleven_side_spectrum eleven_left_structure from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideCounting
open private sideCore edgeLabels side_core_triangle_free eleven_core_data
  low_partner side_core_partner partner_no_shared_high from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideCore

variable {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W}

private theorem triangle_free_neighbor_disjoint
    (ht : ∀ x y z, H.Adj x y → H.Adj y z → H.Adj z x → False)
    {x y : W} (hxy : H.Adj x y) : Disjoint (H.neighborFinset x) (H.neighborFinset y) := by
  apply Finset.disjoint_left.mpr
  intro z hzx hzy
  exact ht x y z hxy ((H.mem_neighborFinset _ _).mp hzy)
    ((H.mem_neighborFinset _ _).mp hzx).symm

private theorem seven_deficient_edge_no_partner
    (hW : Fintype.card W = 7)
    (ht : ∀ x y z, H.Adj x y → H.Adj y z → H.Adj z x → False)
    (v : W) (hv : H.degree v = 2)
    (hd : ∀ x, x ≠ v → H.degree x = 3)
    {a : W} (hva : H.Adj v a) :
    ¬ ∃ x y, H.Adj x y ∧
      (∀ s ∈ ({v, a} : Finset W), ∀ t ∈ ({x, y} : Finset W),
        s ≠ t ∧ ¬ H.Adj s t) := by
  rintro ⟨x, y, hxy, hp⟩
  have hva' := H.ne_of_adj hva
  have hxy' := H.ne_of_adj hxy
  have hxv := (hp v (by simp) x (by simp)).1.symm
  have hyv := (hp v (by simp) y (by simp)).1.symm
  have hxa := (hp a (by simp) x (by simp)).1.symm
  have hya := (hp a (by simp) y (by simp)).1.symm
  let F := H.neighborFinset v ∪ H.neighborFinset a
  have hF : F.card = 5 := by
    rw [Finset.card_union_of_disjoint (triangle_free_neighbor_disjoint ht hva)]
    simp only [SimpleGraph.card_neighborFinset_eq_degree, hv, hd a hva'.symm]
  have hvF : v ∈ F := Finset.mem_union_right _ ((H.mem_neighborFinset _ _).mpr hva.symm)
  have haF : a ∈ F := Finset.mem_union_left _ ((H.mem_neighborFinset _ _).mpr hva)
  have hxF : x ∉ F := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact (hp v (by simp) x (by simp)).2 ((H.mem_neighborFinset _ _).mp h)
    · exact (hp a (by simp) x (by simp)).2 ((H.mem_neighborFinset _ _).mp h)
  have hyF : y ∉ F := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact (hp v (by simp) y (by simp)).2 ((H.mem_neighborFinset _ _).mp h)
    · exact (hp a (by simp) y (by simp)).2 ((H.mem_neighborFinset _ _).mp h)
  have hcomp : Finset.univ \ F = ({x, y} : Finset W) := by
    apply (Finset.eq_of_subset_of_card_le (by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxF⟩,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyF⟩⟩) ?_).symm
    simp [Finset.card_sdiff_of_subset (Finset.subset_univ F), hW, hF, hxy']
  let T := F \ ({v, a} : Finset W)
  have hT : T.card = 3 := by
    have hs : ({v, a} : Finset W) ⊆ F :=
      Finset.insert_subset_iff.mpr ⟨hvF, Finset.singleton_subset_iff.mpr haF⟩
    simp [T, Finset.card_sdiff_of_subset hs, hF, hva']
  have hsub (p q : W) (hpq : H.Adj p q) (hpv : p ≠ v) (hpa : p ≠ a)
      (hnv : ¬ H.Adj v p) (hna : ¬ H.Adj a p)
      (hpair : ({p, q} : Finset W) = {x, y}) :
      (H.neighborFinset p).erase q ⊆ T := by
    intro z hz
    have hz0 := Finset.mem_erase.mp hz
    have hpz := (H.mem_neighborFinset _ _).mp hz0.2
    have hzF : z ∈ F := by
      by_contra hzF
      have hzC : z ∈ Finset.univ \ F := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzF⟩
      rw [hcomp, ← hpair] at hzC
      rcases Finset.mem_insert.mp hzC with h | h
      · exact H.ne_of_adj hpz h.symm
      · exact hz0.1 (Finset.mem_singleton.mp h)
    apply Finset.mem_sdiff.mpr
    refine ⟨hzF, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hnv (h ▸ hpz.symm), fun h => hna (h ▸ hpz.symm)⟩
  have hxsub := hsub x y hxy hxv hxa
    (hp v (by simp) x (by simp)).2 (hp a (by simp) x (by simp)).2 rfl
  have hysub := hsub y x hxy.symm hyv hya
    (hp v (by simp) y (by simp)).2 (hp a (by simp) y (by simp)).2
    (Finset.pair_comm _ _)
  have hdis : Disjoint ((H.neighborFinset x).erase y) ((H.neighborFinset y).erase x) :=
    (triangle_free_neighbor_disjoint ht hxy).mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  have hc := Finset.card_le_card (Finset.union_subset hxsub hysub)
  rw [Finset.card_union_of_disjoint hdis,
    Finset.card_erase_of_mem ((H.mem_neighborFinset _ _).mpr hxy),
    Finset.card_erase_of_mem ((H.mem_neighborFinset _ _).mpr hxy.symm),
    SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree,
    hd x hxv, hd y hyv, hT] at hc
  omega

private theorem eleven_impossible
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hd : ∀ x ∈ L, G.degree x = 3)
    (hr : ∀ y ∈ R, G.degree y ≤ 3) (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 11) (hR : R.card = 13) : False := by
  obtain ⟨hr23, hn3, _⟩ := eleven_side_spectrum hb hd hr hg hL hR
  obtain ⟨r, hrL, hr1, hleft⟩ := eleven_left_structure hb hd hg hL hR hn3
  obtain ⟨v, hvr, huniq, hv2, hother⟩ := eleven_core_data hb hg hrL hr1 hleft
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < ((sideCore G L R).neighborFinset v).card by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hv2]; decide)
  have hva := ((sideCore G L R).mem_neighborFinset _ _).mp ha
  have hno := seven_deficient_edge_no_partner
    (show Fintype.card (degreeThree G R : Set V) = 7 by simpa using hn3)
    (side_core_triangle_free hb hg) v hv2 hother hva
  obtain ⟨_, e, he, hve, hae⟩ := hva
  obtain ⟨m, hm, f, hf, hfe, hem, hfm, _⟩ := low_partner hb hd hr23 he
  have hfr : f ≠ r := by
    intro hfr
    have hvf : G.Adj v.val f := hfr.symm ▸ hvr
    exact partner_no_shared_high hb hg (Finset.mem_filter.mp he).1
      hfe.symm (Finset.mem_filter.mp hm).2 hem hfm v hve hvf
  exact hno (side_core_partner hb hg he
    (Finset.mem_filter.mpr ⟨hf, hleft f hf hfr⟩)
    hfe (Finset.mem_filter.mp hm).2 hem hfm v a hve hae)

private theorem cubic_third_neighbor (hd : ∀ x, H.degree x = 3)
    {p a b : W} (ha : H.Adj p a) (hb : H.Adj p b) (hab : a ≠ b) :
    ∃ c, c ≠ a ∧ c ≠ b ∧ H.Adj p c ∧ H.neighborFinset p = {a, b, c} := by
  have hs : ¬ H.neighborFinset p ⊆ ({a, b} : Finset W) := by
    intro hs
    have hc := Finset.card_le_card hs
    simp [SimpleGraph.card_neighborFinset_eq_degree, hd p, hab] at hc
  obtain ⟨c, hc, hcnot⟩ := Finset.not_subset.mp hs
  have hca : c ≠ a := by intro h; exact hcnot (by simp [h])
  have hcb : c ≠ b := by intro h; exact hcnot (by simp [h])
  refine ⟨c, hca, hcb, (H.mem_neighborFinset _ _).mp hc, ?_⟩
  apply (Finset.eq_of_subset_of_card_le (by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨(H.mem_neighborFinset _ _).mpr ha, (H.mem_neighborFinset _ _).mpr hb, hc⟩) ?_).symm
  simp [SimpleGraph.card_neighborFinset_eq_degree, hd p, hab, hca.symm, hcb.symm]

private theorem cubic_neighbor_table (hd : ∀ x, H.degree x = 3)
    {p a b c : W} (ha : H.Adj p a) (hb : H.Adj p b) (hc : H.Adj p c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    H.neighborFinset p = {a, b, c} := by
  apply (Finset.eq_of_subset_of_card_le (by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨(H.mem_neighborFinset _ _).mpr ha, (H.mem_neighborFinset _ _).mpr hb,
      (H.mem_neighborFinset _ _).mpr hc⟩) ?_).symm
  simp [SimpleGraph.card_neighborFinset_eq_degree, hd p, hab, hac, hbc]

private theorem paired_edge_neighborhoods
    (hW : Fintype.card W = 8) (hd : ∀ x, H.degree x = 3)
    (ht : ∀ x y z, H.Adj x y → H.Adj y z → H.Adj z x → False)
    {u v x y : W} (huv : H.Adj u v) (hxy : H.Adj x y)
    (hp : ∀ s ∈ ({u, v} : Finset W), ∀ t ∈ ({x, y} : Finset W),
      s ≠ t ∧ ¬ H.Adj s t) :
    H.neighborFinset u ∪ H.neighborFinset v = Finset.univ \ {x, y} := by
  have hs : H.neighborFinset u ∪ H.neighborFinset v ⊆ Finset.univ \ {x, y} := by
    intro z hz
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hzxy
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (hp u (by simp) z hzxy).2 ((H.mem_neighborFinset _ _).mp hz)
    · exact (hp v (by simp) z hzxy).2 ((H.mem_neighborFinset _ _).mp hz)
  apply Finset.eq_of_subset_of_card_le hs
  rw [Finset.card_union_of_disjoint (triangle_free_neighbor_disjoint ht huv)]
  simp [SimpleGraph.card_neighborFinset_eq_degree, hd,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), hW, H.ne_of_adj hxy]

private def cubeEightNeighbors : Fin 8 → Finset (Fin 8) :=
  ![{1,2,3}, {0,6,7}, {0,4,6}, {0,4,7}, {2,3,5}, {4,6,7}, {1,2,5}, {1,3,5}]

private theorem eight_vector_injective {u v a b x y c d : W}
    (h : [u,v,a,b,x,y,c,d].Nodup) :
    Function.Injective (![u,v,a,b,x,y,c,d] : Fin 8 → W) := by
  have he : (![u,v,a,b,x,y,c,d] : Fin 8 → W) =
      fun i => [u,v,a,b,x,y,c,d].get i := by
    funext i; fin_cases i <;> rfl
  rw [he]
  exact List.nodup_iff_injective_get.mp h

private theorem cube_eight_labeling
    (hW : Fintype.card W = 8) (hd : ∀ x, H.degree x = 3)
    (ht : ∀ x y z, H.Adj x y → H.Adj y z → H.Adj z x → False)
    (hpairs : ∀ u v, H.Adj u v → ∃ x y, H.Adj x y ∧
      (∀ s ∈ ({u, v} : Finset W), ∀ t ∈ ({x, y} : Finset W),
        s ≠ t ∧ ¬ H.Adj s t)) :
    ∃ f : Fin 8 → W, Function.Bijective f ∧
      ∀ i z, H.Adj (f i) z ↔ z ∈ (cubeEightNeighbors i).image f := by
  obtain ⟨u, _⟩ := Finset.card_pos.mp (show 0 < (Finset.univ : Finset W).card by simp [hW])
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < (H.neighborFinset u).card by
    simp [SimpleGraph.card_neighborFinset_eq_degree, hd])
  have huv := (H.mem_neighborFinset _ _).mp hv
  obtain ⟨x0, y0, hxy0, hp0⟩ := hpairs u v huv
  obtain ⟨a, ha, hav⟩ := Finset.exists_mem_ne (show 1 < (H.neighborFinset u).card by
    simp [SimpleGraph.card_neighborFinset_eq_degree, hd]) v
  have hua := (H.mem_neighborFinset _ _).mp ha
  have hau := (H.ne_of_adj hua).symm
  have hswap0 : ∀ s ∈ ({x0, y0} : Finset W), ∀ t ∈ ({u, v} : Finset W),
      s ≠ t ∧ ¬ H.Adj s t := by
    intro s hs t ht'
    exact ⟨(hp0 t ht' s hs).1.symm, fun h => (hp0 t ht' s hs).2 h.symm⟩
  have hcolors := paired_edge_neighborhoods hW hd ht hxy0 huv hswap0
  have haXY : H.Adj a x0 ∨ H.Adj a y0 := by
    have hh : a ∈ H.neighborFinset x0 ∪ H.neighborFinset y0 := by
      rw [hcolors]
      simp [hau, hav]
    simpa only [Finset.mem_union, SimpleGraph.mem_neighborFinset, H.adj_comm] using hh
  obtain ⟨x, y, hxy, hp, hax⟩ : ∃ x y, H.Adj x y ∧
      (∀ s ∈ ({u, v} : Finset W), ∀ t ∈ ({x, y} : Finset W),
        s ≠ t ∧ ¬ H.Adj s t) ∧ H.Adj a x := by
    rcases haXY with h | h
    · exact ⟨x0, y0, hxy0, hp0, h⟩
    · exact ⟨y0, x0, hxy0.symm, by simpa only [Finset.pair_comm y0 x0] using hp0, h⟩
  have hux := (hp u (by simp) x (by simp)).1
  have hswap : ∀ s ∈ ({x, y} : Finset W), ∀ t ∈ ({u, v} : Finset W),
      s ≠ t ∧ ¬ H.Adj s t := by
    intro s hs t ht'
    exact ⟨(hp t ht' s hs).1.symm, fun h => (hp t ht' s hs).2 h.symm⟩
  have hcolorUV := paired_edge_neighborhoods hW hd ht huv hxy hp
  have hcolorXY := paired_edge_neighborhoods hW hd ht hxy huv hswap
  obtain ⟨c, hcu, hcx, hac, hNa⟩ := cubic_third_neighbor hd hua.symm hax hux
  have hcv : c ≠ v := by
    intro h
    exact ht a u v hua.symm huv (h ▸ hac).symm
  have hcy : c ≠ y := by
    intro h
    exact ht a x y hax hxy (h ▸ hac).symm
  have hvc : H.Adj v c := by
    have hh : c ∈ H.neighborFinset u ∪ H.neighborFinset v := by
      rw [hcolorUV]; simp [hcx, hcy]
    rcases Finset.mem_union.mp hh with h | h
    · exact (ht u a c hua hac ((H.mem_neighborFinset _ _).mp h).symm).elim
    · exact (H.mem_neighborFinset _ _).mp h
  have hyc : H.Adj y c := by
    have hh : c ∈ H.neighborFinset x ∪ H.neighborFinset y := by
      rw [hcolorXY]; simp [hcu, hcv]
    rcases Finset.mem_union.mp hh with h | h
    · exact (ht x a c hax.symm hac ((H.mem_neighborFinset _ _).mp h).symm).elim
    · exact (H.mem_neighborFinset _ _).mp h
  obtain ⟨b, hbv, hba, hub, hNu⟩ := cubic_third_neighbor hd huv hua hav.symm
  obtain ⟨d, hdu, hdc, hvd, hNv⟩ := cubic_third_neighbor hd huv.symm hvc hcu.symm
  have hcross : ∀ p ∈ ({a, b} : Finset W), ∀ q ∈ ({c, d} : Finset W), p ≠ q := by
    intro p hp' q hq hpq
    have hpu : p ∈ H.neighborFinset u := by
      rw [hNu]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp' ⊢
      tauto
    have hqv : q ∈ H.neighborFinset v := by
      rw [hNv]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      tauto
    exact Finset.disjoint_left.mp (triangle_free_neighbor_disjoint ht huv) hpu (hpq ▸ hqv)
  let f : Fin 8 → W := ![u,v,a,b,x,y,c,d]
  have hinj : Function.Injective f := by
    have huv' := H.ne_of_adj huv
    have hxy' := H.ne_of_adj hxy
    have hbu := (H.ne_of_adj hub).symm
    have hcv' := (H.ne_of_adj hvc).symm
    have hdv := (H.ne_of_adj hvd).symm
    have haux : a ≠ x := fun h => (hp u (by simp) x (by simp)).2 (h ▸ hua)
    have hauy : a ≠ y := fun h => (hp u (by simp) y (by simp)).2 (h ▸ hua)
    have hbux : b ≠ x := fun h => (hp u (by simp) x (by simp)).2 (h ▸ hub)
    have hbuy : b ≠ y := fun h => (hp u (by simp) y (by simp)).2 (h ▸ hub)
    have hcvx : c ≠ x := hcx
    have hcvy : c ≠ y := hcy
    have hdvx : d ≠ x := fun h => (hp v (by simp) x (by simp)).2 (h ▸ hvd)
    have hdvy : d ≠ y := fun h => (hp v (by simp) y (by simp)).2 (h ▸ hvd)
    have huy := (hp u (by simp) y (by simp)).1
    have hvx := (hp v (by simp) x (by simp)).1
    have hvy := (hp v (by simp) y (by simp)).1
    have hac' := hcross a (by simp) c (by simp)
    have had' := hcross a (by simp) d (by simp)
    have hbc' := hcross b (by simp) c (by simp)
    have hbd' := hcross b (by simp) d (by simp)
    apply eight_vector_injective
    simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or,
      not_false_eq_true, List.nodup_nil, and_true]
    exact ⟨⟨huv', hau.symm, hbu.symm, hux, huy, hcu.symm, hdu.symm⟩,
      ⟨hav.symm, hbv.symm, hvx, hvy, hcv'.symm, hdv.symm⟩,
      ⟨hba.symm, haux, hauy, hac', had'⟩,
      ⟨hbux, hbuy, hbc', hbd'⟩, ⟨hxy', hcvx.symm, hdvx.symm⟩,
      ⟨hcvy.symm, hdvy.symm⟩, hdc.symm⟩
  have hcover (z : W) : z = u ∨ z = v ∨ z = a ∨ z = b ∨ z = x ∨ z = y ∨ z = c ∨ z = d := by
    have hall : Finset.univ.image f = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_image_of_injective _ hinj]
      simp [hW]
    have hz : z ∈ Finset.univ.image f := by rw [hall]; exact Finset.mem_univ _
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i <;> simp [f]
  have hne (i j : Fin 8) (h : i ≠ j) : f i ≠ f j := hinj.ne h
  have hNc : H.neighborFinset c = {v,y,a} :=
    cubic_neighbor_table hd hvc.symm hyc.symm hac.symm
      (hne 1 5 (by decide)) (hne 1 2 (by decide)) (hne 5 2 (by decide))
  have hbXY : H.Adj b x ∨ H.Adj b y := by
    have hh : b ∈ H.neighborFinset x ∪ H.neighborFinset y := by
      rw [hcolorXY]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne 3 0 (by decide), hbv⟩⟩
    simpa only [Finset.mem_union, SimpleGraph.mem_neighborFinset, H.adj_comm] using hh
  have hnotba : ¬ H.Adj b a := by
    intro h
    have hh := (H.mem_neighborFinset _ _).mpr h.symm
    rw [hNa] at hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with h | h | h
    · exact hne 3 0 (by decide) h
    · exact hne 3 4 (by decide) h
    · exact hne 3 6 (by decide) h
  have hnotbc : ¬ H.Adj b c := by
    intro h
    have hh := (H.mem_neighborFinset _ _).mpr h.symm
    rw [hNc] at hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with h | h | h
    · exact hne 3 1 (by decide) h
    · exact hne 3 5 (by decide) h
    · exact hne 3 2 (by decide) h
  have hbd : H.Adj b d := by
    rcases hbXY with hbx | hby
    · obtain ⟨z, hzu, hzx, hbz, _⟩ := cubic_third_neighbor hd hub.symm hbx hux
      rcases hcover z with hz | hz | hz | hz | hz | hz | hz | hz
      all_goals subst z
      · exact (hzu rfl).elim
      · exact (ht u v b huv hbz.symm hub.symm).elim
      · exact (hnotba hbz).elim
      · exact (H.ne_of_adj hbz rfl).elim
      · exact (hzx rfl).elim
      · exact (ht b x y hbx hxy hbz.symm).elim
      · exact (hnotbc hbz).elim
      · exact hbz
    · obtain ⟨z, hzu, hzy, hbz, _⟩ := cubic_third_neighbor hd hub.symm hby
        (hne 0 5 (by decide))
      rcases hcover z with hz | hz | hz | hz | hz | hz | hz | hz
      all_goals subst z
      · exact (hzu rfl).elim
      · exact (ht u v b huv hbz.symm hub.symm).elim
      · exact (hnotba hbz).elim
      · exact (H.ne_of_adj hbz rfl).elim
      · exact (ht b y x hby hxy.symm hbz.symm).elim
      · exact (hzy rfl).elim
      · exact (hnotbc hbz).elim
      · exact hbz
  have hbyfalse : ¬ H.Adj b y := by
    intro hby
    have hNy := cubic_neighbor_table hd hxy.symm hyc hby.symm
      (hne 4 6 (by decide)) (hne 4 3 (by decide)) (hne 6 3 (by decide))
    have hdx : H.Adj d x := by
      have hh : d ∈ H.neighborFinset x ∪ H.neighborFinset y := by
        rw [hcolorXY]
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hne 7 0 (by decide), hne 7 1 (by decide)⟩⟩
      rcases Finset.mem_union.mp hh with hh | hh
      · exact ((H.mem_neighborFinset _ _).mp hh).symm
      · rw [hNy] at hh
        simp only [Finset.mem_insert, Finset.mem_singleton] at hh
        rcases hh with h | h | h
        · exact (hne 7 4 (by decide) h).elim
        · exact (hne 7 6 (by decide) h).elim
        · exact (hne 7 3 (by decide) h).elim
    obtain ⟨p, q, hpq, hsep⟩ := hpairs u a hua
    have hremaining (z : W) (hz : ∀ s ∈ ({u,a} : Finset W), s ≠ z ∧ ¬ H.Adj s z) :
        z = y ∨ z = d := by
      rcases hcover z with hz | hz | hz | hz | hz | hz | hz | hz
      all_goals subst z
      · exact ((hz u (by simp)).1 rfl).elim
      · exact ((hz u (by simp)).2 huv).elim
      · exact ((hz a (by simp)).1 rfl).elim
      · exact ((hz u (by simp)).2 hub).elim
      · exact ((hz a (by simp)).2 hax).elim
      · exact Or.inl rfl
      · exact ((hz a (by simp)).2 hac).elim
      · exact Or.inr rfl
    have hp' := hremaining p (fun s hs => hsep s hs p (by simp))
    have hq' := hremaining q (fun s hs => hsep s hs q (by simp))
    have hnotyd : ¬ H.Adj y d := by
      intro h
      have hh := (H.mem_neighborFinset _ _).mpr h
      rw [hNy] at hh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with h | h | h
      · exact hne 7 4 (by decide) h
      · exact hne 7 6 (by decide) h
      · exact hne 7 3 (by decide) h
    rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
    · exact H.ne_of_adj hpq rfl
    · exact hnotyd hpq
    · exact hnotyd hpq.symm
    · exact H.ne_of_adj hpq rfl
  have hbx := hbXY.resolve_right hbyfalse
  have hNx := cubic_neighbor_table hd hxy hax.symm hbx.symm
    (hne 5 2 (by decide)) (hne 5 3 (by decide)) (hne 2 3 (by decide))
  have hyd : H.Adj y d := by
    have hh : d ∈ H.neighborFinset x ∪ H.neighborFinset y := by
      rw [hcolorXY]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne 7 0 (by decide), hne 7 1 (by decide)⟩⟩
    rcases Finset.mem_union.mp hh with hh | hh
    · rw [hNx] at hh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with h | h | h
      · exact (hne 7 5 (by decide) h).elim
      · exact (hne 7 2 (by decide) h).elim
      · exact (hne 7 3 (by decide) h).elim
    · exact (H.mem_neighborFinset _ _).mp hh
  have hNb := cubic_neighbor_table hd hub.symm hbx hbd
    (hne 0 4 (by decide)) (hne 0 7 (by decide)) (hne 4 7 (by decide))
  have hNy := cubic_neighbor_table hd hxy.symm hyc hyd
    (hne 4 6 (by decide)) (hne 4 7 (by decide)) (hne 6 7 (by decide))
  have hNd := cubic_neighbor_table hd hvd.symm hbd.symm hyd.symm
    (hne 1 3 (by decide)) (hne 1 5 (by decide)) (hne 3 5 (by decide))
  have hrow (p r s t z : W) (hn : H.neighborFinset p = {r,s,t}) :
      H.Adj p z ↔ z = r ∨ z = s ∨ z = t := by
    rw [← SimpleGraph.mem_neighborFinset, hn]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  refine ⟨f, ⟨hinj, ?_⟩, ?_⟩
  · intro z
    rcases hcover z with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ |
      exact ⟨3,rfl⟩ | exact ⟨4,rfl⟩ | exact ⟨5,rfl⟩ | exact ⟨6,rfl⟩ | exact ⟨7,rfl⟩
  · intro i z
    fin_cases i
    all_goals first
      | simpa [f, cubeEightNeighbors, SimpleGraph.neighborFinset_def, Set.mem_toFinset, SimpleGraph.mem_neighborSet, or_comm, or_left_comm, or_assoc] using hrow u v a b z hNu
      | simpa [f, cubeEightNeighbors, SimpleGraph.neighborFinset_def, Set.mem_toFinset, SimpleGraph.mem_neighborSet, or_comm, or_left_comm, or_assoc] using hrow v u c d z hNv
      | simpa [f, cubeEightNeighbors, SimpleGraph.neighborFinset_def, Set.mem_toFinset, SimpleGraph.mem_neighborSet, or_comm, or_left_comm, or_assoc] using hrow a u x c z hNa
      | simpa [f, cubeEightNeighbors, SimpleGraph.neighborFinset_def, Set.mem_toFinset, SimpleGraph.mem_neighborSet, or_comm, or_left_comm, or_assoc] using hrow b u x d z hNb
      | simpa [f, cubeEightNeighbors, SimpleGraph.neighborFinset_def, Set.mem_toFinset, SimpleGraph.mem_neighborSet, or_comm, or_left_comm, or_assoc] using hrow x y a b z hNx
      | simpa [f, cubeEightNeighbors, SimpleGraph.neighborFinset_def, Set.mem_toFinset, SimpleGraph.mem_neighborSet, or_comm, or_left_comm, or_assoc] using hrow y x c d z hNy
      | simpa [f, cubeEightNeighbors, SimpleGraph.neighborFinset_def, Set.mem_toFinset, SimpleGraph.mem_neighborSet, or_comm, or_left_comm, or_assoc] using hrow c v y a z hNc
      | simpa [f, cubeEightNeighbors, SimpleGraph.neighborFinset_def, Set.mem_toFinset, SimpleGraph.mem_neighborSet, or_comm, or_left_comm, or_assoc] using hrow d v b y z hNd

end D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideGap
