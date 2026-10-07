/- GID: D5/S3/Combinatorics/Graph/RankThreeLocalCutDensity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/RankThreeLocalCutDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Local trace cut bounds yield seven colors and weighted support density. -/

import D5.S3.Combinatorics.Graph.BipartiteSubgraphDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators
open D5.S3.Combinatorics.Graph.BipartiteSubgraphDensity

namespace D5.S3.Combinatorics.Graph.RankThreeLocalCutDensity

variable {α ι : Type*} [DecidableEq α]

def TraceCap (V : Finset α) (I : Finset ι) (A : ι → Finset α) : Prop :=
  ∀ S ⊆ V, ∀ L ⊆ S, CutAverage.ownerCount I (fun i => A i ∩ S) L ≤ S.card

def traceWeight (T : Finset α) : Nat := if 2 ≤ T.card then T.card else 0

theorem cross_weight_eq (S T : Finset α) (hTS : T ⊆ S) (hrank : T.card ≤ 3) :
    4 * CutAverage.crossCount S T = traceWeight T * 2 ^ S.card := by
  by_cases h0 : T.card = 0
  · have ht : T = ∅ := card_eq_zero.mp h0
    simp [ht, traceWeight, CutAverage.crossCount, CutAverage.Cross]
  have hT : T.Nonempty := card_pos.mp (by omega)
  rw [CutAverage.cross_count_nonempty S T hTS hT]
  have hn := card_le_card hTS
  have hp : 0 < 2 ^ S.card := pow_pos (by decide) _
  rcases (show T.card = 1 ∨ T.card = 2 ∨ T.card = 3 by omega) with h1 | h2 | h3
  · have he : S.card - T.card + 1 = S.card := by omega
    rw [he]
    simp [traceWeight, h1]
  · have he : S.card - T.card + 1 = S.card - 1 := by omega
    have hp' : 2 ^ S.card = 2 * 2 ^ (S.card - 1) := by
      have he' : S.card = S.card - 1 + 1 := by omega
      conv_lhs => rw [he']
      rw [pow_succ, Nat.mul_comm]
    rw [he, hp']
    simp only [traceWeight, h2, le_refl, ↓reduceIte]
    omega
  · have he : S.card - T.card + 1 = S.card - 2 := by omega
    have hp' : 2 ^ S.card = 4 * 2 ^ (S.card - 2) := by
      have he' : S.card = S.card - 2 + 2 := by omega
      conv_lhs => rw [he']
      rw [pow_add]
      norm_num
      omega
    rw [he, hp']
    simp only [traceWeight, h3, Nat.reduceLeDiff, ↓reduceIte]
    omega

theorem trace_weight_sparse (V : Finset α) (I : Finset ι) (A : ι → Finset α)
    (hrank : ∀ i ∈ I, (A i).card ≤ 3) (hcap : TraceCap V I A)
    (S : Finset α) (hSV : S ⊆ V) (hS : S.Nonempty) :
    (∑ i ∈ I, traceWeight (A i ∩ S)) < 4 * S.card := by
  have hsum : (∑ i ∈ I, traceWeight (A i ∩ S)) * 2 ^ S.card =
      4 * ∑ L ∈ S.powerset, CutAverage.ownerCount I (fun i => A i ∩ S) L := by
    rw [← CutAverage.double_count, sum_mul, mul_sum]
    apply sum_congr rfl
    intro i hi
    exact (cross_weight_eq S _ inter_subset_right
      ((card_le_card inter_subset_left).trans (hrank i hi))).symm
  have hstrict : (∑ L ∈ S.powerset, CutAverage.ownerCount I (fun i => A i ∩ S) L) <
      ∑ _L ∈ S.powerset, S.card := by
    apply sum_lt_sum
    · intro L hL
      exact hcap S hSV L (mem_powerset.mp hL)
    · exact ⟨∅, empty_mem_powerset S, by
        rw [CutAverage.empty_cut_count]
        exact card_pos.mpr hS⟩
  simp only [sum_const, card_powerset, smul_eq_mul] at hstrict
  have hp : 0 < 2 ^ S.card := pow_pos (by decide) _
  nlinarith

def ownersAt (I : Finset ι) (A : ι → Finset α) (S : Finset α) (v : α) : Finset ι :=
  I.filter fun i => v ∈ A i ∩ S ∧ 2 ≤ (A i ∩ S).card

theorem sum_ownersAt (I : Finset ι) (A : ι → Finset α) (S : Finset α) :
    (∑ v ∈ S, (ownersAt I A S v).card) = ∑ i ∈ I, traceWeight (A i ∩ S) := by
  have hd := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := S) (t := I) (fun v i => v ∈ A i ∩ S ∧ 2 ≤ (A i ∩ S).card)
  change (∑ v ∈ S, (I.filter fun i => v ∈ A i ∩ S ∧ 2 ≤ (A i ∩ S).card).card) =
    ∑ i ∈ I, (S.filter fun v => v ∈ A i ∩ S ∧ 2 ≤ (A i ∩ S).card).card at hd
  unfold ownersAt
  rw [hd]
  apply sum_congr rfl
  intro i hi
  by_cases hb : 2 ≤ (A i ∩ S).card
  · have he : S.filter (fun v => v ∈ A i ∩ S ∧ 2 ≤ (A i ∩ S).card) = A i ∩ S := by
      ext v
      simp [hb]
    rw [he]
    simp [traceWeight, hb]
  · simp [traceWeight, hb]

theorem exists_few_owners (V : Finset α) (I : Finset ι) (A : ι → Finset α)
    (hrank : ∀ i ∈ I, (A i).card ≤ 3) (hcap : TraceCap V I A)
    (S : Finset α) (hSV : S ⊆ V) (hS : S.Nonempty) :
    ∃ v ∈ S, (ownersAt I A S v).card ≤ 3 := by
  have hs := trace_weight_sparse V I A hrank hcap S hSV hS
  rw [← sum_ownersAt] at hs
  by_contra h
  have hh : ∀ v ∈ S, 4 ≤ (ownersAt I A S v).card := by
    intro v hv
    by_contra hn
    exact h ⟨v, hv, by omega⟩
  have hsum := sum_le_sum hh
  simp only [sum_const, smul_eq_mul] at hsum
  omega

def neighbors (I : Finset ι) (A : ι → Finset α) (S : Finset α) (v : α) : Finset α :=
  (ownersAt I A S v).biUnion fun i => (A i ∩ S).erase v

theorem neighbors_card (I : Finset ι) (A : ι → Finset α)
    (hrank : ∀ i ∈ I, (A i).card ≤ 3) (S : Finset α) (v : α) :
    (neighbors I A S v).card ≤ 2 * (ownersAt I A S v).card := by
  calc
    _ ≤ ∑ i ∈ ownersAt I A S v, ((A i ∩ S).erase v).card := card_biUnion_le
    _ ≤ ∑ _i ∈ ownersAt I A S v, 2 := by
      apply sum_le_sum
      intro i hi
      have hm := mem_filter.mp hi
      have hcard :=
        (card_le_card (inter_subset_left (s₁ := A i) (s₂ := S))).trans (hrank i hm.1)
      rw [card_erase_of_mem hm.2.1]
      omega
    _ = _ := by simp [Nat.mul_comm]

theorem mem_neighbors {I : Finset ι} {A : ι → Finset α} {S : Finset α}
    {i : ι} (hi : i ∈ I) {v w : α} (hv : v ∈ A i) (hw : w ∈ A i)
    (hvS : v ∈ S) (hwS : w ∈ S) (hne : w ≠ v) :
    w ∈ neighbors I A S v := by
  apply mem_biUnion.mpr
  refine ⟨i, ?_, mem_erase.mpr ⟨hne, mem_inter.mpr ⟨hw,hwS⟩⟩⟩
  apply mem_filter.mpr
  have hc : 1 < (A i ∩ S).card := one_lt_card.mpr
    ⟨v, mem_inter.mpr ⟨hv,hvS⟩, w, mem_inter.mpr ⟨hw,hwS⟩, hne.symm⟩
  exact ⟨hi, mem_inter.mpr ⟨hv,hvS⟩, hc⟩

theorem strong_seven_coloring (V : Finset α) (I : Finset ι) (A : ι → Finset α)
    (hrank : ∀ i ∈ I, (A i).card ≤ 3) (hcap : TraceCap V I A) :
    ∃ c : α → Fin 7, ∀ i ∈ I, ∀ x ∈ A i, ∀ y ∈ A i,
      x ∈ V → y ∈ V → x ≠ y → c x ≠ c y := by
  induction V using Finset.strongInductionOn with
  | _ V ih =>
    by_cases hV : V.Nonempty
    · obtain ⟨v,hv,hfew⟩ := exists_few_owners V I A hrank hcap V (Subset.refl _) hV
      have hcap' : TraceCap (V.erase v) I A := by
        intro S hS L hL
        exact hcap S (hS.trans (erase_subset v V)) L hL
      obtain ⟨c,hc⟩ := ih (V.erase v) (erase_ssubset hv) hcap'
      let used := (neighbors I A V v).image c
      have hused : used.card < (univ : Finset (Fin 7)).card := by
        have h1 : used.card ≤ (neighbors I A V v).card := card_image_le
        have h2 := neighbors_card I A hrank V v
        simpa using (show used.card < 7 by omega)
      obtain ⟨a,_,ha⟩ := exists_mem_notMem_of_card_lt_card hused
      let c' := Function.update c v a
      refine ⟨c', ?_⟩
      intro i hi x hx y hy hxV hyV hxy
      by_cases hxv : x = v
      · subst x
        have hyv : y ≠ v := hxy.symm
        have hm : c y ∈ used := mem_image.mpr
          ⟨y, mem_neighbors hi hx hy hxV hyV hyv, rfl⟩
        have hne : a ≠ c y := by intro heq; exact ha (heq ▸ hm)
        simpa [c', hyv] using hne
      · by_cases hyv : y = v
        · subst y
          have hm : c x ∈ used := mem_image.mpr
            ⟨x, mem_neighbors hi hy hx hyV hxV hxv, rfl⟩
          have hne : c x ≠ a := by intro heq; exact ha (heq ▸ hm)
          simpa [c', hxv] using hne
        · have hne := hc i hi x hx y hy (mem_erase.mpr ⟨hxv,hxV⟩)
            (mem_erase.mpr ⟨hyv,hyV⟩) hxy
          simpa [c', hxv, hyv] using hne
    · refine ⟨fun _ => 0, ?_⟩
      intro i hi x hx y hy hxV _ _
      exact (hV ⟨x,hxV⟩).elim

abbrev CutIndex := Σ _o : Fin 7, Finset (Fin 7)

def colorCuts : Finset CutIndex :=
  (univ : Finset (Fin 7)).sigma fun o => (univ.erase o).powersetCard 3

def colorCrossCount (T : Finset (Fin 7)) : Nat :=
  (colorCuts.filter fun q => CutAverage.Cross (T.erase q.1) q.2).card

theorem fixed_size_cross_count (P T : Finset α) (n : Nat)
    (hTP : T ⊆ P) (hT : T.Nonempty) (hn : T.card ≤ n) :
    ((P.powersetCard n).filter (CutAverage.Cross T)).card =
      P.card.choose n - ((P.card - T.card).choose n +
        (P.card - T.card).choose (n - T.card)) := by
  let U := (P \ T).powersetCard n
  let W := (P.powersetCard n).filter (T ⊆ ·)
  have heq : (P.powersetCard n).filter (CutAverage.Cross T) =
      P.powersetCard n \ (U ∪ W) := by
    ext L
    simp only [U, W, mem_filter, mem_powersetCard, CutAverage.Cross, mem_sdiff,
      mem_union, sdiff_nonempty, ← not_disjoint_iff_nonempty_inter, subset_sdiff]
    rw [disjoint_comm (a := T)]
    tauto
  have hsub : U ∪ W ⊆ P.powersetCard n := by
    intro L hL
    rcases mem_union.mp hL with hL | hL
    · have hh := mem_powersetCard.mp hL
      exact mem_powersetCard.mpr ⟨hh.1.trans sdiff_subset, hh.2⟩
    · exact (mem_filter.mp hL).1
  have hd : Disjoint U W := by
    apply disjoint_left.mpr
    intro L hLU hLW
    obtain ⟨t,ht⟩ := hT
    have htL := (mem_filter.mp hLW).2 ht
    have hnot := (mem_sdiff.mp ((mem_powersetCard.mp hLU).1 htL)).2
    exact hnot ht
  rw [heq, card_sdiff_of_subset hsub, card_union_of_disjoint hd]
  rw [show U.card = (P.card-T.card).choose n by
    change ((P \ T).powersetCard n).card = _
    rw [card_powersetCard, card_sdiff_of_subset hTP]]
  rw [show W.card = (P.card-T.card).choose (n-T.card) by
    exact card_filter_powersetCard_subset T P n hTP hn]
  rw [card_powersetCard]

theorem color_cut_fiber_formula (T : Finset (Fin 7)) (o : Fin 7)
    (hlo : 2 ≤ T.card) (hhi : T.card ≤ 3) :
    (((univ.erase o).powersetCard 3).filter (CutAverage.Cross (T.erase o))).card =
      20 - ((6-(T.erase o).card).choose 3 +
        (6-(T.erase o).card).choose (3-(T.erase o).card)) := by
  have hsub : T.erase o ⊆ (univ : Finset (Fin 7)).erase o := erase_subset_erase o (subset_univ T)
  have hcard : (T.erase o).card ≤ 3 := (card_erase_le).trans hhi
  have hne : (T.erase o).Nonempty := by
    apply card_pos.mp
    by_cases ho : o ∈ T
    · rw [card_erase_of_mem ho]
      omega
    · rw [erase_eq_of_notMem ho]
      omega
  rw [fixed_size_cross_count _ _ 3 hsub hne hcard]
  norm_num [Nat.choose]

theorem color_pair_count (T : Finset (Fin 7)) (hT : T.card = 2) :
    colorCrossCount T = 60 := by
  unfold colorCrossCount colorCuts
  rw [filter_sigma, card_sigma]
  have hf (o : Fin 7) :
      (((univ.erase o).powersetCard 3).filter (CutAverage.Cross (T.erase o))).card =
        if o ∈ T then 0 else 12 := by
    rw [color_cut_fiber_formula T o (by omega) (by omega)]
    by_cases ho : o ∈ T
    · rw [card_erase_of_mem ho, if_pos ho, hT]
      decide
    · rw [erase_eq_of_notMem ho, if_neg ho, hT]
      decide
  change (∑ o : Fin 7,
    (((univ.erase o).powersetCard 3).filter (CutAverage.Cross (T.erase o))).card) = 60
  simp_rw [hf]
  have hfilter : (univ : Finset (Fin 7)).filter (fun o => o ∉ T) = univ \ T := by ext o; simp
  rw [sum_ite]
  simp [hfilter, card_sdiff_of_subset (subset_univ T), hT]

theorem color_triple_count (T : Finset (Fin 7)) (hT : T.card = 3) :
    colorCrossCount T = 108 := by
  unfold colorCrossCount colorCuts
  rw [filter_sigma, card_sigma]
  have hf (o : Fin 7) :
      (((univ.erase o).powersetCard 3).filter (CutAverage.Cross (T.erase o))).card =
        if o ∈ T then 12 else 18 := by
    rw [color_cut_fiber_formula T o (by omega) (by omega)]
    by_cases ho : o ∈ T
    · rw [card_erase_of_mem ho, if_pos ho, hT]
      decide
    · rw [erase_eq_of_notMem ho, if_neg ho, hT]
      decide
  change (∑ o : Fin 7,
    (((univ.erase o).powersetCard 3).filter (CutAverage.Cross (T.erase o))).card) = 108
  simp_rw [hf]
  have hfilter : (univ : Finset (Fin 7)).filter (fun o => o ∉ T) = univ \ T := by ext o; simp
  rw [sum_ite]
  simp [hfilter, card_sdiff_of_subset (subset_univ T), hT]

theorem color_available_count (v : Fin 7) :
    (colorCuts.filter fun q => v ≠ q.1).card = 120 := by
  unfold colorCuts
  rw [filter_sigma, card_sigma]
  have hf (o : Fin 7) :
      (((univ.erase o).powersetCard 3).filter fun _ => v ≠ o).card =
        if v ≠ o then 20 else 0 := by
    by_cases ho : v ≠ o <;> simp [ho, card_powersetCard, Nat.choose]
  change (∑ o : Fin 7, (((univ.erase o).powersetCard 3).filter fun _ => v ≠ o).card) = 120
  simp_rw [hf]
  rw [← sum_filter]
  have he : (univ : Finset (Fin 7)).filter (fun o => v ≠ o) = univ.erase v := by
    ext o
    simp [ne_comm]
  simp [he]

def available (V : Finset α) (c : α → Fin 7) (q : CutIndex) : Finset α :=
  V.filter fun v => c v ≠ q.1

def cutLeft (V : Finset α) (c : α → Fin 7) (q : CutIndex) : Finset α :=
  (available V c q).filter fun v => c v ∈ q.2

theorem cross_transport (V A : Finset α) (hAV : A ⊆ V)
    (c : α → Fin 7) (q : CutIndex) :
    CutAverage.Cross (A ∩ available V c q) (cutLeft V c q) ↔
      CutAverage.Cross ((A.image c).erase q.1) q.2 := by
  constructor
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    have hxA := (mem_inter.mp (mem_inter.mp hx).1).1
    have hxS := (mem_inter.mp (mem_inter.mp hx).1).2
    have hxL := (mem_filter.mp (mem_inter.mp hx).2).2
    have hyA := (mem_inter.mp (mem_sdiff.mp hy).1).1
    have hyS := (mem_inter.mp (mem_sdiff.mp hy).1).2
    have hyL : c y ∉ q.2 := by
      intro hcy
      exact (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨hyS,hcy⟩)
    exact ⟨⟨c x, mem_inter.mpr ⟨mem_erase.mpr
      ⟨(mem_filter.mp hxS).2, mem_image_of_mem c hxA⟩, hxL⟩⟩,
      ⟨c y, mem_sdiff.mpr ⟨mem_erase.mpr
      ⟨(mem_filter.mp hyS).2, mem_image_of_mem c hyA⟩, hyL⟩⟩⟩
  · rintro ⟨⟨u,hu⟩,⟨v,hv⟩⟩
    have hu0 := mem_erase.mp (mem_inter.mp hu).1
    have hv0 := mem_erase.mp (mem_sdiff.mp hv).1
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hu0.2
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hv0.2
    have hxS : x ∈ available V c q := mem_filter.mpr ⟨hAV hx, hu0.1⟩
    have hyS : y ∈ available V c q := mem_filter.mpr ⟨hAV hy, hv0.1⟩
    refine ⟨⟨x, mem_inter.mpr ⟨mem_inter.mpr ⟨hx,hxS⟩,
      mem_filter.mpr ⟨hxS,(mem_inter.mp hu).2⟩⟩⟩,
      ⟨y, mem_sdiff.mpr ⟨mem_inter.mpr ⟨hy,hyS⟩, ?_⟩⟩⟩
    intro h
    exact (mem_sdiff.mp hv).2 (mem_filter.mp h).2

omit [DecidableEq α] in
theorem sum_available (V : Finset α) (c : α → Fin 7) :
    (∑ q ∈ colorCuts, (available V c q).card) = 120 * V.card := by
  have hd := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := colorCuts) (t := V) (fun q v => c v ≠ q.1)
  change (∑ q ∈ colorCuts, (available V c q).card) =
    ∑ v ∈ V, (colorCuts.filter fun q => c v ≠ q.1).card at hd
  rw [hd]
  simp_rw [color_available_count]
  simp [Nat.mul_comm]

def ownerCost (k : Nat) : Nat :=
  (if k = 2 then 60 else 0) + (if k = 3 then 108 else 0)

theorem color_cross_ge_cost (T : Finset (Fin 7)) :
    ownerCost T.card ≤ colorCrossCount T := by
  by_cases h2 : T.card = 2
  · rw [color_pair_count T h2]
    simp [ownerCost, h2]
  · by_cases h3 : T.card = 3
    · rw [color_triple_count T h3]
      simp [ownerCost, h3]
    · simp [ownerCost, h2, h3]

omit [DecidableEq α] in
theorem sum_ownerCost (I : Finset ι) (A : ι → Finset α) :
    (∑ i ∈ I, ownerCost (A i).card) =
      60 * (I.filter fun i => (A i).card = 2).card +
      108 * (I.filter fun i => (A i).card = 3).card := by
  unfold ownerCost
  rw [sum_add_distrib, ← sum_filter, ← sum_filter]
  simp [Nat.mul_comm]

theorem density_of_strong_seven (V : Finset α) (I : Finset ι) (A : ι → Finset α)
    (hAV : ∀ i ∈ I, A i ⊆ V) (hcap : TraceCap V I A)
    (c : α → Fin 7)
    (hc : ∀ i ∈ I, ∀ x ∈ A i, ∀ y ∈ A i, x ≠ y → c x ≠ c y) :
    5 * (I.filter fun i => (A i).card = 2).card +
      9 * (I.filter fun i => (A i).card = 3).card ≤ 10 * V.card := by
  have hd := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := colorCuts) (t := I)
    (fun q i => CutAverage.Cross (A i ∩ available V c q) (cutLeft V c q))
  change (∑ q ∈ colorCuts,
    CutAverage.ownerCount I (fun i => A i ∩ available V c q) (cutLeft V c q)) =
    ∑ i ∈ I, (colorCuts.filter fun q =>
      CutAverage.Cross (A i ∩ available V c q) (cutLeft V c q)).card at hd
  have htransport : ∀ i ∈ I, (colorCuts.filter fun q =>
      CutAverage.Cross (A i ∩ available V c q) (cutLeft V c q)).card =
      colorCrossCount ((A i).image c) := by
    intro i hi
    unfold colorCrossCount
    apply congrArg Finset.card
    apply filter_congr
    intro q _
    exact cross_transport V (A i) (hAV i hi) c q
  have hbound : (∑ i ∈ I, colorCrossCount ((A i).image c)) ≤ 120 * V.card := by
    rw [← sum_congr rfl htransport, ← hd, ← sum_available V c]
    apply sum_le_sum
    intro q hq
    exact hcap _ (filter_subset _ _) _ (filter_subset _ _)
  have hcard : ∀ i ∈ I, ((A i).image c).card = (A i).card := by
    intro i hi
    apply card_image_of_injOn
    intro x hx y hy hxy
    by_contra hn
    exact hc i hi x hx y hy hn hxy
  have hlower : (∑ i ∈ I, ownerCost (A i).card) ≤
      ∑ i ∈ I, colorCrossCount ((A i).image c) := by
    apply sum_le_sum
    intro i hi
    rw [← hcard i hi]
    exact color_cross_ge_cost _
  rw [sum_ownerCost] at hlower
  omega

theorem rank_three_local_cut_density (V : Finset α) (I : Finset ι) (A : ι → Finset α)
    (hrank : ∀ i ∈ I, (A i).card ≤ 3) (hAV : ∀ i ∈ I, A i ⊆ V)
    (hcap : TraceCap V I A) :
    5 * (I.filter fun i => (A i).card = 2).card +
      9 * (I.filter fun i => (A i).card = 3).card ≤ 10 * V.card := by
  obtain ⟨c,hc⟩ := strong_seven_coloring V I A hrank hcap
  exact density_of_strong_seven V I A hAV hcap c
    (fun i hi x hx y hy hxy => hc i hi x hx y hy (hAV i hi hx) (hAV i hi hy) hxy)

noncomputable def shrink (A : Finset α) : Finset α :=
  if h : 3 ≤ A.card then Classical.choose (exists_subset_card_eq h) else A

omit [DecidableEq α] in
theorem shrink_spec (A : Finset α) :
    shrink A ⊆ A ∧ (shrink A).card = min A.card 3 := by
  unfold shrink
  by_cases h : 3 ≤ A.card
  · rw [dif_pos h]
    have hh := Classical.choose_spec (exists_subset_card_eq h)
    exact ⟨hh.1, hh.2.trans (min_eq_right h).symm⟩
  · rw [dif_neg h]
    exact ⟨Subset.refl _, (min_eq_left (by omega)).symm⟩

theorem cross_mono {A B L : Finset α} (hAB : A ⊆ B)
    (h : CutAverage.Cross A L) : CutAverage.Cross B L := by
  rcases h with ⟨⟨a,ha⟩,⟨b,hb⟩⟩
  exact ⟨⟨a, mem_inter.mpr ⟨hAB (mem_inter.mp ha).1,(mem_inter.mp ha).2⟩⟩,
    ⟨b, mem_sdiff.mpr ⟨hAB (mem_sdiff.mp hb).1,(mem_sdiff.mp hb).2⟩⟩⟩

theorem trace_cap_mono (V : Finset α) (I : Finset ι) (A B : ι → Finset α)
    (hAB : ∀ i ∈ I, A i ⊆ B i) (hcap : TraceCap V I B) : TraceCap V I A := by
  intro S hS L hL
  apply le_trans (card_le_card ?_) (hcap S hS L hL)
  intro i hi
  have hm := mem_filter.mp hi
  exact mem_filter.mpr ⟨hm.1,
    cross_mono (fun x hx => mem_inter.mpr
      ⟨hAB i hm.1 (mem_inter.mp hx).1, (mem_inter.mp hx).2⟩) hm.2⟩

theorem local_cut_density (V : Finset α) (I : Finset ι) (A : ι → Finset α)
    (hAV : ∀ i ∈ I, A i ⊆ V) (hcap : TraceCap V I A) :
    5 * (I.filter fun i => (A i).card = 2).card +
      9 * (I.filter fun i => 3 ≤ (A i).card).card ≤ 10 * V.card := by
  let B := fun i => shrink (A i)
  have hBV : ∀ i ∈ I, B i ⊆ V := fun i hi => (shrink_spec _).1.trans (hAV i hi)
  have hrank : ∀ i ∈ I, (B i).card ≤ 3 := by
    intro i _
    rw [(shrink_spec (A i)).2]
    exact min_le_right _ _
  have hc := trace_cap_mono V I B A (fun i _ => (shrink_spec _).1) hcap
  have h := rank_three_local_cut_density V I B hrank hBV hc
  have htwo : I.filter (fun i => (B i).card = 2) = I.filter (fun i => (A i).card = 2) := by
    apply filter_congr
    intro i hi
    rw [(shrink_spec (A i)).2]
    omega
  have hthree : I.filter (fun i => (B i).card = 3) = I.filter (fun i => 3 ≤ (A i).card) := by
    apply filter_congr
    intro i hi
    rw [(shrink_spec (A i)).2]
    omega
  rwa [htwo,hthree] at h

end D5.S3.Combinatorics.Graph.RankThreeLocalCutDensity
