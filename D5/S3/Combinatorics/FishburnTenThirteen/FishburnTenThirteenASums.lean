/- GID: D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenASums
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenASums
   mirror-E: none(waiver:interval-component-site-analysis)
   anchors: []
   utility: none
   digest: Earlier sum blocks allow only separated cuts while the final block keeps its sites. -/

import D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenSites
import D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicSum
import D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicComponentCuts

open D5.S3.Combinatorics.Fishburn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenASums

open FishburnBasicComponents FishburnBasicComponentCuts

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnTenThirteenSites
open NonnestingBasicSum

theorem interval_sum_sites (m n : ℕ) (left right : List ℕ) (hn : 0 < n)
    (hleft : left.Perm (List.range' 1 m))
    (hright : right ∈ avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]])
    (hparent : directSum m left right ∈
      avoiders (m + n) [[2, 4, 1, 3], [2, 4, 3, 1]]) :
    (∀ site, site ≤ left.length →
      ((directSum m left right).insertIdx site (m + n + 1) ∈
          avoiders (m + n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] ↔
        ∀ a ∈ left.take site, ∀ b ∈ left.drop site, a < b)) ∧
    (∀ site, site ≤ right.length →
      ((directSum m left right).insertIdx (left.length + site) (m + n + 1) ∈
          avoiders (m + n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] ↔
        right.insertIdx site (n + 1) ∈
          avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]])) ∧
    (sumIndecomposable right → ∀ site, 0 < site → site ≤ right.length →
      right.insertIdx site (n + 1) ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] →
        n ∈ right.take site)∧
   (∀ parts : List (List ℕ),
     (∀ block ∈ parts, block ≠ [] ∧
       block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) →
     assemble parts = left →
     let rightCuts := @Finset.filter ℕ (fun gap =>
       right.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]])
       (fun _ => Classical.propDecidable _) (Finset.range (right.length + 1))
     let whole := directSum m left right
     let wholeCuts := @Finset.filter ℕ (fun gap =>
       whole.insertIdx gap (m + n + 1) ∈
         avoiders (m + n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]])
       (fun _ => Classical.propDecidable _) (Finset.range (whole.length + 1))
     wholeCuts.card = parts.length + rightCuts.card) := by
  let word := directSum m left right
  have hleftlen : left.length = m := by
    simpa using hleft.length_eq
  have hrightlen : right.length = n := by
    simpa using hright.1.length_eq
  have hlength : word.length = left.length + right.length := by
    simp [word, directSum, shift]
  have hvalues (size : ℕ) (block : List ℕ) (hp : block.Perm (List.range' 1 size))
      (value : ℕ) (hv : value ∈ block) : 1 ≤ value ∧ value ≤ size := by
    have hm := hp.mem_iff.mp hv
    simp only [List.mem_range', Nat.one_mul] at hm
    obtain ⟨index, hi, heq⟩ := hm
    omega
  have hbefore (index : ℕ) (hi : index < left.length) :
      word.getD index 0 = left.getD index 0 :=
    List.getD_append _ _ _ _ hi
  have hafter (index : ℕ) (hi : left.length ≤ index) (hb : index < word.length) :
      word.getD index 0 = right.getD (index - left.length) 0 + m := by
    change (left ++ shift m right).getD index 0 = _
    rw [List.getD_append_right _ _ _ _ hi]
    have hindex : index - left.length < right.length := by omega
    rw [List.getD_eq_getElem _ 0 (by simpa [shift] using hindex),
      List.getD_eq_getElem right 0 hindex]
    simp [shift]
  have hdisjoint (site : ℕ) :
      ∀ a ∈ word.take site, ∀ b ∈ word.drop site, a ≠ b := by
    have hnd := hparent.1.nodup_iff.mpr (List.nodup_range' 1)
    have happ : (word.take site ++ word.drop site).Nodup := by simpa using hnd
    exact (List.nodup_append.mp happ).2.2
  have hprefix (site index : ℕ) (hi : index < site) (hb : index < word.length) :
      word.getD index 0 ∈ word.take site := by
    apply List.mem_take_iff_getElem.mpr
    exact ⟨index, by omega, (List.getD_eq_getElem word 0 hb).symm⟩
  have hsuffix (site index : ℕ) (hi : site ≤ index) (hb : index < word.length) :
      word.getD index 0 ∈ word.drop site := by
    apply List.mem_drop_iff_getElem.mpr
    refine ⟨index - site, by omega, ?_⟩
    have heq : site + (index - site) = index := by omega
    simpa only [heq] using (List.getD_eq_getElem word 0 hb).symm
  have hshiftinterval (block : List ℕ) :
      Set.OrdConnected {value : ℕ | value ∈ shift m block} ↔
        Set.OrdConnected {value : ℕ | value ∈ block} := by
    constructor
    · intro hconn
      constructor
      intro low hlo high hhi middle hbetween
      have hm : middle + m ∈ shift m block := hconn.out
        (List.mem_map.mpr ⟨low, hlo, rfl⟩)
        (List.mem_map.mpr ⟨high, hhi, rfl⟩)
        ⟨Nat.add_le_add_right hbetween.1 m, Nat.add_le_add_right hbetween.2 m⟩
      obtain ⟨value, hv, heq⟩ := List.mem_map.mp hm
      have hequal : value = middle := by omega
      simpa [hequal] using hv
    · intro hconn
      constructor
      intro low hlo high hhi middle hbetween
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hlo
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hhi
      have hbounds : a + m ≤ middle ∧ middle ≤ b + m := hbetween
      have hm : middle - m ∈ block := hconn.out ha hb ⟨by omega, by omega⟩
      exact List.mem_map.mpr ⟨middle - m, hm, by omega⟩
  have hsites :
    (∀ site, site ≤ left.length →
      ((directSum m left right).insertIdx site (m + n + 1) ∈
          avoiders (m + n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] ↔
        ∀ a ∈ left.take site, ∀ b ∈ left.drop site, a < b)) ∧
    (∀ site, site ≤ right.length →
      ((directSum m left right).insertIdx (left.length + site) (m + n + 1) ∈
          avoiders (m + n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] ↔
        right.insertIdx site (n + 1) ∈
          avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]])) ∧
    (sumIndecomposable right → ∀ site, 0 < site → site ≤ right.length →
      right.insertIdx site (n + 1) ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] →
        n ∈ right.take site) := by
    refine ⟨?_, ?_, ?_⟩
    · intro site hsite
      have ht : word.take site = left.take site :=
        List.take_append_of_le_length hsite
      have hd : word.drop site = left.drop site ++ shift m right := by
        change (left ++ shift m right).drop site = _
        rw [List.drop_append_of_le_length hsite]
      have hmaximum : m + n ∈ word.drop site := by
        rw [hd]
        apply List.mem_append.mpr
        right
        apply List.mem_map.mpr
        refine ⟨n, ?_, by omega⟩
        apply hright.1.mem_iff.mpr
        simp only [List.mem_range', Nat.one_mul]
        exact ⟨n - 1, by omega, by omega⟩
      have hseparation :
          (∀ a ∈ word.take site, ∀ b ∈ word.drop site, a < b) ↔
            ∀ a ∈ left.take site, ∀ b ∈ left.drop site, a < b := by
        rw [ht, hd]
        constructor
        · intro hsep a ha b hb
          exact hsep a ha b (List.mem_append_left _ hb)
        · intro hsep a ha b hb
          rcases List.mem_append.mp hb with hleftb | hrightb
          · exact hsep a ha b hleftb
          · obtain ⟨value, hv, rfl⟩ := List.mem_map.mp hrightb
            have := (hvalues m left hleft a ((List.take_sublist site left).subset ha)).2
            have := (hvalues n right hright.1 value hv).1
            omega
      rw [← hseparation]
      constructor
      · intro hactive a ha b hb
        by_contra hnot
        have haLeft : a ∈ left := (List.take_sublist site left).subset (ht ▸ ha)
        have haBound := (hvalues m left hleft a haLeft).2
        have hne := hdisjoint site a ha b hb
        have hstrict : b < a ∧ a < m + n := by omega
        obtain ⟨first, hf, hfirst⟩ := List.mem_take_iff_getElem.mp ha
        obtain ⟨smallIndex, hsmallIndex, hsmallValue⟩ := List.mem_drop_iff_getElem.mp hb
        obtain ⟨topIndex, htopIndex, htopValue⟩ :=
          List.mem_drop_iff_getElem.mp hmaximum
        have hfirstD : word.getD first 0 = a :=
          (List.getD_eq_getElem word 0 (by omega)).trans hfirst
        have hsmallD : word.getD (site + smallIndex) 0 = b :=
          (List.getD_eq_getElem word 0 (by omega)).trans hsmallValue
        have htopD : word.getD (site + topIndex) 0 = m + n :=
          (List.getD_eq_getElem word 0 (by omega)).trans htopValue
        have htests := FishburnBasicTenThirteenPatterns.maximum_crossing_pattern_tests
          (m + n) word hparent.1 site (by omega)
        by_cases horder : smallIndex < topIndex
        · apply hactive.2.2 [2, 4, 1, 3] (by simp)
          apply htests.1.mpr
          right
          refine ⟨first, site + smallIndex, site + topIndex,
            by omega, by omega, by omega, by omega, ?_, ?_⟩
          · rw [hsmallD, hfirstD]
            exact hstrict.1
          · rw [hfirstD, htopD]
            exact hstrict.2
        · have hdistinct : smallIndex ≠ topIndex := by
            intro heq
            rw [heq] at hsmallD
            omega
          apply hactive.2.2 [2, 4, 3, 1] (by simp)
          apply htests.2.mpr
          right
          refine ⟨first, site + topIndex, site + smallIndex,
            by omega, by omega, by omega, by omega, ?_, ?_⟩
          · rw [hsmallD, hfirstD]
            exact hstrict.1
          · rw [hfirstD, htopD]
            exact hstrict.2
      · intro hsep
        apply (interval_active_sites (m + n) word hparent site (by omega)).mpr
        constructor
        · intro before later hbeforeSite hlater hbound heq
          have := hsep _ (hprefix site before (by omega) (by omega))
            _ (hsuffix site later hlater hbound)
          omega
        · constructor
          intro low hlo high hhi middle hbetween
          have hlov := hvalues (m + n) word hparent.1 low
            ((List.drop_sublist site word).subset hlo)
          have hhiv := hvalues (m + n) word hparent.1 high
            ((List.drop_sublist site word).subset hhi)
          have hbounds : low ≤ middle ∧ middle ≤ high := hbetween
          have hm : middle ∈ word := by
            apply hparent.1.mem_iff.mpr
            simp only [List.mem_range', Nat.one_mul]
            exact ⟨middle - 1, by omega, by omega⟩
          have happ : middle ∈ word.take site ++ word.drop site := by simpa using hm
          rcases List.mem_append.mp happ with hpref | hsuf
          · have := hsep middle hpref low hlo
            omega
          · exact hsuf
    · intro site hsite
      have hd : word.drop (left.length + site) = shift m (right.drop site) := by
        simp [word, directSum, shift, List.drop_append]
      have heligible :
          (∀ before later, before + 1 = left.length + site →
            left.length + site ≤ later → later < word.length →
            word.getD before 0 ≠ word.getD later 0 + 1) ↔
          (∀ before later, before + 1 = site → site ≤ later → later < right.length →
            right.getD before 0 ≠ right.getD later 0 + 1) := by
        constructor
        · intro he before later hb hl hbound hbad
          apply he (left.length + before) (left.length + later) (by omega) (by omega)
            (by omega)
          rw [hafter (left.length + before) (by omega) (by omega),
            hafter (left.length + later) (by omega) (by omega)]
          simp only [Nat.add_sub_cancel_left]
          omega
        · intro he before later hb hl hbound hbad
          by_cases hbefLeft : before < left.length
          · have hsmall := (hvalues m left hleft (left.getD before 0) (by
              rw [List.getD_eq_getElem left 0 hbefLeft]
              exact List.getElem_mem hbefLeft)).2
            have hlarge := (hvalues n right hright.1
              (right.getD (later - left.length) 0) (by
                rw [List.getD_eq_getElem right 0 (by omega)]
                exact List.getElem_mem (by omega))).1
            rw [hbefore before hbefLeft, hafter later (by omega) hbound] at hbad
            omega
          · apply he (before - left.length) (later - left.length) (by omega) (by omega)
              (by omega)
            rw [hafter before (by omega) (by omega),
              hafter later (by omega) hbound] at hbad
            omega
      rw [interval_active_sites (m + n) word hparent (left.length + site) (by omega),
        interval_active_sites n right hright site hsite, hd, hshiftinterval, heligible]
    · intro hindec site hpositive hsite hactive
      have hmax : n ∈ right := by
        apply hright.1.mem_iff.mpr
        simp only [List.mem_range', Nat.one_mul]
        exact ⟨n - 1, by omega, by omega⟩
      by_contra hmissing
      have hsuffix : n ∈ right.drop site := by
        have happ : n ∈ right.take site ++ right.drop site := by simpa using hmax
        exact (List.mem_append.mp happ).resolve_left hmissing
      have hproper : site < right.length := by
        by_contra hnot
        have heq : site = right.length := by omega
        simp [heq] at hsuffix
      obtain ⟨before, later, hinversion⟩ := hindec ⟨site, hproper⟩ hpositive
      have ha : (right.take site).get before ∈ right.take site := List.get_mem _ before
      have hb : (right.drop site).get later ∈ right.drop site := List.get_mem _ later
      have hbound : (right.take site).get before ≤ n :=
        (hvalues n right hright.1 _ ((List.take_sublist site right).subset ha)).2
      have hconn := (interval_active_sites n right hright site hsite).mp hactive |>.2
      have hm : (right.take site).get before ∈ right.drop site :=
        hconn.out hb hsuffix ⟨hinversion, hbound⟩
      have hnd := hright.1.nodup_iff.mpr (List.nodup_range' 1)
      have happ : (right.take site ++ right.drop site).Nodup := by simpa using hnd
      exact (List.nodup_append.mp happ).2.2 _ ha _ hm rfl
  refine ⟨hsites.1, hsites.2.1, hsites.2.2, ?_⟩
  intro parts hparts heq
  classical
  dsimp only
  let boundaries := @Finset.filter ℕ (fun gap =>
    ∀ before ∈ left.take gap, ∀ later ∈ left.drop gap, before < later)
    (fun _ => Classical.propDecidable _) (Finset.range (left.length + 1))
  let rightCuts := (Finset.range (right.length + 1)).filter fun gap =>
    right.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]]
  let wholeCuts := (Finset.range (word.length + 1)).filter fun gap =>
    word.insertIdx gap (m + n + 1) ∈
      avoiders (m + n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]]
  change wholeCuts.card = parts.length + rightCuts.card
  have hboundaryCount : boundaries.card = parts.length + 1 := by
    dsimp only [boundaries]
    rw [← heq]
    exact component_boundary_count parts hparts
  have hboundary (gap : ℕ) : gap ∈ boundaries ↔ gap ≤ left.length ∧
      ∀ before ∈ left.take gap, ∀ later ∈ left.drop gap, before < later := by
    simp only [boundaries, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  have hrightCut (gap : ℕ) : gap ∈ rightCuts ↔ gap ≤ right.length ∧
      right.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] := by
    simp only [rightCuts, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  have hwholeCut (gap : ℕ) : gap ∈ wholeCuts ↔ gap ≤ word.length ∧
      word.insertIdx gap (m + n + 1) ∈
        avoiders (m + n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] := by
    simp only [wholeCuts, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  have hdecomp : wholeCuts = boundaries.erase left.length ∪
      rightCuts.image (left.length + ·) := by
    ext gap
    constructor
    · intro hg
      obtain ⟨hb, ha⟩ := (hwholeCut gap).mp hg
      by_cases hlocal : gap < left.length
      · apply Finset.mem_union_left
        apply Finset.mem_erase.mpr
        exact ⟨by omega, (hboundary gap).mpr
          ⟨by omega, (hsites.1 gap (by omega)).mp ha⟩⟩
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        have hprevBound : gap - left.length ≤ right.length := by omega
        have hprev : right.insertIdx (gap - left.length) (n + 1) ∈
            avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] := by
          apply (hsites.2.1 (gap - left.length) hprevBound).mp
          simpa only [Nat.add_sub_cancel' (by omega : left.length ≤ gap)] using ha
        exact ⟨gap - left.length, (hrightCut _).mpr ⟨hprevBound, hprev⟩, by omega⟩
    · intro hg
      rcases Finset.mem_union.mp hg with hleftGap | him
      · obtain ⟨hne, hg⟩ := Finset.mem_erase.mp hleftGap
        obtain ⟨hb, hsep⟩ := (hboundary gap).mp hg
        exact (hwholeCut gap).mpr ⟨by omega, (hsites.1 gap hb).mpr hsep⟩
      · obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp him
        obtain ⟨hb, ha⟩ := (hrightCut old).mp hold
        exact (hwholeCut _).mpr ⟨by omega, (hsites.2.1 old hb).mpr ha⟩
  have hdisjoint : Disjoint (boundaries.erase left.length)
      (rightCuts.image (left.length + ·)) := by
    apply Finset.disjoint_left.mpr
    intro gap hb him
    obtain ⟨hne, hb⟩ := Finset.mem_erase.mp hb
    have hbound := (hboundary gap).mp hb |>.1
    obtain ⟨old, _, heq⟩ := Finset.mem_image.mp him
    omega
  have himage : (rightCuts.image (left.length + ·)).card = rightCuts.card :=
    Finset.card_image_of_injective _ (fun _ _ heq => Nat.add_left_cancel heq)
  have hfinal : left.length ∈ boundaries := by
    apply (hboundary _).mpr
    exact ⟨le_rfl, by simp⟩
  have herase := Finset.card_erase_add_one hfinal
  rw [hdecomp, Finset.card_union_of_disjoint hdisjoint, himage]
  omega

end D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenASums
