/- GID: D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBSums
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBSums
   mirror-E: none(waiver:crossing-component-site-localization)
   anchors: []
   utility: none
   digest: Both crossing obstructions at a direct-sum cut belong to its local block. -/

import D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicTenThirteenPatterns
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum

open D5.S3.Combinatorics.Fishburn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenBSums

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasicFourPatterns FishburnBasicTenThirteenPatterns NonnestingBasicSum

theorem crossing_sum_sites (m n : ℕ) (left right : List ℕ)
    (hleft : left ∈ avoiders m [[2, 4, 3, 1], [3, 2, 4, 1]])
    (hright : right ∈ avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]])
    (hparent : directSum m left right ∈
      avoiders (m + n) [[2, 4, 3, 1], [3, 2, 4, 1]]) :
    (∀ site, site ≤ left.length →
      ((directSum m left right).insertIdx site (m + n + 1) ∈
          avoiders (m + n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] ↔
        left.insertIdx site (m + 1) ∈ avoiders (m + 1) [[2, 4, 3, 1], [3, 2, 4, 1]])) ∧
    (∀ site, site ≤ right.length →
      ((directSum m left right).insertIdx (left.length + site) (m + n + 1) ∈
          avoiders (m + n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] ↔
        right.insertIdx site (n + 1) ∈ avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]])) ∧
    (∀ maximum site, (directSum m left right).getD maximum 0 = m + n →
      maximum < site → site ≤ (directSum m left right).length →
      (directSum m left right).insertIdx site (m + n + 1) ∈
        avoiders (m + n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] →
      ∀ middle later, maximum < middle → middle < site → site ≤ later →
        later < (directSum m left right).length →
        (directSum m left right).getD middle 0 < (directSum m left right).getD later 0) := by
  let eligible (block : List ℕ) (site : ℕ) : Prop :=
    ∀ before later, before + 1 = site → site ≤ later → later < block.length →
      block.getD before 0 ≠ block.getD later 0 + 1
  let guard243 (block : List ℕ) (site : ℕ) : Prop :=
    ∃ first second third, first < site ∧ site ≤ second ∧ second < third ∧
      third < block.length ∧ block.getD third 0 < block.getD first 0 ∧
      block.getD first 0 < block.getD second 0
  let guard324 (block : List ℕ) (site : ℕ) : Prop :=
    ∃ first second third, first < second ∧ second < site ∧ site ≤ third ∧
      third < block.length ∧ block.getD third 0 < block.getD second 0 ∧
      block.getD second 0 < block.getD first 0
  have hvalues (size : ℕ) (block : List ℕ) (hp : block.Perm (List.range' 1 size))
      (value : ℕ) (hv : value ∈ block) : 1 ≤ value ∧ value ≤ size := by
    have hm := hp.mem_iff.mp hv
    simp only [List.mem_range', Nat.one_mul] at hm
    obtain ⟨index, hi, heq⟩ := hm
    omega
  have htest (size : ℕ) (block : List ℕ)
      (hp : block ∈ avoiders size [[2, 4, 3, 1], [3, 2, 4, 1]])
      (site : ℕ) (hs : site ≤ block.length) :
      block.insertIdx site (size + 1) ∈
          avoiders (size + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] ↔
        eligible block site ∧ ¬ guard243 block site ∧ ¬ guard324 block site := by
    have hmax : ∀ value ∈ block, value < size + 1 := by
      intro value hv
      have := (hvalues size block hp.1 value hv).2
      omega
    have h243 := (maximum_crossing_pattern_tests size block hp.1 site hs).2
    have h324 := (maximum_four_pattern_tests size block hp.1 site hs).2.2
    have hperm : (block.insertIdx site (size + 1)).Perm
        (List.range' 1 (size + 1)) := by
      apply (List.perm_insertIdx (size + 1) block hs).trans
      apply (hp.1.cons (size + 1)).trans
      rw [List.range'_concat]
      simpa [Nat.add_comm] using
        (List.perm_append_comm (l₁ := [size + 1]) (l₂ := List.range' 1 size))
    constructor
    · intro hc
      refine ⟨(isFishburn_insertIdx_max_iff block (size + 1) site hs hmax).mp hc.2.1
        |>.2, ?_, ?_⟩
      · intro hbad
        exact hc.2.2 _ (by simp) (h243.mpr (Or.inr hbad))
      · intro hbad
        exact hc.2.2 _ (by simp) (h324.mpr (Or.inr hbad))
    · rintro ⟨he, hno243, hno324⟩
      refine ⟨hperm,
        (isFishburn_insertIdx_max_iff block (size + 1) site hs hmax).mpr ⟨hp.2.1, he⟩,
        ?_⟩
      intro pattern hpattern hbad
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl
      · exact (h243.mp hbad).elim (hp.2.2 _ (by simp)) hno243
      · exact (h324.mp hbad).elim (hp.2.2 _ (by simp)) hno324
  let word := directSum m left right
  have hlength : word.length = left.length + right.length := by
    simp [word, directSum, shift]
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
  have hsmall (index : ℕ) (hi : index < left.length) : word.getD index 0 ≤ m := by
    rw [hbefore index hi]
    apply (hvalues m left hleft.1 _ _).2
    rw [List.getD_eq_getElem left 0 hi]
    exact List.getElem_mem hi
  have hlarge (index : ℕ) (hi : left.length ≤ index) (hb : index < word.length) :
      m < word.getD index 0 := by
    have hpositive := (hvalues n right hright.1 (right.getD (index - left.length) 0)
      (by
        rw [List.getD_eq_getElem right 0 (by omega)]
        exact List.getElem_mem (by omega))).1
    rw [hafter index hi hb]
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro site hsite
    have he : eligible word site ↔ eligible left site := by
      constructor
      · intro he before later hb hl hbound hbad
        apply he before later hb hl (by omega)
        simpa only [hbefore before (by omega), hbefore later hbound] using hbad
      · intro he before later hb hl hbound hbad
        by_cases hlater : later < left.length
        · apply he before later hb hl hlater
          simpa only [hbefore before (by omega), hbefore later hlater] using hbad
        · have := hsmall before (by omega)
          have := hlarge later (by omega) hbound
          omega
    have hg243 : guard243 word site ↔ guard243 left site := by
      constructor
      · rintro ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩
        have htleft : third < left.length := by
          by_contra hnot
          have := hsmall first (by omega)
          have := hlarge third (by omega) ht
          omega
        refine ⟨first, second, third, hf, hs, hst, htleft, ?_, ?_⟩
        · simpa only [hbefore third htleft, hbefore first (by omega)] using hlow
        · simpa only [hbefore first (by omega), hbefore second (by omega)] using hhigh
      · rintro ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩
        refine ⟨first, second, third, hf, hs, hst, by omega, ?_, ?_⟩
        · simpa only [hbefore third ht, hbefore first (by omega)] using hlow
        · simpa only [hbefore first (by omega), hbefore second (by omega)] using hhigh
    have hg324 : guard324 word site ↔ guard324 left site := by
      constructor
      · rintro ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩
        have htleft : third < left.length := by
          by_contra hnot
          have := hsmall second (by omega)
          have := hlarge third (by omega) ht
          omega
        refine ⟨first, second, third, hf, hs, hst, htleft, ?_, ?_⟩
        · simpa only [hbefore third htleft, hbefore second (by omega)] using hlow
        · simpa only [hbefore second (by omega), hbefore first (by omega)] using hhigh
      · rintro ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩
        refine ⟨first, second, third, hf, hs, hst, by omega, ?_, ?_⟩
        · simpa only [hbefore third ht, hbefore second (by omega)] using hlow
        · simpa only [hbefore second (by omega), hbefore first (by omega)] using hhigh
    rw [htest (m + n) word hparent site (by omega), htest m left hleft site hsite,
      he, hg243, hg324]
  · intro site hsite
    have he : eligible word (left.length + site) ↔ eligible right site := by
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
        · have := hsmall before hbefLeft
          have := hlarge later (by omega) hbound
          omega
        · apply he (before - left.length) (later - left.length) (by omega) (by omega)
            (by omega)
          rw [hafter before (by omega) (by omega), hafter later (by omega) hbound] at hbad
          omega
    have hg243 : guard243 word (left.length + site) ↔ guard243 right site := by
      constructor
      · rintro ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩
        have hfright : left.length ≤ first := by
          by_contra hnot
          have := hsmall first (by omega)
          have := hlarge third (by omega) ht
          omega
        refine ⟨first - left.length, second - left.length, third - left.length,
          by omega, by omega, by omega, by omega, ?_, ?_⟩
        · rw [hafter third (by omega) ht, hafter first hfright (by omega)] at hlow
          omega
        · rw [hafter first hfright (by omega), hafter second (by omega) (by omega)]
            at hhigh
          omega
      · rintro ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩
        refine ⟨left.length + first, left.length + second, left.length + third,
          by omega, by omega, by omega, by omega, ?_, ?_⟩
        · rw [hafter (left.length + third) (by omega) (by omega),
            hafter (left.length + first) (by omega) (by omega)]
          simp only [Nat.add_sub_cancel_left]
          omega
        · rw [hafter (left.length + first) (by omega) (by omega),
            hafter (left.length + second) (by omega) (by omega)]
          simp only [Nat.add_sub_cancel_left]
          omega
    have hg324 : guard324 word (left.length + site) ↔ guard324 right site := by
      constructor
      · rintro ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩
        have hsright : left.length ≤ second := by
          by_contra hnot
          have := hsmall second (by omega)
          have := hlarge third (by omega) ht
          omega
        have hfright : left.length ≤ first := by
          by_contra hnot
          have := hsmall first (by omega)
          have := hlarge second hsright (by omega)
          omega
        refine ⟨first - left.length, second - left.length, third - left.length,
          by omega, by omega, by omega, by omega, ?_, ?_⟩
        · rw [hafter third (by omega) ht, hafter second hsright (by omega)] at hlow
          omega
        · rw [hafter second hsright (by omega), hafter first hfright (by omega)] at hhigh
          omega
      · rintro ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩
        refine ⟨left.length + first, left.length + second, left.length + third,
          by omega, by omega, by omega, by omega, ?_, ?_⟩
        · rw [hafter (left.length + third) (by omega) (by omega),
            hafter (left.length + second) (by omega) (by omega)]
          simp only [Nat.add_sub_cancel_left]
          omega
        · rw [hafter (left.length + second) (by omega) (by omega),
            hafter (left.length + first) (by omega) (by omega)]
          simp only [Nat.add_sub_cancel_left]
          omega
    rw [htest (m + n) word hparent (left.length + site) (by omega),
      htest n right hright site hsite, he, hg243, hg324]
  · intro maximum site hmaximum hmaxsite hsite hactive
    change word.getD maximum 0 = m + n at hmaximum
    change site ≤ word.length at hsite
    have hnd := hparent.1.nodup_iff.mpr (List.nodup_range' 1)
    change word.Nodup at hnd
    have hbound (index : ℕ) (hi : index < word.length) : word.getD index 0 ≤ m + n := by
      apply (hvalues (m + n) word hparent.1 _ _).2
      rw [List.getD_eq_getElem word 0 hi]
      exact List.getElem_mem hi
    intro middle later hmiddle hmidsite hlater hboundlater
    change later < word.length at hboundlater
    change word.getD middle 0 < word.getD later 0
    by_contra hnot
    have hdistinct : word.getD later 0 ≠ word.getD middle 0 := by
      intro heq
      have := (List.getD_inj hboundlater (by omega) hnd).mp heq
      omega
    have hdistinctmax : word.getD middle 0 ≠ m + n := by
      intro heq
      have := (List.getD_inj (by omega) (by omega) hnd).mp (heq.trans hmaximum.symm)
      omega
    have hmvalue := hbound middle (by omega)
    have hbad : NonnestingDefs.Occurs [3, 2, 4, 1]
        (word.insertIdx site (m + n + 1)) := by
      apply (maximum_four_pattern_tests (m + n) word hparent.1 site hsite).2.2.mpr
      right
      exact ⟨maximum, middle, later, hmiddle, hmidsite, hlater, hboundlater,
        by omega, by omega⟩
    exact hactive.2.2 _ (by simp) hbad

end D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenBSums
