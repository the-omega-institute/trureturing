/- GID: D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBStructure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBStructure
   mirror-E: none(waiver:reversible-interval-normal-forms)
   anchors: [mathlib/module/Mathlib.Data.List.Sort]
   utility: none
   digest: Crossing patterns force the two interval normal forms of the second class. -/

import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenAuxiliary
import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenMinimum
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenBStructure

open D5.S3.Combinatorics Nonnesting Fishburn.FishburnDefs
open Fishburn.FishburnBasicPrefixes
open FishburnTenSevenAuxiliary FishburnTenSevenMinimum

set_option maxHeartbeats 2400000 in
theorem B_interval_normalForm (n : ℕ) (p : List ℕ) (hn : 1 ≤ n)
    (hp : p ∈ avoiders n [[1, 3, 2, 4], [2, 1, 4, 3], [3, 1, 2, 4]]) :
    ∃ m, 1 ≤ m ∧ m ≤ n ∧
      ((∃ s : ↥(avoiders m [[2, 1, 3]]), s.val.head? = some 1 ∧
          p = (List.range' (m + 1) (n - m)).reverse ++ s.val) ∨
        ∃ d h, 2 ≤ d ∧ d ≤ h ∧ h < m ∧ ∃ q : ↥(avoiders (d - 2) [[2, 1, 3]]),
          p = (List.range' (m + 1) (n - m)).reverse ++
            (List.range' d (h + 1 - d)).reverse ++
              1 :: (List.range' (h + 1) (m - h - 1) ++ m :: q.val.map (· + 1))) := by
  classical
  obtain ⟨hperm, hfish, havoid⟩ := hp
  have h1324 := havoid [1, 3, 2, 4] (by simp)
  have h2143 := havoid [2, 1, 4, 3] (by simp)
  have h3124 := havoid [3, 1, 2, 4] (by simp)
  have hnodup : p.Nodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
  have hvalues : ∀ value, value ∈ p ↔ 1 ≤ value ∧ value ≤ n := by
    intro value
    rw [hperm.mem_iff]
    simp only [List.mem_range'_1]
    omega
  obtain ⟨before, tail, heq⟩ := List.mem_iff_append.mp ((hvalues 1).mpr (by omega))
  subst p
  let suffix := 1 :: tail
  have hsuffix : suffix.Sublist (before ++ suffix) := List.sublist_append_right _ _
  have hbefore : before.Sublist (before ++ suffix) := List.sublist_append_left _ _
  have hbeforeN := hnodup.sublist hbefore
  have hsuffixN := hnodup.sublist hsuffix
  have honebound : before.length < (before ++ suffix).length := by simp [suffix]
  have hone : (before ++ suffix).getD before.length 0 = 1 := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [suffix]
  have hdec := prefix_through_one_decreasing n (before ++ suffix) hperm hfish
    before.length honebound hone
  have hbeforeDec : before.Pairwise (· > ·) := by
    apply List.pairwise_iff_getElem.mpr
    intro first second hfirst hsecond hlt
    have ht := hdec first second hlt (by omega)
    change (before ++ suffix).getD second 0 < (before ++ suffix).getD first 0 at ht
    rw [List.getD_append before suffix 0 second hsecond,
      List.getD_append before suffix 0 first hfirst,
      List.getD_eq_getElem _ _ hfirst, List.getD_eq_getElem _ _ hsecond] at ht
    exact ht
  have hafter (index : ℕ) :
      (before ++ suffix).getD (before.length + index) 0 = suffix.getD index 0 := by
    rw [List.getD_append_right before suffix 0 _ (by omega), Nat.add_sub_cancel_left]
  have htests := minimum_pattern_tests n (before ++ suffix) hperm hfish
    before.length honebound hone
  have htail213 : ¬ NonnestingDefs.Occurs [2, 1, 3] suffix := by
    change ¬ ArrowWilfDefs.Contains [2, 1, 3] [] 3 suffix
    rintro ⟨values, hstep, _, hsub, _⟩
    obtain ⟨positions, hembed⟩ :=
      List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    let first := positions ⟨0, by simp⟩
    let second := positions ⟨1, by simp⟩
    let third := positions ⟨2, by simp⟩
    have h12 : first.val < second.val :=
      positions.strictMono (by change (0 : ℕ) < 1; omega)
    have h23 : second.val < third.val :=
      positions.strictMono (by change (1 : ℕ) < 2; omega)
    have hfirst : suffix.getD first.val 0 = values 2 := by
      simpa [first, List.getD_eq_getElem] using (hembed ⟨0, by simp⟩).symm
    have hsecond : suffix.getD second.val 0 = values 1 := by
      simpa [second, List.getD_eq_getElem] using (hembed ⟨1, by simp⟩).symm
    have hthird : suffix.getD third.val 0 = values 3 := by
      simpa [third, List.getD_eq_getElem] using (hembed ⟨2, by simp⟩).symm
    have hpos : 1 ≤ values 1 :=
      ((hvalues (values 1)).mp (hsuffix.subset (hsub.subset (by simp)))).1
    have hf : 0 < first.val := by
      by_contra hnot
      have hz : first.val = 0 := by omega
      have hlt : values 1 < values 2 := hstep 1 (by omega) (by omega)
      rw [hz] at hfirst
      change 1 = values 2 at hfirst
      omega
    apply h1324
    apply htests.1.mpr
    refine ⟨before.length + first.val, before.length + second.val,
      before.length + third.val, by omega, by omega, by omega, by
        simpa only [List.length_append] using Nat.add_lt_add_left third.isLt before.length,
      ?_, ?_⟩
    · rw [hafter, hafter, hsecond, hfirst]
      exact hstep 1 (by omega) (by omega)
    · rw [hafter, hafter, hfirst, hthird]
      exact hstep 2 (by omega) (by omega)
  have hsuffixFish : IsFishburn suffix := by
    intro first later hgap hlater hbad
    apply hfish (before.length + first) (before.length + later) (by omega)
      (by simpa only [List.length_append] using Nat.add_lt_add_left hlater before.length)
    change (before ++ suffix).getD (before.length + first) 0 =
      (before ++ suffix).getD (before.length + later) 0 + 1 ∧
      (before ++ suffix).getD (before.length + later) 0 + 1 <
        (before ++ suffix).getD (before.length + first + 1) 0
    rw [show before.length + first + 1 = before.length + (first + 1) by omega,
      hafter, hafter, hafter]
    exact hbad
  have hsNonempty : suffix.toFinset.Nonempty := ⟨1, by simp [suffix]⟩
  let m := suffix.toFinset.max' hsNonempty
  have hmMem : m ∈ suffix := List.mem_toFinset.mp (Finset.max'_mem _ _)
  have hm : 1 ≤ m ∧ m ≤ n := (hvalues m).mp (hsuffix.subset hmMem)
  have hmax : ∀ value ∈ suffix, value ≤ m := by
    intro value hv
    exact Finset.le_max' _ _ (List.mem_toFinset.mpr hv)
  let low := before.toFinset.filter (· < m)
  have hlow : ∀ value, value ∈ low ↔ value ∈ before ∧ value < m := by
    simp [low]
  have hnotOne : 1 ∉ before := by
    intro hmem
    have hd := (List.nodup_append.mp hnodup).2.2
    exact hd 1 hmem 1 (by simp) rfl
  have hbeforePositive : ∀ value ∈ before, 2 ≤ value := by
    intro value hv
    have := ((hvalues value).mp (hbefore.subset hv)).1
    have : value ≠ 1 := fun he => hnotOne (he ▸ hv)
    omega
  have hseparate : ∀ value ∈ before, value ∉ suffix := by
    intro value hv hs
    exact (List.nodup_append.mp hnodup).2.2 value hv value hs rfl
  have hsortedInterval (word : List ℕ) (start size : ℕ)
      (hwordN : word.Nodup) (hwordSort : word.Pairwise (· < ·))
      (hwordMem : ∀ value, value ∈ word ↔ start ≤ value ∧ value < start + size) :
      word = List.range' start size := by
    apply List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => by omega)
      hwordSort (List.pairwise_lt_range')
    apply (List.perm_ext_iff_of_nodup hwordN (List.nodup_range')).mpr
    intro value
    rw [hwordMem]
    simp only [List.mem_range', Nat.one_mul]
    constructor
    · rintro ⟨hlo, hhi⟩
      exact ⟨value - start, by omega, by omega⟩
    · rintro ⟨offset, hoffset, rfl⟩
      omega
  by_cases hempty : low = ∅
  · have hbeforeMem : ∀ value, value ∈ before ↔ m < value ∧ value ≤ n := by
      intro value
      constructor
      · intro hv
        have hb := (hvalues value).mp (hbefore.subset hv)
        have hnlow : ¬ value < m := by
          intro hlt
          have := (hlow value).mpr ⟨hv, hlt⟩
          simp [hempty] at this
        have hne : value ≠ m := fun he => hseparate m (he ▸ hv) hmMem
        omega
      · rintro ⟨hlo, hhi⟩
        have hv := (hvalues value).mpr (by omega)
        rcases List.mem_append.mp hv with hv | hv
        · exact hv
        · have := hmax value hv
          omega
    have hbeforeEq : before = (List.range' (m + 1) (n - m)).reverse := by
      have hr : before.reverse = List.range' (m + 1) (n - m) := by
        apply hsortedInterval _ _ _ (List.nodup_reverse.mpr hbeforeN)
          (List.pairwise_reverse.mpr hbeforeDec)
        intro value
        rw [List.mem_reverse, hbeforeMem]
        omega
      simpa using congrArg List.reverse hr
    have hsuffixPerm : suffix.Perm (List.range' 1 m) := by
      apply (List.perm_ext_iff_of_nodup hsuffixN (List.nodup_range' 1)).mpr
      intro value
      simp only [List.mem_range'_1]
      constructor
      · intro hv
        have := (hvalues value).mp (hsuffix.subset hv)
        have := hmax value hv
        omega
      · intro hv
        have hvp := (hvalues value).mpr (by omega)
        rcases List.mem_append.mp hvp with hb | hs
        · have := (hbeforeMem value).mp hb
          omega
        · exact hs
    refine ⟨m, hm.1, hm.2, Or.inl ?_⟩
    exact ⟨⟨suffix, hsuffixPerm, hsuffixFish,
      by simpa only [List.mem_singleton, forall_eq] using htail213⟩, by simp [suffix],
      by rw [hbeforeEq]⟩
  · have hnonempty : low.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    let d := low.min' hnonempty
    let h := low.max' hnonempty
    have hdMem : d ∈ before ∧ d < m := (hlow d).mp (Finset.min'_mem _ _)
    have hhMem : h ∈ before ∧ h < m := (hlow h).mp (Finset.max'_mem _ _)
    have hd : 2 ≤ d := hbeforePositive d hdMem.1
    have hdh : d ≤ h := Finset.min'_le _ _ (Finset.max'_mem _ _)
    have hlowBounds : ∀ value ∈ before, value < m → d ≤ value ∧ value ≤ h := by
      intro value hv hlt
      have hvlow := (hlow value).mpr ⟨hv, hlt⟩
      exact ⟨Finset.min'_le _ _ hvlow, Finset.le_max' _ _ hvlow⟩
    have hmTail : m ∈ tail := by
      have : m ≠ 1 := by omega
      simpa [suffix, this] using hmMem
    obtain ⟨middle, last, htail⟩ := List.mem_iff_append.mp hmTail
    have hform : suffix = 1 :: (middle ++ m :: last) := by simp [suffix, htail]
    have hmiddleSub : middle.Sublist suffix := by
      rw [hform]
      exact (List.sublist_append_left _ _).cons _
    have hlastSub : last.Sublist suffix := by
      rw [hform]
      exact ((List.Sublist.refl last).cons m).trans
        ((List.sublist_append_right middle (m :: last)).cons 1)
    have hmiddleN := hsuffixN.sublist hmiddleSub
    have hlastN := hsuffixN.sublist hlastSub
    have hmNot : m ∉ middle ++ last := by
      have hn := hsuffixN
      rw [hform] at hn
      have hparts := List.nodup_append.mp (List.nodup_cons.mp hn).2
      intro hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hparts.2.2 m hv m (by simp) rfl
      · exact (List.nodup_cons.mp hparts.2.1).1 hv
    have hmiddleMax : ∀ value ∈ middle, value < m := by
      intro value hv
      have := hmax value (hmiddleSub.subset hv)
      have : value ≠ m := fun he => hmNot (by simp [← he, hv])
      omega
    have hlastMax : ∀ value ∈ last, value < m := by
      intro value hv
      have := hmax value (hlastSub.subset hv)
      have : value ≠ m := fun he => hmNot (by simp [← he, hv])
      omega
    have hmake (pattern : List ℕ) (size : ℕ) (values : ℕ → ℕ)
        (hpattern : ∀ rank, 1 ≤ rank → rank ≤ size → rank ∈ pattern)
        (hstep : ∀ rank, 1 ≤ rank → rank < size → values rank < values (rank + 1))
        (hsub : (pattern.map values).Sublist (before ++ suffix)) :
        ArrowWilfDefs.Contains pattern [] size (before ++ suffix) := by
      exact ⟨values, hstep, fun rank hl hh =>
        hsub.subset (List.mem_map_of_mem (hpattern rank hl hh)), hsub, by simp⟩
    have hmiddleInc : middle.Pairwise (· < ·) := by
      apply List.pairwise_iff_forall_sublist.mpr
      intro first second hpair
      have hne : first ≠ second := by simpa using hmiddleN.sublist hpair
      have hmfirst := hmiddleMax first (hpair.subset (by simp))
      by_contra hnot
      apply htail213
      change ArrowWilfDefs.Contains [2, 1, 3] [] 3 suffix
      let values : ℕ → ℕ := fun rank => if rank = 1 then second
        else if rank = 2 then first else m
      refine ⟨values, ?_, ?_, ?_, by simp⟩
      · intro rank hl hh
        have : rank = 1 ∨ rank = 2 := by omega
        rcases this with rfl | rfl <;> simp [values] <;> omega
      · intro rank hl hh
        have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases this with rfl | rfl | rfl <;> simp [values]
        · exact hmiddleSub.subset (hpair.subset (by simp))
        · exact hmiddleSub.subset (hpair.subset (by simp))
        · exact hmMem
      · rw [hform]
        have ht := hpair.append (show [m].Sublist (m :: last) by simp)
        simpa [values] using ht.cons 1
    have hlastLow : ∀ value ∈ last, value < d := by
      intro value hv
      have hne : value ≠ d := fun he => hseparate d hdMem.1 (he ▸ hlastSub.subset hv)
      by_contra hnot
      apply h2143
      let values : ℕ → ℕ := fun rank => if rank = 1 then 1
        else if rank = 2 then d else if rank = 3 then value else m
      apply hmake [2, 1, 4, 3] 4 values (by intro rank hl hh; simp; omega)
      · intro rank hl hh
        have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases this with rfl | rfl | rfl <;> simp [values] <;>
          have := hlastMax value hv <;> omega
      · rw [hform]
        have hsub : [d, 1, m, value].Sublist
            (before ++ 1 :: (middle ++ m :: last)) :=
          (List.singleton_sublist.mpr hdMem.1).append
            ((((List.singleton_sublist.mpr hv).cons_cons m).trans
              (List.sublist_append_right middle (m :: last))).cons_cons 1)
        simpa [values] using hsub
    have hmiddleHigh : ∀ value ∈ middle, h < value := by
      intro value hv
      have hne : value ≠ h :=
        fun he => hseparate h hhMem.1 (he ▸ hmiddleSub.subset hv)
      have hpos : 1 < value := by
        have hn := hsuffixN
        rw [hform] at hn
        have hnot1 := (List.nodup_cons.mp hn).1
        have := ((hvalues value).mp (hsuffix.subset (hmiddleSub.subset hv))).1
        have : value ≠ 1 := fun he => hnot1 (by simp [← he, hv])
        omega
      by_contra hnot
      apply h3124
      let values : ℕ → ℕ := fun rank => if rank = 1 then 1
        else if rank = 2 then value else if rank = 3 then h else m
      apply hmake [3, 1, 2, 4] 4 values (by intro rank hl hh; simp; omega)
      · intro rank hl hh
        have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases this with rfl | rfl | rfl <;> simp [values] <;> omega
      · rw [hform]
        have hsub : [h, 1, value, m].Sublist
            (before ++ 1 :: (middle ++ m :: last)) :=
          (List.singleton_sublist.mpr hhMem.1).append
            (((List.singleton_sublist.mpr hv).append
              (show [m].Sublist (m :: last) by simp)).cons_cons 1)
        simpa [values] using hsub
    have hlastPositive : ∀ value ∈ last, 2 ≤ value := by
      intro value hv
      have hn := hsuffixN
      rw [hform] at hn
      have hnot1 := (List.nodup_cons.mp hn).1
      have := ((hvalues value).mp (hsuffix.subset (hlastSub.subset hv))).1
      have : value ≠ 1 := fun he => hnot1 (by simp [← he, hv])
      omega
    have hpartition : ∀ value, value ∈ before ++ suffix ↔
        value ∈ before ∨ value = 1 ∨ value ∈ middle ∨ value = m ∨ value ∈ last := by
      intro value
      simp [hform]
    have hmiddleMem : ∀ value, value ∈ middle ↔ h < value ∧ value < m := by
      intro value
      constructor
      · intro hv
        exact ⟨hmiddleHigh value hv, hmiddleMax value hv⟩
      · rintro ⟨hlo, hhi⟩
        have hv := (hpartition value).mp ((hvalues value).mpr (by omega))
        rcases hv with hv | hv | hv | hv | hv
        · have := (hlowBounds value hv hhi).2
          omega
        · omega
        · exact hv
        · omega
        · have := hlastLow value hv
          omega
    have hlastMem : ∀ value, value ∈ last ↔ 2 ≤ value ∧ value < d := by
      intro value
      constructor
      · intro hv
        exact ⟨hlastPositive value hv, hlastLow value hv⟩
      · rintro ⟨hlo, hhi⟩
        have hv := (hpartition value).mp ((hvalues value).mpr (by omega))
        rcases hv with hv | hv | hv | hv | hv
        · have := (hlowBounds value hv (by omega)).1
          omega
        · omega
        · have := hmiddleHigh value hv
          omega
        · omega
        · exact hv
    have hbeforeMem : ∀ value, value ∈ before ↔
        (m < value ∧ value ≤ n) ∨ (d ≤ value ∧ value ≤ h) := by
      intro value
      constructor
      · intro hv
        have hbound := (hvalues value).mp (hbefore.subset hv)
        have hne : value ≠ m := fun he => hseparate m (he ▸ hv) hmMem
        by_cases hlt : value < m
        · exact Or.inr (hlowBounds value hv hlt)
        · exact Or.inl ⟨by omega, hbound.2⟩
      · intro hv
        have hbound : 1 ≤ value ∧ value ≤ n := by rcases hv with hv | hv <;> omega
        have hvp := (hpartition value).mp ((hvalues value).mpr hbound)
        rcases hvp with hvp | hvp | hvp | hvp | hvp
        · exact hvp
        · rcases hv with hv | hv <;> omega
        · have := (hmiddleMem value).mp hvp
          rcases hv with hv | hv <;> omega
        · rcases hv with hv | hv <;> omega
        · have := (hlastMem value).mp hvp
          rcases hv with hv | hv <;> omega
    have hmiddleEq : middle = List.range' (h + 1) (m - h - 1) := by
      apply hsortedInterval _ _ _ hmiddleN hmiddleInc
      intro value
      rw [hmiddleMem]
      omega
    have hbeforeEq : before = (List.range' (m + 1) (n - m)).reverse ++
        (List.range' d (h + 1 - d)).reverse := by
      let upper := before.filter (m < ·)
      let lower := before.filter (· ≤ m)
      have hu : upper.reverse = List.range' (m + 1) (n - m) := by
        apply hsortedInterval _ _ _ (List.nodup_reverse.mpr (hbeforeN.filter _))
          (List.pairwise_reverse.mpr (hbeforeDec.filter _))
        intro value
        simp only [List.mem_reverse, List.mem_filter, decide_eq_true_eq]
        rw [hbeforeMem]
        omega
      have hl : lower.reverse = List.range' d (h + 1 - d) := by
        apply hsortedInterval _ _ _ (List.nodup_reverse.mpr (hbeforeN.filter _))
          (List.pairwise_reverse.mpr (hbeforeDec.filter _))
        intro value
        simp only [List.mem_reverse, List.mem_filter, decide_eq_true_eq]
        rw [hbeforeMem]
        omega
      have hsplit : before = upper ++ lower := by
        apply List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => by omega) hbeforeDec
        · apply List.pairwise_append.mpr
          refine ⟨hbeforeDec.filter _, hbeforeDec.filter _, ?_⟩
          intro high hh low hl
          simp only [upper, lower, List.mem_filter, decide_eq_true_eq] at hh hl
          omega
        · have hnotfun : (fun value => !decide (m < value)) =
              (fun value => decide (value ≤ m)) := by
            funext value
            rw [← decide_not]
            simp only [not_lt]
          have ht := (List.filter_append_perm (fun value => decide (m < value)) before).symm
          rw [hnotfun] at ht
          exact ht
      have hu' := congrArg List.reverse hu
      have hl' := congrArg List.reverse hl
      simpa using hsplit.trans (congrArg₂ List.append
        (by simpa using hu') (by simpa using hl'))
    have hlastPerm : last.Perm (List.range' 2 (d - 2)) := by
      apply (List.perm_ext_iff_of_nodup hlastN (List.nodup_range')).mpr
      intro value
      rw [hlastMem]
      simp only [List.mem_range', Nat.one_mul]
      constructor
      · rintro ⟨hlo, hhi⟩
        exact ⟨value - 2, by omega, by omega⟩
      · rintro ⟨offset, hoffset, rfl⟩
        omega
    let q := last.map (· - 1)
    have hshift : q.map (· + 1) = last := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id last]
      apply List.map_congr_left
      intro value hv
      have := hlastPositive value hv
      dsimp
      omega
    have hqPerm : q.Perm (List.range' 1 (d - 2)) := by
      have hmapped := hlastPerm.map (· - 1)
      simpa [q, List.map_sub_range' (by omega : 1 ≤ 2) (d - 2)] using hmapped
    have hlastFish : IsFishburn last := by
      have hwhole : before ++ suffix = (before ++ 1 :: (middle ++ [m])) ++ last := by
        simp [hform, List.append_assoc]
      rw [hwhole] at hfish
      intro first later hgap hlater hbad
      let offset := (before ++ 1 :: (middle ++ [m])).length
      apply hfish (offset + first) (offset + later) (by omega)
        (by dsimp [offset]; simp only [List.length_append, List.length_cons]; omega)
      have hat (index : ℕ) :
          ((before ++ 1 :: (middle ++ [m])) ++ last).getD (offset + index) 0 =
            last.getD index 0 := by
        rw [List.getD_append_right (before ++ 1 :: (middle ++ [m])) last 0 _
          (by change offset ≤ offset + index; omega), Nat.add_sub_cancel_left]
      rw [show offset + first + 1 = offset + (first + 1) by omega, hat, hat, hat]
      exact hbad
    have hqFish : IsFishburn q := by
      intro first later hgap hlater hbad
      have hlength : q.length = last.length := by simp [q]
      have htranslate (index : ℕ) (hi : index < q.length) :
          last.getD index 0 = q.getD index 0 + 1 := by
        rw [← hshift]
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
          List.getD_eq_getElem _ _ hi]
      apply hlastFish first later hgap (by omega)
      rw [htranslate first (by omega), htranslate later hlater,
        htranslate (first + 1) (by omega)]
      omega
    have hqAvoid : ¬ NonnestingDefs.Occurs [2, 1, 3] q := by
      change ¬ ArrowWilfDefs.Contains [2, 1, 3] [] 3 q
      rintro ⟨values, hstep, hmem, hsub, _⟩
      apply htail213
      refine ⟨fun rank => values rank + 1, ?_, ?_, ?_, by simp⟩
      · intro rank hl hh
        exact Nat.add_lt_add_right (hstep rank hl hh) 1
      · intro rank hl hh
        apply hlastSub.subset
        rw [← hshift]
        exact List.mem_map_of_mem (hmem rank hl hh)
      · have ht := hsub.map (· + 1)
        rw [hshift] at ht
        have ht' : ([2, 1, 3].map (fun rank => values rank + 1)).Sublist last := by
          simpa [List.map_map, Function.comp_def] using ht
        exact ht'.trans hlastSub
    refine ⟨m, hm.1, hm.2, Or.inr ⟨d, h, hd, hdh, hhMem.2,
      ⟨q, hqPerm, hqFish,
        by simpa only [List.mem_singleton, forall_eq] using hqAvoid⟩, ?_⟩⟩
    change before ++ suffix = _
    change before ++ suffix = (List.range' (m + 1) (n - m)).reverse ++
      (List.range' d (h + 1 - d)).reverse ++
        1 :: (List.range' (h + 1) (m - h - 1) ++ m :: q.map (· + 1))
    rw [hbeforeEq, hform, hmiddleEq, hshift]

end D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenBStructure
