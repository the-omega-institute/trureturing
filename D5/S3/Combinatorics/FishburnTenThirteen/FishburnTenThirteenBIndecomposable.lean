/- GID: D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBIndecomposable
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBIndecomposable
   mirror-E: none(waiver:inductive-first-component-site-obstruction)
   anchors: []
   utility: none
   digest: B insertion families have exact component and ranked active-cut labels. -/

import D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenBUpdates
import D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenBSums
import D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicSumInsertion

open D5.S3.Combinatorics.Fishburn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenBIndecomposable

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasicParents FishburnBasicFourPatterns FishburnBasicTenThirteenPatterns
open FishburnBasicComponents FishburnBasicSumInsertion FishburnTenThirteenBUpdates
open FishburnTenThirteenBSums
open NonnestingBasicSum

theorem crossing_indecomposable_sites (n : ℕ) (p : List ℕ)
    (hparent : p ∈ avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]])
    (hindec : sumIndecomposable p) (site : ℕ) (hpositive : 0 < site)
    (hsite : site ≤ p.length)
    (hactive : p.insertIdx site (n + 1) ∈
      avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]]) :
    n ∈ p.take site ∧
      (site < p.length →
        let cuts := @Finset.filter ℕ (fun gap =>
          p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]])
          (fun _ => Classical.propDecidable _) (Finset.range (p.length + 1))
        let child := p.insertIdx site (n + 1)
        let childCuts := @Finset.filter ℕ (fun gap =>
          child.insertIdx gap (n + 2) ∈ avoiders (n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]])
          (fun _ => Classical.propDecidable _) (Finset.range (child.length + 1))
        childCuts.card = cuts.card + 1 - (cuts.filter fun gap => gap < site).card) := by
  classical
  have hvalues (size : ℕ) (block : List ℕ) (hp : block.Perm (List.range' 1 size))
      (value : ℕ) (hv : value ∈ block) : 1 ≤ value ∧ value ≤ size := by
    have hm := hp.mem_iff.mp hv
    simp only [List.mem_range', Nat.one_mul] at hm
    obtain ⟨index, hi, heq⟩ := hm
    omega
  have hlocalize (size : ℕ) (left tail : List ℕ)
      (hwhole : left ++ tail ∈ avoiders size [[2, 4, 3, 1], [3, 2, 4, 1]])
      (hl : left ∈ avoiders left.length [[2, 4, 3, 1], [3, 2, 4, 1]])
      (gap : ℕ) (hg : gap ≤ left.length)
      (ha : (left ++ tail).insertIdx gap (size + 1) ∈
        avoiders (size + 1) [[2, 4, 3, 1], [3, 2, 4, 1]]) :
      left.insertIdx gap (left.length + 1) ∈
        avoiders (left.length + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] := by
    have hbefore (index : ℕ) (hi : index < left.length) :
        (left ++ tail).getD index 0 = left.getD index 0 :=
      List.getD_append _ _ _ _ hi
    have hmwhole : ∀ value ∈ left ++ tail, value < size + 1 := by
      intro value hv
      have := (hvalues size (left ++ tail) hwhole.1 value hv).2
      omega
    have hmleft : ∀ value ∈ left, value < left.length + 1 := by
      intro value hv
      have := (hvalues left.length left hl.1 value hv).2
      omega
    have hel := (isFishburn_insertIdx_max_iff (left ++ tail) (size + 1) gap
      (by simp only [List.length_append]; omega) hmwhole).mp ha.2.1 |>.2
    have hperm : (left.insertIdx gap (left.length + 1)).Perm
        (List.range' 1 (left.length + 1)) := by
      apply (List.perm_insertIdx (left.length + 1) left hg).trans
      apply (hl.1.cons (left.length + 1)).trans
      rw [List.range'_concat]
      simpa [Nat.add_comm] using
        (List.perm_append_comm (l₁ := [left.length + 1])
          (l₂ := List.range' 1 left.length))
    refine ⟨hperm, ?_, ?_⟩
    · apply (isFishburn_insertIdx_max_iff left (left.length + 1) gap hg hmleft).mpr
      refine ⟨hl.2.1, ?_⟩
      intro before later hb hlow hbound hbad
      apply hel before later hb hlow (by simp only [List.length_append]; omega)
      simpa only [hbefore before (by omega), hbefore later hbound] using hbad
    · intro pattern hpattern hbad
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl
      · rcases (maximum_crossing_pattern_tests left.length left hl.1 gap hg).2.mp hbad
          with hold | ⟨first, second, third, hf, hs, hst, ht, hlo, hhi⟩
        · exact hl.2.2 _ (by simp) hold
        · apply ha.2.2 [2, 4, 3, 1] (by simp)
          apply (maximum_crossing_pattern_tests size (left ++ tail) hwhole.1 gap
            (by simp only [List.length_append]; omega)).2.mpr
          right
          refine ⟨first, second, third, hf, hs, hst,
            by simp only [List.length_append]; omega, ?_, ?_⟩
          · simpa only [hbefore third ht, hbefore first (by omega)] using hlo
          · simpa only [hbefore first (by omega), hbefore second (by omega)] using hhi
      · rcases (maximum_four_pattern_tests left.length left hl.1 gap hg).2.2.mp hbad
          with hold | ⟨first, second, third, hf, hs, hst, ht, hlo, hhi⟩
        · exact hl.2.2 _ (by simp) hold
        · apply ha.2.2 [3, 2, 4, 1] (by simp)
          apply (maximum_four_pattern_tests size (left ++ tail) hwhole.1 gap
            (by simp only [List.length_append]; omega)).2.2.mpr
          right
          refine ⟨first, second, third, hf, hs, hst,
            by simp only [List.length_append]; omega, ?_, ?_⟩
          · simpa only [hbefore third ht, hbefore second (by omega)] using hlo
          · simpa only [hbefore second (by omega), hbefore first (by omega)] using hhi
  have hpatterns : ∀ pattern ∈ [[2, 4, 3, 1], [3, 2, 4, 1]],
      pattern ≠ [] ∧ sumIndecomposable pattern ∧ (∀ value ∈ pattern, 1 ≤ value) ∧
        ∀ rank, 1 ≤ rank → rank ≤ NonnestingDefs.letters pattern → rank ∈ pattern := by
    intro pattern hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    all_goals
      refine ⟨by decide, by unfold sumIndecomposable; decide, by simp, ?_⟩
      intro rank hr hbound
      norm_num [NonnestingDefs.letters] at hbound
      simp only [List.mem_cons, List.not_mem_nil]
      omega
  have htailpositive (parts : List (List ℕ))
      (hparts : ∀ block ∈ parts, block.Perm (List.range' 1 block.length)) :
      ∀ value ∈ assemble parts, 1 ≤ value := by
    induction parts with
    | nil => simp [assemble]
    | cons first rest ih =>
      intro value hv
      rcases List.mem_append.mp hv with hfirst | hrest
      · exact (hvalues first.length first (hparts first (by simp)) value hfirst).1
      · obtain ⟨small, hs, rfl⟩ := List.mem_map.mp hrest
        have := ih (fun block hb => hparts block (by simp [hb])) small hs
        omega
  have hpositions : ∀ size parent,
      parent ∈ avoiders size [[2, 4, 3, 1], [3, 2, 4, 1]] →
      sumIndecomposable parent → ∀ gap, 0 < gap → gap ≤ parent.length →
      parent.insertIdx gap (size + 1) ∈
        avoiders (size + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] → size ∈ parent.take gap := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
      intro child hc hindec gap hgapPositive hgapBound hgapActive
      cases size with
      | zero =>
        have hlength : child.length = 0 := by simpa using hc.1.length_eq
        omega
      | succ size =>
        obtain ⟨entry, heq⟩ :=
          (maximum_insertion_bijection size [[2, 4, 3, 1], [3, 2, 4, 1]]).2 ⟨child, hc⟩
        let parent := entry.val.1
        let insertion := entry.val.2
        have hp : parent ∈ avoiders size [[2, 4, 3, 1], [3, 2, 4, 1]] := entry.property.1
        have hinsBound : insertion ≤ parent.length := entry.property.2.1
        have hinsActive : parent.insertIdx insertion (size + 1) ∈
            avoiders (size + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] := entry.property.2.2
        have hword : parent.insertIdx insertion (size + 1) = child :=
          congrArg Subtype.val heq
        have hparentLength : parent.length = size := by simpa using hp.1.length_eq
        have hchildLength : child.length = parent.length + 1 := by
          rw [← hword]
          exact List.length_insertIdx_of_le_length hinsBound _
        by_cases hafter : insertion < gap
        · apply List.mem_take_iff_getElem.mpr
          refine ⟨insertion, by omega, ?_⟩
          have hat : (parent.insertIdx insertion (size + 1)).getD insertion 0 =
              size + 1 := by
            rw [List.getD_eq_getElem _ 0 (by
              rw [List.length_insertIdx_of_le_length hinsBound]
              omega)]
            exact List.getElem_insertIdx_self _
          rw [hword] at hat
          exact (List.getD_eq_getElem child 0 (by omega)).symm.trans hat
        have hbefore : gap ≤ insertion := by omega
        have hsizePositive : 0 < size := by omega
        have hupdates := (crossing_site_updates size parent hsizePositive hp insertion
          hinsBound hinsActive).1 gap hbefore
        have hgapChild : (parent.insertIdx insertion (size + 1)).insertIdx gap (size + 2) ∈
            avoiders (size + 2) [[2, 4, 3, 1], [3, 2, 4, 1]] := by
          simpa only [hword, Nat.succ_eq_add_one, Nat.add_assoc] using hgapActive
        obtain ⟨hgapParent, hseparation⟩ := hupdates.mp hgapChild
        have hcuts := (indecomposable_maximum_insertion size parent hp.1 insertion
          hinsBound).mp (by rwa [hword])
        obtain ⟨parts, hparts, _⟩ := (unique_sum_components size parent hp.1
          [[2, 4, 3, 1], [3, 2, 4, 1]] hpatterns).1
        cases parts with
        | nil =>
          have hempty : parent = [] := by simpa [assemble] using hparts.1.symm
          simp only [hempty, List.length_nil] at hinsBound
          omega
        | cons first rest =>
          have hf := hparts.2.1 first (by simp)
          have hfClass : first ∈ avoiders first.length [[2, 4, 3, 1], [3, 2, 4, 1]] :=
            (hparts.2.2.mp hp) first (by simp)
          have hdecomp : parent = first ++ shift first.length (assemble rest) :=
            hparts.1.symm
          have hlength : parent.length = first.length + (assemble rest).length := by
            simp [hdecomp, shift]
          have hfirstPositive : 0 < first.length := List.length_pos_iff_ne_nil.mpr hf.1
          have hrightPositive : ∀ value ∈ assemble rest, 1 ≤ value :=
            htailpositive rest (fun block hb => (hparts.2.1 block (by simp [hb])).2.1)
          have hlocalBefore (index : ℕ) (hi : index < first.length) :
              parent.getD index 0 = first.getD index 0 := by
            rw [hdecomp]
            exact List.getD_append _ _ _ _ hi
          have hsmall (index : ℕ) (hi : index < first.length) :
              parent.getD index 0 ≤ first.length := by
            rw [hlocalBefore index hi]
            apply (hvalues first.length first hf.2.1 _ _).2
            rw [List.getD_eq_getElem first 0 hi]
            exact List.getElem_mem hi
          have hinternal : insertion < first.length := by
            by_contra hnot
            obtain ⟨before, later, hb, hl, hbound, hbad⟩ :=
              hcuts first.length hfirstPositive (by omega)
            have hsmallValue := hsmall before hb
            have hlater : parent.getD later 0 ∈ shift first.length (assemble rest) := by
              rw [hdecomp, List.getD_append_right _ _ _ _ hl,
                List.getD_eq_getElem _ 0 (by simp only [shift, List.length_map]; omega)]
              exact List.getElem_mem (by simp only [shift, List.length_map]; omega)
            obtain ⟨value, hv, hequal⟩ := List.mem_map.mp hlater
            have := hrightPositive value hv
            omega
          have hfirstActive := hlocalize size first (shift first.length (assemble rest))
            (by rwa [← hdecomp]) hfClass gap (by omega) (by rwa [← hdecomp])
          have hfirstSmall : first.length < size + 1 := by omega
          have hfirstMax := ih first.length hfirstSmall first hfClass hf.2.2 gap
            hgapPositive (by omega) hfirstActive
          obtain ⟨maxIndex, hmaxIndex, hmaxValue⟩ := List.mem_take_iff_getElem.mp hfirstMax
          have hmaxD : parent.getD maxIndex 0 = first.length := by
            rw [hlocalBefore maxIndex (by omega), List.getD_eq_getElem first 0 (by omega)]
            exact hmaxValue
          have hcontra := hseparation maxIndex insertion (by omega) le_rfl
            (by omega)
          have := hsmall insertion hinternal
          omega
  refine ⟨hpositions n p hparent hindec site hpositive hsite hactive, ?_⟩
  intro hproper
  dsimp only
  let cuts := (Finset.range (p.length + 1)).filter fun gap =>
    p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]]
  let child := p.insertIdx site (n + 1)
  let childCuts := (Finset.range (child.length + 1)).filter fun gap =>
    child.insertIdx gap (n + 2) ∈ avoiders (n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]]
  let laterCuts := cuts.filter fun gap => site < gap
  change childCuts.card = cuts.card + 1 - (cuts.filter fun gap => gap < site).card
  have hn : 0 < n := by
    have := hparent.1.length_eq
    simp only [List.length_range'] at this
    omega
  have hlength : child.length = p.length + 1 :=
    List.length_insertIdx_of_le_length hsite _
  have hcuts (gap : ℕ) : gap ∈ cuts ↔ gap ≤ p.length ∧
      p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] := by
    simp only [cuts, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  have hchildren (gap : ℕ) : gap ∈ childCuts ↔ gap ≤ child.length ∧
      child.insertIdx gap (n + 2) ∈ avoiders (n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]] := by
    simp only [childCuts, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  have hupdates := crossing_site_updates n p hn hparent site hsite hactive
  have hmaximum : n ∈ p.take site :=
    hpositions n p hparent hindec site hpositive hsite hactive
  have hmiddle : site + 1 ∈ childCuts :=
    (hchildren _).mpr ⟨by omega, hupdates.2.2.1.mpr hmaximum⟩
  have hfront : child.insertIdx 0 (n + 2) ∈
      avoiders (n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]] := by
    have hbound : ∀ value ∈ child, value < n + 2 := by
      intro value hv
      have := hvalues (n + 1) child hactive.1 value hv
      omega
    have hperm : (child.insertIdx 0 (n + 2)).Perm (List.range' 1 (n + 2)) := by
      apply (List.perm_insertIdx (n + 2) child (Nat.zero_le _)).trans
      apply (hactive.1.cons (n + 2)).trans
      have hconcat : List.range' 1 (n + 2) = List.range' 1 (n + 1) ++ [n + 2] := by
        simpa only [Nat.add_assoc, Nat.one_add, Nat.one_mul] using
          (List.range'_concat (s := 1) (n := n + 1) (step := 1))
      rw [hconcat]
      exact
        (List.perm_append_comm (l₁ := [n + 2]) (l₂ := List.range' 1 (n + 1)))
    refine ⟨hperm, ?_, ?_⟩
    · apply (isFishburn_insertIdx_max_iff child (n + 2) 0 (Nat.zero_le _) hbound).mpr
      exact ⟨hactive.2.1, by intros; omega⟩
    · intro pattern hp hbad
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · have htest := (maximum_crossing_pattern_tests (n + 1) child hactive.1 0
          (Nat.zero_le _)).2
        rcases htest.mp (by simpa only [Nat.add_assoc] using hbad) with hold | hnew
        · exact hactive.2.2 _ (by simp) hold
        · obtain ⟨first, second, third, hb, _⟩ := hnew
          omega
      · have htest := (maximum_four_pattern_tests (n + 1) child hactive.1 0
          (Nat.zero_le _)).2.2
        rcases htest.mp (by simpa only [Nat.add_assoc] using hbad) with hold | hnew
        · exact hactive.2.2 _ (by simp) hold
        · obtain ⟨first, second, third, _, hb, _⟩ := hnew
          omega
  have hchildZero : 0 ∈ childCuts := (hchildren 0).mpr ⟨Nat.zero_le _, hfront⟩
  have hnoBefore (gap : ℕ) (hg : 0 < gap) (hb : gap ≤ site) : gap ∉ childCuts := by
    intro hgap
    obtain ⟨hgapActive, hsep⟩ := (hupdates.1 gap hb).mp ((hchildren gap).mp hgap).2
    have hmaxGap := hpositions n p hparent hindec gap hg (by omega) hgapActive
    obtain ⟨maxIndex, hm, hvalue⟩ := List.mem_take_iff_getElem.mp hmaxGap
    have hmaxD : p.getD maxIndex 0 = n := by
      rw [List.getD_eq_getElem p 0 (by omega)]
      exact hvalue
    have hlater : p.getD site 0 ≤ n := by
      apply (hvalues n p hparent.1 _ _).2
      rw [List.getD_eq_getElem p 0 hproper]
      exact List.getElem_mem hproper
    have hless := hsep maxIndex site (by omega) le_rfl hproper
    rw [hmaxD] at hless
    omega
  have hsurvive (gap : ℕ) (hg : site < gap) (hb : gap ≤ p.length)
      (ha : p.insertIdx gap (n + 1) ∈
        avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]]) :
      child.insertIdx (gap + 1) (n + 2) ∈
        avoiders (n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]] := by
    apply (hupdates.2.1 gap hg hb).mpr
    refine ⟨ha, ?_⟩
    obtain ⟨maxIndex, hm, hvalue⟩ := List.mem_take_iff_getElem.mp hmaximum
    have hmaxD : p.getD maxIndex 0 = n := by
      rw [List.getD_eq_getElem p 0 (by omega)]
      exact hvalue
    have hempty : ([] : List ℕ) ∈ avoiders 0 [[2, 4, 3, 1], [3, 2, 4, 1]] := by
      refine ⟨by simp, ?_, ?_⟩
      · intro first second horder hbound
        simp at hbound
      · intro pattern hp hocc
        obtain ⟨values, _, hmem, _⟩ := hocc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        have hletters : 1 ≤ NonnestingDefs.letters pattern := by
          rcases hp with rfl | rfl <;> norm_num [NonnestingDefs.letters]
        have := hmem 1 le_rfl hletters
        simp at this
    have hsum := (crossing_sum_sites 0 n [] p hempty hparent
      (by simpa [directSum, shift] using hparent)).2.2
    have hseparation := hsum maxIndex gap (by simpa [directSum, shift] using hmaxD)
      (by omega) (by simpa [directSum, shift] using hb)
      (by simpa [directSum, shift] using ha)
    intro middle later hmiddle hmiddleGap hlater hbound
    simpa [directSum, shift] using hseparation middle later (by omega)
      hmiddleGap hlater (by simpa [directSum, shift] using hbound)
  have himage (gap : ℕ) : gap ∈ laterCuts.image (· + 1) ↔
      ∃ old, old ∈ cuts ∧ site < old ∧ old + 1 = gap := by
    simp only [Finset.mem_image, laterCuts, Finset.mem_filter]
    aesop
  have hdecomp : childCuts = {0, site + 1} ∪ laterCuts.image (· + 1) := by
    ext gap
    constructor
    · intro hg
      obtain ⟨hb, ha⟩ := (hchildren gap).mp hg
      by_cases hgap : gap = 0 ∨ gap = site + 1
      · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl hgap
      have hafter : site + 1 < gap := by
        by_contra hnot
        exact hnoBefore gap (by omega) (by omega) hg
      have hprevBound : gap - 1 ≤ p.length := by omega
      have hprevActive := (hupdates.2.1 (gap - 1) (by omega) hprevBound).mp
        (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ gap)] using ha) |>.1
      apply Finset.mem_union_right
      exact (himage gap).mpr ⟨gap - 1,
        (hcuts _).mpr ⟨hprevBound, hprevActive⟩, by omega, by omega⟩
    · intro hg
      rcases Finset.mem_union.mp hg with hspecial | him
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hspecial
        rcases hspecial with rfl | rfl
        · exact hchildZero
        · exact hmiddle
      · obtain ⟨old, hold, hafter, rfl⟩ := (himage gap).mp him
        obtain ⟨hb, ha⟩ := (hcuts old).mp hold
        exact (hchildren _).mpr ⟨by omega, hsurvive old hafter hb ha⟩
  have hdisjoint : Disjoint ({0, site + 1} : Finset ℕ)
      (laterCuts.image (· + 1)) := by
    apply Finset.disjoint_left.mpr
    intro gap hgap him
    obtain ⟨old, _, hafter, heq⟩ := (himage gap).mp him
    simp only [Finset.mem_insert, Finset.mem_singleton] at hgap
    omega
  have himageCard : (laterCuts.image (· + 1)).card = laterCuts.card :=
    Finset.card_image_of_injective _ (fun _ _ heq => Nat.add_right_cancel heq)
  have hpartition : laterCuts.card + (cuts.filter fun gap => gap < site).card + 1 =
      cuts.card := by
    have hsiteCut := (hcuts site).mpr ⟨hsite, hactive⟩
    have hlow : (cuts.filter fun gap => ¬ site < gap) =
        insert site (cuts.filter fun gap => gap < site) := by
      ext gap
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hg, hb⟩
        by_cases heq : gap = site
        · exact Or.inl heq
        · exact Or.inr ⟨hg, by omega⟩
      · rintro (rfl | ⟨hg, hb⟩)
        · exact ⟨hsiteCut, by omega⟩
        · exact ⟨hg, by omega⟩
    have hsplit := Finset.card_filter_add_card_filter_not (s := cuts) (site < ·)
    rw [hlow, Finset.card_insert_of_notMem (by simp)] at hsplit
    exact hsplit
  rw [hdecomp, Finset.card_union_of_disjoint hdisjoint, himageCard,
    Finset.card_pair (by omega : 0 ≠ site + 1)]
  omega

end D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenBIndecomposable

namespace D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenBConstruction

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasicFourPatterns FishburnBasicTenThirteenPatterns FishburnBasicComponents
open FishburnBasicComponentCuts FishburnBasicSumInsertion FishburnTenThirteenBUpdates
open FishburnTenThirteenBSums FishburnTenThirteenBIndecomposable NonnestingBasicSum

set_option maxHeartbeats 1200000 in
theorem decomposable_internal_construction (m n : ℕ) (left right : List ℕ)
    (hleft : left ∈ avoiders m [[2, 4, 3, 1], [3, 2, 4, 1]])
    (hright : right ∈ avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]])
    (hparent : directSum m left right ∈
      avoiders (m + n) [[2, 4, 3, 1], [3, 2, 4, 1]])
    (hindec : sumIndecomposable left) (hn : 0 < n)
    (site : ℕ) (hpositive : 0 < site) (hproper : site < left.length)
    (hactive : left.insertIdx site (m + 1) ∈
      avoiders (m + 1) [[2, 4, 3, 1], [3, 2, 4, 1]])
    (parts : List (List ℕ)) (hparts : ∀ block ∈ parts, block ≠ [] ∧
      block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block)
    (hassemble : assemble parts = right) :
    let word := directSum m left right
    let child := word.insertIdx site (m + n + 1)
    let cuts := @Finset.filter ℕ (fun gap =>
      left.insertIdx gap (m + 1) ∈ avoiders (m + 1) [[2, 4, 3, 1], [3, 2, 4, 1]])
      (fun _ => Classical.propDecidable _) (Finset.range (left.length + 1))
    let childCuts := @Finset.filter ℕ (fun gap =>
      child.insertIdx gap (m + n + 2) ∈
        avoiders (m + n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]])
      (fun _ => Classical.propDecidable _) (Finset.range (child.length + 1))
    child ∈ avoiders (m + n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] ∧
      sumIndecomposable child ∧
      childCuts.card + (cuts.filter fun gap => gap < site).card =
        cuts.card + parts.length := by
  classical
  dsimp only
  let word := directSum m left right
  let child := word.insertIdx site (m + n + 1)
  let cuts := (Finset.range (left.length + 1)).filter fun gap =>
    left.insertIdx gap (m + 1) ∈ avoiders (m + 1) [[2, 4, 3, 1], [3, 2, 4, 1]]
  let childCuts := (Finset.range (child.length + 1)).filter fun gap =>
    child.insertIdx gap (m + n + 2) ∈
      avoiders (m + n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]]
  let laterCuts := cuts.filter fun gap => site < gap
  let boundaries := (Finset.range (right.length + 1)).filter fun gap =>
    ∀ before ∈ right.take gap, ∀ later ∈ right.drop gap, before < later
  have hleftLen : left.length = m := by simpa using hleft.1.length_eq
  have hrightLen : right.length = n := by simpa using hright.1.length_eq
  have hlength : word.length = left.length + right.length := by
    simp [word, directSum, shift]
  have hsite : site ≤ word.length := by omega
  have hchildLen : child.length = word.length + 1 :=
    List.length_insertIdx_of_le_length hsite _
  have hvalues (size : ℕ) (block : List ℕ) (hp : block.Perm (List.range' 1 size))
      (index : ℕ) (hb : index < block.length) :
      1 ≤ block.getD index 0 ∧ block.getD index 0 ≤ size := by
    have hm := hp.mem_iff.mp (show block.getD index 0 ∈ block from by
      rw [List.getD_eq_getElem block 0 hb]
      exact List.getElem_mem hb)
    simp only [List.mem_range', Nat.one_mul] at hm
    obtain ⟨offset, ho, heq⟩ := hm
    omega
  have hbefore (index : ℕ) (hb : index < left.length) :
      word.getD index 0 = left.getD index 0 :=
    List.getD_append _ _ _ _ hb
  have hafter (index : ℕ) (hl : left.length ≤ index) (hb : index < word.length) :
      word.getD index 0 = right.getD (index - left.length) 0 + m := by
    change (left ++ shift m right).getD index 0 = _
    rw [List.getD_append_right _ _ _ _ hl]
    have hi : index - left.length < right.length := by omega
    rw [List.getD_eq_getElem _ 0 (by simpa [shift] using hi),
      List.getD_eq_getElem right 0 hi]
    simp [shift]
  have hsmall (index : ℕ) (hb : index < left.length) : word.getD index 0 ≤ m := by
    rw [hbefore index hb]
    exact (hvalues m left hleft.1 index hb).2
  have hlarge (index : ℕ) (hl : left.length ≤ index) (hb : index < word.length) :
      m < word.getD index 0 := by
    have := (hvalues n right hright.1 (index - left.length) (by omega)).1
    rw [hafter index hl hb]
    omega
  have hsums := crossing_sum_sites m n left right hleft hright hparent
  have hchild : child ∈ avoiders (m + n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] :=
    (hsums.1 site (by omega)).mpr hactive
  have hchildIndec : sumIndecomposable child := by
    apply (indecomposable_maximum_insertion (m + n) word hparent.1 site hsite).mpr
    intro boundary hb hs
    obtain ⟨before, later, hbad⟩ := hindec ⟨boundary, by omega⟩ hb
    have hbef : before.val < boundary := by
      have := before.is_lt
      simp only [List.length_take] at this
      omega
    have hlat : boundary + later.val < left.length := by
      have := later.is_lt
      simp only [List.length_drop] at this
      omega
    refine ⟨before.val, boundary + later.val, hbef, by omega, by omega, ?_⟩
    rw [hbefore before.val (by omega), hbefore (boundary + later.val) hlat,
      List.getD_eq_getElem left 0 (by omega : before.val < left.length),
      List.getD_eq_getElem left 0 hlat]
    simpa only [List.get_eq_getElem, List.getElem_take, List.getElem_drop] using hbad
  refine ⟨hchild, hchildIndec, ?_⟩
  change childCuts.card + (cuts.filter fun gap => gap < site).card =
    cuts.card + parts.length
  have hcuts (gap : ℕ) : gap ∈ cuts ↔ gap ≤ left.length ∧
      left.insertIdx gap (m + 1) ∈ avoiders (m + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] := by
    simp only [cuts, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  have hchildren (gap : ℕ) : gap ∈ childCuts ↔ gap ≤ child.length ∧
      child.insertIdx gap (m + n + 2) ∈
        avoiders (m + n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]] := by
    simp only [childCuts, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  have hboundary (gap : ℕ) : gap ∈ boundaries ↔ gap ≤ right.length ∧
      ∀ before later, before < gap → gap ≤ later → later < right.length →
        right.getD before 0 < right.getD later 0 := by
    simp only [boundaries, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · rintro ⟨hb, hsep⟩
      refine ⟨hb, ?_⟩
      intro before later hbef hlat hbound
      apply hsep
      · apply List.mem_take_iff_getElem.mpr
        exact ⟨before, by omega, (List.getD_eq_getElem right 0 (by omega)).symm⟩
      · apply List.mem_drop_iff_getElem.mpr
        refine ⟨later - gap, by omega, ?_⟩
        simpa only [Nat.add_sub_cancel' hlat] using
          (List.getD_eq_getElem right 0 hbound).symm
    · rintro ⟨hb, hsep⟩
      refine ⟨hb, ?_⟩
      intro before hbef later hlat
      obtain ⟨first, hf, heq⟩ := List.mem_take_iff_getElem.mp hbef
      obtain ⟨second, hs, hseq⟩ := List.mem_drop_iff_getElem.mp hlat
      have hless := hsep first (gap + second) (by omega) (by omega) (by omega)
      rw [List.getD_eq_getElem right 0 (by omega),
        List.getD_eq_getElem right 0 (by omega), heq, hseq] at hless
      exact hless
  have hseparatedActive (size : ℕ) (block : List ℕ)
      (hp : block ∈ avoiders size [[2, 4, 3, 1], [3, 2, 4, 1]])
      (gap : ℕ) (hg : gap ≤ block.length)
      (hsep : ∀ before later, before < gap → gap ≤ later → later < block.length →
        block.getD before 0 < block.getD later 0) :
      block.insertIdx gap (size + 1) ∈
        avoiders (size + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] := by
    have hmax : ∀ value ∈ block, value < size + 1 := by
      intro value hv
      have hm := hp.1.mem_iff.mp hv
      simp only [List.mem_range', Nat.one_mul] at hm
      obtain ⟨offset, ho, heq⟩ := hm
      omega
    have hperm : (block.insertIdx gap (size + 1)).Perm (List.range' 1 (size + 1)) := by
      apply (List.perm_insertIdx (size + 1) block hg).trans
      apply (hp.1.cons (size + 1)).trans
      rw [List.range'_concat]
      simpa [Nat.add_comm] using
        (List.perm_append_comm (l₁ := [size + 1]) (l₂ := List.range' 1 size))
    refine ⟨hperm, ?_, ?_⟩
    · apply (isFishburn_insertIdx_max_iff block (size + 1) gap hg hmax).mpr
      refine ⟨hp.2.1, ?_⟩
      intro before later hb hl hbound heq
      have := hsep before later (by omega) hl hbound
      omega
    · intro pattern hpattern hbad
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl
      · rcases (maximum_crossing_pattern_tests size block hp.1 gap hg).2.mp hbad with
          hold | ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩
        · exact hp.2.2 _ (by simp) hold
        · have := hsep first third hf (by omega) ht
          omega
      · rcases (maximum_four_pattern_tests size block hp.1 gap hg).2.2.mp hbad with
          hold | ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩
        · exact hp.2.2 _ (by simp) hold
        · have := hsep second third hs hst ht
          omega
  have hupdates := crossing_site_updates (m + n) word (by omega) hparent site hsite hchild
  have hzero : 0 ∈ childCuts := by
    apply (hchildren 0).mpr
    exact ⟨Nat.zero_le _, hseparatedActive (m + n + 1) child hchild 0
      (Nat.zero_le _) (by intros; omega)⟩
  have hnoNew : site + 1 ∉ childCuts := by
    intro hg
    have hmax := hupdates.2.2.1.mp ((hchildren _).mp hg).2
    obtain ⟨index, hi, heq⟩ := List.mem_take_iff_getElem.mp hmax
    have hsmallMax := hsmall index (by omega)
    rw [List.getD_eq_getElem word 0 (by omega), heq] at hsmallMax
    omega
  have hnoBefore (gap : ℕ) (hg : 0 < gap) (hb : gap ≤ site) : gap ∉ childCuts := by
    intro hc
    obtain ⟨hactiveGap, hsep⟩ := (hupdates.1 gap hb).mp ((hchildren gap).mp hc).2
    have hlocal := (hsums.1 gap (by omega)).mp hactiveGap
    have hmax := (crossing_indecomposable_sites m left hleft hindec gap hg
      (by omega) hlocal).1
    obtain ⟨index, hi, heq⟩ := List.mem_take_iff_getElem.mp hmax
    have hcontra := hsep index site (by omega) le_rfl (by omega)
    have hsmallSite := hsmall site hproper
    rw [hbefore index (by omega), List.getD_eq_getElem left 0 (by omega), heq] at hcontra
    omega
  have hmaximum := (crossing_indecomposable_sites m left hleft hindec site hpositive
    (by omega) hactive).1
  obtain ⟨maximum, hmaximumBound, hmaximumValue⟩ :=
    List.mem_take_iff_getElem.mp hmaximum
  have hmaximumD : left.getD maximum 0 = m := by
    rw [List.getD_eq_getElem left 0 (by omega)]
    exact hmaximumValue
  have hempty : ([] : List ℕ) ∈ avoiders 0 [[2, 4, 3, 1], [3, 2, 4, 1]] := by
    refine ⟨by simp, ?_, ?_⟩
    · intro first second horder hbound
      simp at hbound
    · intro pattern hp hocc
      obtain ⟨values, _, hmem, _⟩ := hocc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      have hletters : 1 ≤ NonnestingDefs.letters pattern := by
        rcases hp with rfl | rfl <;> norm_num [NonnestingDefs.letters]
      have := hmem 1 le_rfl hletters
      simp at this
  have hlocalSurvives (gap : ℕ) (hafterSite : site < gap) (hb : gap ≤ left.length) :
      gap + 1 ∈ childCuts ↔ gap ∈ cuts := by
    constructor
    · intro hg
      have hold := ((hupdates.2.1 gap hafterSite (by omega)).mp
        ((hchildren _).mp hg).2).1
      exact (hcuts gap).mpr ⟨hb, (hsums.1 gap hb).mp hold⟩
    · intro hg
      have ha := ((hcuts gap).mp hg).2
      have htail := (crossing_sum_sites 0 m [] left hempty hleft
        (by simpa [directSum, shift] using hleft)).2.2 maximum gap
        (by simpa [directSum, shift] using hmaximumD) (by omega)
        (by simpa [directSum, shift] using hb) (by simpa [directSum, shift] using ha)
      apply (hchildren _).mpr
      refine ⟨by omega, (hupdates.2.1 gap hafterSite (by omega)).mpr
        ⟨(hsums.1 gap hb).mpr ha, ?_⟩⟩
      intro middle later hm hmg hgl hl
      by_cases hleftLater : later < left.length
      · have hless := htail middle later (by omega) hmg hgl
          (by simpa [directSum, shift] using hleftLater)
        rw [hbefore middle (by omega), hbefore later hleftLater]
        simpa [directSum, shift] using hless
      · have := hsmall middle (by omega)
        have := hlarge later (by omega) hl
        omega
  have htailSurvives (gap : ℕ) (hpositiveGap : 0 < gap) (hb : gap ≤ right.length) :
      left.length + gap + 1 ∈ childCuts ↔ gap ∈ boundaries := by
    constructor
    · intro hg
      have hsep := ((hupdates.2.1 (left.length + gap) (by omega) (by omega)).mp
        ((hchildren _).mp hg).2).2
      apply (hboundary gap).mpr
      refine ⟨hb, ?_⟩
      intro before later hbef hlat hbound
      have hless := hsep (left.length + before) (left.length + later)
        (by omega) (by omega) (by omega) (by omega)
      rw [hafter _ (by omega) (by omega), hafter _ (by omega) (by omega),
        Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at hless
      omega
    · intro hg
      have hsep := ((hboundary gap).mp hg).2
      have hrightActive := hseparatedActive n right hright gap hb hsep
      apply (hchildren _).mpr
      refine ⟨by omega, (hupdates.2.1 (left.length + gap) (by omega) (by omega)).mpr
        ⟨(hsums.2.1 gap hb).mpr hrightActive, ?_⟩⟩
      intro middle later hm hmg hgl hl
      by_cases hleftMiddle : middle < left.length
      · have := hsmall middle hleftMiddle
        have := hlarge later (by omega) hl
        omega
      · have hless := hsep (middle - left.length) (later - left.length)
          (by omega) (by omega) (by omega)
        rw [hafter middle (by omega) (by omega), hafter later (by omega) hl]
        omega
  have hdecomp : childCuts = {0} ∪ laterCuts.image (· + 1) ∪
      (boundaries.erase 0).image (fun gap => left.length + gap + 1) := by
    ext gap
    constructor
    · intro hg
      have hb := ((hchildren gap).mp hg).1
      by_cases hz : gap = 0
      · simp [hz]
      have hafterSite : site + 1 < gap := by
        by_contra hnot
        by_cases hnew : gap = site + 1
        · exact hnoNew (by simpa only [hnew] using hg)
        · exact hnoBefore gap (by omega) (by omega) hg
      by_cases hlocal : gap - 1 ≤ left.length
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨gap - 1, ?_, by omega⟩
        apply Finset.mem_filter.mpr
        refine ⟨(hlocalSurvives (gap - 1) (by omega) hlocal).mp
          (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ gap)] using hg), by omega⟩
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨gap - 1 - left.length, ?_, by omega⟩
        apply Finset.mem_erase.mpr
        refine ⟨by omega, (htailSurvives _ (by omega) (by omega)).mp ?_⟩
        simpa only [Nat.add_sub_cancel' (by omega : left.length ≤ gap - 1),
          Nat.sub_add_cancel (by omega : 1 ≤ gap)] using hg
    · intro hg
      rcases Finset.mem_union.mp hg with hfirst | htail
      · rcases Finset.mem_union.mp hfirst with hz | hlocal
        · simpa only [Finset.mem_singleton.mp hz] using hzero
        · obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp hlocal
          obtain ⟨ha, hs⟩ := Finset.mem_filter.mp hold
          exact (hlocalSurvives old hs ((hcuts old).mp ha).1).mpr ha
      · obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp htail
        obtain ⟨hnotZero, ha⟩ := Finset.mem_erase.mp hold
        exact (htailSurvives old (by omega) ((hboundary old).mp ha).1).mpr ha
  have hdisjointLocal : Disjoint ({0} : Finset ℕ) (laterCuts.image (· + 1)) := by
    apply Finset.disjoint_left.mpr
    intro gap hz him
    obtain ⟨old, _, heq⟩ := Finset.mem_image.mp him
    simp only [Finset.mem_singleton] at hz
    omega
  have hdisjointTail : Disjoint ({0} ∪ laterCuts.image (· + 1))
      ((boundaries.erase 0).image (fun gap => left.length + gap + 1)) := by
    apply Finset.disjoint_left.mpr
    intro gap hlocal htail
    obtain ⟨tailGap, ht, heq⟩ := Finset.mem_image.mp htail
    have htPositive : 0 < tailGap := by
      have := (Finset.mem_erase.mp ht).1
      omega
    rcases Finset.mem_union.mp hlocal with hz | him
    · simp only [Finset.mem_singleton] at hz
      omega
    · obtain ⟨old, ho, hequal⟩ := Finset.mem_image.mp him
      have := ((hcuts old).mp (Finset.mem_filter.mp ho).1).1
      omega
  have hlocalCard : (laterCuts.image (· + 1)).card = laterCuts.card :=
    Finset.card_image_of_injective _ (fun _ _ heq => Nat.add_right_cancel heq)
  have htailCard : ((boundaries.erase 0).image
      (fun gap => left.length + gap + 1)).card = (boundaries.erase 0).card := by
    apply Finset.card_image_of_injective
    intro first second heq
    dsimp only at heq
    omega
  have hboundaryZero : 0 ∈ boundaries := by simp [boundaries]
  have hboundaryCard : boundaries.card = parts.length + 1 := by
    simpa only [hassemble] using component_boundary_count parts hparts
  have htailCount := Finset.card_erase_add_one hboundaryZero
  have hsiteCut : site ∈ cuts := (hcuts site).mpr ⟨by omega, hactive⟩
  have hlow : cuts.filter (fun gap => ¬ site < gap) =
      insert site (cuts.filter fun gap => gap < site) := by
    ext gap
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hg, hs⟩
      by_cases heq : gap = site
      · exact Or.inl heq
      · exact Or.inr ⟨hg, by omega⟩
    · rintro (rfl | ⟨hg, hs⟩)
      · exact ⟨hsiteCut, by omega⟩
      · exact ⟨hg, by omega⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := cuts) (site < ·)
  rw [hlow, Finset.card_insert_of_notMem (by simp)] at hsplit
  rw [hdecomp, Finset.card_union_of_disjoint hdisjointTail,
    Finset.card_union_of_disjoint hdisjointLocal, Finset.card_singleton,
    hlocalCard, htailCard]
  change laterCuts.card + _ = _ at hsplit
  omega

end D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenBConstruction
