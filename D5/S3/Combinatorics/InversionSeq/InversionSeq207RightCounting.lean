/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207RightCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207RightCounting
   mirror-E: none(waiver:right-labelled-continuation-counting)
   anchors: []
   utility: none
   digest: First-entry counting identifies actual right continuations with four-type labels. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207Counting
import D5.S3.Combinatorics.InversionSeq.InversionSeq207RightChildren
import D5.S3.Combinatorics.InversionSeq.InversionSeq207RightReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207RightCounting

open InversionSeq207Append InversionSeq207RightStructure
open InversionSeq207RightChildren InversionSeq207RightReduction InversionSeq207Counting
open D5.S3.Combinatorics.Nonnesting

noncomputable def rightState (word : List ℕ) : RightType × ℕ × ℕ := by
  classical
  let maximum := word.toFinset.sup id
  let second := secondLargest word
  let banned (value : ℕ) := ∃ top bottom : ℕ,
    top < bottom ∧ bottom < word.length ∧
      word.getD top 0 = value ∧ word.getD bottom 0 < word.getD top 0
  exact (if second = maximum then .diagonal else
    if banned second then .lowerBanned else
    if banned maximum then .upperBanned else .unbanned,
    word.length - maximum, maximum - second)

theorem right_count_correspondence (depth : ℕ) :
    ∀ word : List ℕ,
      word ∈ InversionSeqDefs.avoiders word.length
        [[2, 1, 2], [2, 2, 1], [2, 3, 1], [3, 2, 1]] →
      ({suffix : List ℕ | suffix.length = depth ∧
        word ++ suffix ∈ InversionSeqDefs.avoiders (word.length + depth)
          [[2, 1, 2], [2, 2, 1], [2, 3, 1], [3, 2, 1]]}.ncard : ℤ) =
        rightCount depth (rightState word).1 (rightState word).2.1
          (rightState word).2.2 := by
  classical
  let patterns := [[2, 1, 2], [2, 2, 1], [2, 3, 1], [3, 2, 1]]
  let future (length : ℕ) (word : List ℕ) : ℤ :=
    ({suffix : List ℕ | suffix.length = length ∧
      word ++ suffix ∈ InversionSeqDefs.avoiders (word.length + length) patterns}.ncard : ℤ)
  let banned (word : List ℕ) (value : ℕ) := ∃ top bottom : ℕ,
    top < bottom ∧ bottom < word.length ∧
      word.getD top 0 = value ∧ word.getD bottom 0 < word.getD top 0
  have hprefix (word suffix : List ℕ)
      (hfull : word ++ suffix ∈
        InversionSeqDefs.avoiders (word.length + suffix.length) patterns) :
      word ∈ InversionSeqDefs.avoiders word.length patterns := by
    refine ⟨rfl, ?_, ?_⟩
    · intro index hindex
      have hbound := hfull.2.1 index (by simp; omega)
      simpa only [List.getD_append word suffix 0 index hindex] using hbound
    · intro pattern hpattern hoccurs
      obtain ⟨values, hincreasing, hmem, hsublist, harrows⟩ := hoccurs
      apply hfull.2.2 pattern hpattern
      refine ⟨values, hincreasing, ?_, ?_, ?_⟩
      · intro index hlow hhigh
        exact List.mem_append_left suffix (hmem index hlow hhigh)
      · exact hsublist.trans (List.sublist_append_left word suffix)
      · simp
  have hzero (word : List ℕ)
      (hword : word ∈ InversionSeqDefs.avoiders word.length patterns) :
      future 0 word = 1 := by
    have hset : {suffix : List ℕ | suffix.length = 0 ∧
        word ++ suffix ∈ InversionSeqDefs.avoiders (word.length + 0) patterns} = {[]} := by
      ext suffix
      simp only [Set.mem_ofPred_eq, List.length_eq_zero_iff, Set.mem_singleton_iff]
      constructor
      · exact And.left
      · rintro rfl
        simpa using hword
    change (({suffix : List ℕ | suffix.length = 0 ∧
      word ++ suffix ∈ InversionSeqDefs.avoiders (word.length + 0) patterns}).ncard : ℤ) = 1
    rw [hset]
    simp
  induction depth with
  | zero =>
      intro word hword
      change future 0 word = _
      rw [hzero word hword]
      rfl
  | succ depth inductionHyp =>
      intro word hword
      have hstep : future (depth + 1) word =
          ∑ value ∈ Finset.range (word.length + 1), future depth (word ++ [value]) := by
        unfold future
        exact_mod_cast continuation_card_succ patterns word depth
      have hchild (value : ℕ) : future depth (word ++ [value]) =
          if word ++ [value] ∈ InversionSeqDefs.avoiders (word.length + 1) patterns then
            rightCount depth (rightState (word ++ [value])).1
              (rightState (word ++ [value])).2.1 (rightState (word ++ [value])).2.2
          else 0 := by
        split_ifs with hvalid
        · exact inductionHyp _ (by simpa using hvalid)
        · have hset : {suffix : List ℕ | suffix.length = depth ∧
              (word ++ [value]) ++ suffix ∈
                InversionSeqDefs.avoiders ((word ++ [value]).length + depth) patterns} = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro suffix hsuffix
            apply hvalid
            simpa using hprefix (word ++ [value]) suffix
              (by simpa [hsuffix.1] using hsuffix.2)
          change (({suffix : List ℕ | suffix.length = depth ∧
            (word ++ [value]) ++ suffix ∈
              InversionSeqDefs.avoiders ((word ++ [value]).length + depth) patterns}).ncard : ℤ)
            = 0
          rw [hset]
          simp
      change future (depth + 1) word = _
      by_cases hempty : word = []
      · subst word
        rw [hstep]
        simp only [List.length_nil, zero_add, Finset.sum_range_one]
        rw [hchild 0]
        have hvalid : [0] ∈ InversionSeqDefs.avoiders 1 patterns := by
          apply (right_append_iff [] 0 hword).mpr
          simp [secondLargest]
        simp only [List.nil_append, List.length_nil, hvalid, if_true]
        have hstates : rightState [] = (.diagonal, 0, 0) ∧
            rightState [0] = (.diagonal, 1, 0) := by
          simp [rightState, secondLargest]
        rw [hstates.1, hstates.2]
        simp [rightCount]
      · let maximum := word.toFinset.sup id
        let second := secondLargest word
        have hnonempty : word.toFinset.Nonempty := by simpa using hempty
        obtain ⟨entry, hentry, hentryMax⟩ :=
          Finset.exists_mem_eq_sup word.toFinset hnonempty id
        obtain ⟨maximumIndex, hmaximumIndex, hgetMaximum⟩ :=
          List.mem_iff_getElem.mp (List.mem_toFinset.mp hentry)
        have hmaximumValue : word.getD maximumIndex 0 = maximum := by
          simpa [List.getD, hmaximumIndex, maximum, hentryMax] using hgetMaximum
        have hmaximum (index : ℕ) (hindex : index < word.length) :
            word.getD index 0 ≤ word.getD maximumIndex 0 := by
          rw [hmaximumValue]
          apply Finset.le_sup (f := id)
          exact List.mem_toFinset.mpr (by simp [hindex])
        have hmaxBound : maximum ≤ word.length := by
          have := hword.2.1 maximumIndex hmaximumIndex
          rw [hmaximumValue] at this
          omega
        have hsecondBound : second ≤ maximum := by
          simp only [second, secondLargest, Finset.sup_le_iff, Finset.mem_range]
          intro later hlater earlier hearlier
          exact le_trans (min_le_right _ _) ((hmaximum later hlater).trans_eq hmaximumValue)
        have hclassification :=
          right_descent_classification word hword maximumIndex hmaximumIndex hmaximum
        have hbanBound (value : ℕ) (hban : banned word value) : value ≤ maximum := by
          obtain ⟨top, bottom, htop, hbottom, heq, hdrop⟩ := hban
          have := hmaximum top (by omega)
          rwa [heq, hmaximumValue] at this
        have hdiagonal : second = maximum → ¬ banned word maximum := by
          intro heq hban
          obtain ⟨top, bottom, htop, hbottom, hvalue, hdrop⟩ := hban
          have := hclassification.2.1 top bottom htop hbottom hdrop
            (by simpa [second, heq] using hvalue.ge)
          rw [hmaximumValue] at this
          omega
        have hnotBoth : ¬ (banned word second ∧ banned word maximum) := by
          have := hclassification.2.2
          rw [hmaximumValue] at this
          exact this
        have hactive (value : ℕ) :
            word ++ [value] ∈ InversionSeqDefs.avoiders (word.length + 1) patterns ↔
              second ≤ value ∧ value ≤ word.length ∧ ¬ banned word value := by
          rw [right_append_iff word value hword]
          constructor
          · rintro ⟨hlow, hhigh, hdescent⟩
            refine ⟨hlow, hhigh, ?_⟩
            rintro ⟨top, bottom, htop, hbottom, heq, hdrop⟩
            exact hdescent top bottom htop hbottom hdrop heq
          · rintro ⟨hlow, hhigh, hnot⟩
            refine ⟨hlow, hhigh, ?_⟩
            intro top bottom htop hbottom hdrop heq
            exact hnot ⟨top, bottom, htop, hbottom, heq, hdrop⟩
        have hbanEndpoint (value : ℕ) (hvalue : second ≤ value) :
            banned word value ↔
              (value = second ∧ banned word second) ∨
              (value = maximum ∧ banned word maximum) := by
          constructor
          · intro hban
            obtain ⟨top, bottom, htop, hbottom, heq, hdrop⟩ := hban
            have hends := hclassification.2.1 top bottom htop hbottom hdrop
              (by change second ≤ word.getD top 0; rwa [heq])
            rcases hends.2 with hlower | hupper
            · exact Or.inl ⟨heq.symm.trans hlower,
                ⟨top, bottom, htop, hbottom, hlower, hdrop⟩⟩
            · have hsame : value = maximum := heq.symm.trans
                (hupper.trans hmaximumValue)
              exact Or.inr ⟨hsame,
                ⟨top, bottom, htop, hbottom, heq.trans hsame, hdrop⟩⟩
          · rintro (⟨rfl, hban⟩ | ⟨rfl, hban⟩) <;> exact hban
        have hupdate (value : ℕ)
            (hvalid : word ++ [value] ∈
              InversionSeqDefs.avoiders (word.length + 1) patterns) :
            rightState (word ++ [value]) =
              (if value < maximum then .upperBanned else
                if maximum < value then
                  if banned word maximum then .lowerBanned else .unbanned
                else .diagonal,
                word.length + 1 - max maximum value, max maximum value - min maximum value) := by
          have hlegal := (hactive value).mp hvalid
          have hsecondUpdate := (right_children_exact word value maximumIndex hword hvalid
            hmaximumIndex hmaximum).1
          rw [hmaximumValue] at hsecondUpdate
          have hmaxUpdate : (word ++ [value]).toFinset.sup id = max maximum value := by
            simp [List.toFinset_append, maximum, Finset.sup_insert,
              max_comm]
          have hget (index : ℕ) (hindex : index < word.length) :
              (word ++ [value]).getD index 0 = word.getD index 0 :=
            List.getD_append word [value] 0 index hindex
          have hlast : (word ++ [value]).getD word.length 0 = value := by
            rw [List.getD_append_right _ _ _ _ le_rfl]
            simp
          have hbanUpdate (candidate : ℕ) : banned (word ++ [value]) candidate ↔
              banned word candidate ∨ (candidate = maximum ∧ value < maximum) := by
            constructor
            · rintro ⟨top, bottom, htop, hbottom, heq, hdrop⟩
              have htoplen : top < word.length := by simp at hbottom; omega
              rw [hget top htoplen] at heq hdrop
              by_cases hbottomlen : bottom < word.length
              · rw [hget bottom hbottomlen] at hdrop
                exact Or.inl ⟨top, bottom, htop, hbottomlen, heq, hdrop⟩
              · have hbottomEq : bottom = word.length := by simp at hbottom; omega
                subst bottom
                rw [hlast] at hdrop
                rcases hclassification.1 top htoplen with hsmall | hmax
                · have : second ≤ value := hlegal.1
                  change word.getD top 0 ≤ second at hsmall
                  omega
                · rw [hmaximumValue] at hmax
                  exact Or.inr ⟨heq.symm.trans hmax, by omega⟩
            · rintro (hban | ⟨rfl, hlow⟩)
              · obtain ⟨top, bottom, htop, hbottom, heq, hdrop⟩ := hban
                exact ⟨top, bottom, htop, by simp; omega,
                  by rwa [hget top (by omega)],
                  by rwa [hget bottom hbottom, hget top (by omega)]⟩
              · exact ⟨maximumIndex, word.length, hmaximumIndex, by simp,
                  by rw [hget maximumIndex hmaximumIndex, hmaximumValue],
                  by rw [hlast, hget maximumIndex hmaximumIndex, hmaximumValue]; exact hlow⟩
          unfold rightState
          simp only [hsecondUpdate, hmaxUpdate]
          change (if min maximum value = max maximum value then _ else
            if banned (word ++ [value]) (min maximum value) then _ else
            if banned (word ++ [value]) (max maximum value) then _ else _, _, _) = _
          by_cases hlow : value < maximum
          · have hnot : ¬ banned (word ++ [value]) value := by
              rw [hbanUpdate]
              exact not_or.mpr ⟨hlegal.2.2, by omega⟩
            have hyes : banned (word ++ [value]) maximum :=
              (hbanUpdate maximum).mpr (Or.inr ⟨rfl, hlow⟩)
            simp [List.length_append, min_eq_right hlow.le, max_eq_left hlow.le,
              hlow, hnot, hyes,
              Nat.ne_of_lt hlow]
          · by_cases hhigh : maximum < value
            · have hnot : ¬ banned (word ++ [value]) value := by
                rw [hbanUpdate]
                exact not_or.mpr
                  ⟨fun hban => (not_le_of_gt hhigh) (hbanBound value hban), by omega⟩
              have hsame : banned (word ++ [value]) maximum ↔ banned word maximum := by
                rw [hbanUpdate]
                simp [hlow]
              simp [List.length_append, min_eq_left hhigh.le, max_eq_right hhigh.le,
                hlow, hhigh, hnot,
                hsame, Nat.ne_of_lt hhigh]
            · have heq : value = maximum := by omega
              simp [List.length_append, heq]
        let coefficient (value : ℕ) : ℤ :=
          if word ++ [value] ∈ InversionSeqDefs.avoiders (word.length + 1) patterns then
            rightCount depth (rightState (word ++ [value])).1
              (rightState (word ++ [value])).2.1 (rightState (word ++ [value])).2.2
          else 0
        let reserve := word.length - maximum
        let gap := maximum - second
        have hbelow (value : ℕ) (hvalue : value < second) : coefficient value = 0 := by
          have hnot : word ++ [value] ∉
              InversionSeqDefs.avoiders (word.length + 1) patterns := by
            intro hvalid
            have := (hactive value).mp hvalid
            omega
          simp [coefficient, hnot]
        have hmiddle (offset : ℕ) (hoffset : offset < gap) :
            coefficient (second + offset) =
              if offset = 0 ∧ banned word second then 0 else
                rightCount depth .upperBanned (reserve + 1) (gap - offset) := by
          have hlow : second + offset < maximum := by dsimp [gap] at hoffset; omega
          have hbound : second + offset ≤ word.length := by omega
          have hban : banned word (second + offset) ↔ offset = 0 ∧ banned word second := by
            rw [hbanEndpoint _ (by omega)]
            constructor
            · rintro (⟨heq, hban⟩ | ⟨heq, hban⟩)
              · exact ⟨by omega, hban⟩
              · omega
            · rintro ⟨rfl, hban⟩
              exact Or.inl ⟨by omega, hban⟩
          by_cases hbanned : offset = 0 ∧ banned word second
          · have hnot : word ++ [second + offset] ∉
                InversionSeqDefs.avoiders (word.length + 1) patterns := by
              intro hvalid
              exact ((hactive _).mp hvalid).2.2 (hban.mpr hbanned)
            unfold coefficient
            rw [if_neg hnot, if_pos hbanned]
          · have hvalid : word ++ [second + offset] ∈
                InversionSeqDefs.avoiders (word.length + 1) patterns :=
              (hactive _).mpr ⟨by omega, hbound, fun hyes => hbanned (hban.mp hyes)⟩
            have hstate := hupdate (second + offset) hvalid
            simp only [hlow, if_true, max_eq_left hlow.le, min_eq_right hlow.le] at hstate
            have hreserve : word.length + 1 - maximum = reserve + 1 := by
              dsimp [reserve]; omega
            have hgap : maximum - (second + offset) = gap - offset := by
              dsimp [gap]; omega
            simp [coefficient, hvalid, hbanned, hstate, hreserve, hgap]
        have hmaxTerm : coefficient maximum =
            if banned word maximum then 0 else rightCount depth .diagonal (reserve + 1) 0 := by
          by_cases hban : banned word maximum
          · have hnot : word ++ [maximum] ∉
                InversionSeqDefs.avoiders (word.length + 1) patterns := by
              intro hvalid
              exact ((hactive _).mp hvalid).2.2 hban
            simp [coefficient, hnot, hban]
          · have hvalid : word ++ [maximum] ∈
                InversionSeqDefs.avoiders (word.length + 1) patterns :=
              (hactive _).mpr ⟨hsecondBound, hmaxBound, hban⟩
            have hstate := hupdate maximum hvalid
            have hreserve : word.length + 1 - maximum = reserve + 1 := by
              dsimp [reserve]; omega
            simp [coefficient, hvalid, hban, hstate, hreserve]
        have hhighTerm (offset : ℕ) (hoffset : offset < reserve) :
            coefficient (maximum + 1 + offset) =
              rightCount depth (if banned word maximum then .lowerBanned else .unbanned)
                (reserve - offset) (offset + 1) := by
          have hhigh : maximum < maximum + 1 + offset := by omega
          have hbound : maximum + 1 + offset ≤ word.length := by
            dsimp [reserve] at hoffset; omega
          have hban : ¬ banned word (maximum + 1 + offset) := by
            intro hyes
            have := hbanBound _ hyes
            omega
          have hvalid : word ++ [maximum + 1 + offset] ∈
              InversionSeqDefs.avoiders (word.length + 1) patterns :=
            (hactive _).mpr ⟨by omega, hbound, hban⟩
          have hstate := hupdate (maximum + 1 + offset) hvalid
          simp only [not_lt_of_ge hhigh.le, if_false, hhigh, if_true,
            max_eq_right hhigh.le, min_eq_left hhigh.le] at hstate
          have hreserve : word.length + 1 - (maximum + 1 + offset) = reserve - offset := by
            dsimp [reserve]; omega
          have hgap : maximum + 1 + offset - maximum = offset + 1 := by omega
          simp [coefficient, hvalid, hstate, hreserve, hgap]
        have hlowSum : (∑ value ∈ Finset.range maximum, coefficient value) =
            if banned word second then
              ∑ distance ∈ Finset.range (gap - 1),
                rightCount depth .upperBanned (reserve + 1) (distance + 1)
            else ∑ distance ∈ Finset.range gap,
              rightCount depth .upperBanned (reserve + 1) (distance + 1) := by
          have hsplit : maximum = second + gap := by dsimp [gap]; omega
          rw [hsplit, Finset.sum_range_add]
          have hsmall : (∑ value ∈ Finset.range second, coefficient value) = 0 := by
            apply Finset.sum_eq_zero
            intro value hvalue
            exact hbelow value (Finset.mem_range.mp hvalue)
          rw [hsmall, zero_add]
          have hmid : (∑ offset ∈ Finset.range gap, coefficient (second + offset)) =
              ∑ offset ∈ Finset.range gap,
                if offset = 0 ∧ banned word second then 0 else
                  rightCount depth .upperBanned (reserve + 1) (gap - offset) := by
            apply Finset.sum_congr rfl
            intro offset hoffset
            exact hmiddle offset (Finset.mem_range.mp hoffset)
          rw [hmid, ← Finset.sum_range_reflect]
          by_cases hban : banned word second
          · have hpositive : 0 < gap := by
              by_contra hnot
              have heq : second = maximum := by dsimp [gap] at hnot; omega
              exact hdiagonal heq (by rwa [← heq])
            obtain ⟨rest, hrest⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : gap ≠ 0)
            rw [hrest, Finset.sum_range_succ]
            simp only [hban, and_true, if_true]
            have hterms : (∑ distance ∈ Finset.range rest,
                if rest - distance = 0 then 0 else
                  rightCount depth .upperBanned (reserve + 1)
                    (rest + 1 - (rest - distance))) =
                ∑ distance ∈ Finset.range rest,
                  rightCount depth .upperBanned (reserve + 1) (distance + 1) := by
              apply Finset.sum_congr rfl
              intro distance hdistance
              have hlt := Finset.mem_range.mp hdistance
              have hnonzero : rest - distance ≠ 0 := by omega
              have heq : rest + 1 - (rest - distance) = distance + 1 := by omega
              simp [hnonzero, heq]
            simp [hterms]
          · simp only [hban, and_false, if_false]
            apply Finset.sum_congr rfl
            intro distance hdistance
            have hlt := Finset.mem_range.mp hdistance
            have heq : gap - (gap - 1 - distance) = distance + 1 := by omega
            rw [heq]
        have hhighSum : (∑ offset ∈ Finset.range reserve,
            coefficient (maximum + 1 + offset)) =
            ∑ distance ∈ Finset.range reserve,
              rightCount depth (if banned word maximum then .lowerBanned else .unbanned)
                (reserve - distance) (distance + 1) := by
          apply Finset.sum_congr rfl
          intro distance hdistance
          exact hhighTerm distance (Finset.mem_range.mp hdistance)
        have htotal : (∑ value ∈ Finset.range (word.length + 1), coefficient value) =
            (∑ value ∈ Finset.range maximum, coefficient value) + coefficient maximum +
              ∑ offset ∈ Finset.range reserve, coefficient (maximum + 1 + offset) := by
          have hsplit : word.length + 1 = (maximum + 1) + reserve := by
            dsimp [reserve]; omega
          rw [hsplit, Finset.sum_range_add, Finset.sum_range_succ]
        rw [hstep]
        change (∑ value ∈ Finset.range (word.length + 1), future depth (word ++ [value])) = _
        simp_rw [hchild]
        change (∑ value ∈ Finset.range (word.length + 1), coefficient value) = _
        rw [htotal, hlowSum, hmaxTerm, hhighSum]
        change _ = rightCount (depth + 1)
          (if second = maximum then .diagonal else
            if banned word second then .lowerBanned else
            if banned word maximum then .upperBanned else .unbanned) reserve gap
        by_cases hdiag : second = maximum
        · have hbanMax := hdiagonal hdiag
          have hgap : gap = 0 := by dsimp [gap]; omega
          simp [hdiag, hbanMax, hgap, rightCount]
        · by_cases hbanSecond : banned word second
          · have hbanMax : ¬ banned word maximum := fun hban => hnotBoth ⟨hbanSecond, hban⟩
            simp [hdiag, hbanSecond, hbanMax, rightCount]
            ring
          · by_cases hbanMax : banned word maximum
            · simp [hdiag, hbanSecond, hbanMax, rightCount]
            · simp [hdiag, hbanSecond, hbanMax, rightCount]
              ring

end D5.S3.Combinatorics.InversionSeq.InversionSeq207RightCounting
