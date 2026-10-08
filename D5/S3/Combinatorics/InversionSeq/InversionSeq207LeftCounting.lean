/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207LeftCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207LeftCounting
   mirror-E: none(waiver:left-labelled-continuation-counting)
   anchors: []
   utility: none
   digest: Ordered child matching and depth induction count actual left continuations. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftChildren
import D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftTree
import D5.S3.Combinatorics.InversionSeq.InversionSeq207Counting

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftCounting

open InversionSeq207Append InversionSeq207LeftChildren InversionSeq207LeftTree
open InversionSeq207Counting D5.S3.Combinatorics.Nonnesting

noncomputable def leftState (word : List ℕ) (maximum : ℕ) : List Bool × ℕ × Bool := by
  classical
  let active (value : ℕ) := word ++ [value] ∈ InversionSeqDefs.avoiders (word.length + 1)
    [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]
  exact (((List.range (maximum + 1)).filter (fun value => decide (active value))).map
    (fun value => decide (value ∈ word)), word.length - maximum, decide (active maximum))

theorem left_count_correspondence (depth : ℕ) :
    ∀ (word : List ℕ) (maximumIndex : ℕ),
      word ∈ InversionSeqDefs.avoiders word.length
        [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]] →
      maximumIndex < word.length →
      (∀ index < word.length, word.getD index 0 ≤ word.getD maximumIndex 0) →
      {suffix : List ℕ | suffix.length = depth ∧
        word ++ suffix ∈ InversionSeqDefs.avoiders (word.length + depth)
          [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]}.ncard =
        leftCount depth (leftState word (word.getD maximumIndex 0)).1
          (leftState word (word.getD maximumIndex 0)).2.1
          (leftState word (word.getD maximumIndex 0)).2.2 := by
  classical
  have hchildMatching (word : List ℕ) (maximumIndex : ℕ)
      (hword : word ∈ InversionSeqDefs.avoiders word.length
        [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]])
      (hmaximumIndex : maximumIndex < word.length)
      (hmaximum : ∀ index < word.length,
        word.getD index 0 ≤ word.getD maximumIndex 0) :
      ∃ choices : List ℕ, choices.Nodup ∧
        (∀ value, value ∈ choices ↔
          word ++ [value] ∈ InversionSeqDefs.avoiders (word.length + 1)
            [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]) ∧
        choices.length = (leftState word (word.getD maximumIndex 0)).1.length +
          (leftState word (word.getD maximumIndex 0)).2.1 ∧
        ∀ index (hindex : index < choices.length),
          leftState (word ++ [choices[index]])
            (max (word.getD maximumIndex 0) choices[index]) =
          leftChild (leftState word (word.getD maximumIndex 0)).1
            (leftState word (word.getD maximumIndex 0)).2.1
            (leftState word (word.getD maximumIndex 0)).2.2 index := by
    classical
    let patterns := [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]
    let maximum := word.getD maximumIndex 0
    let active (value : ℕ) :=
      word ++ [value] ∈ InversionSeqDefs.avoiders (word.length + 1) patterns
    let low := (List.range (maximum + 1)).filter (fun value => decide (active value))
    let used (value : ℕ) := decide (value ∈ word)
    let bits := low.map used
    have hbitsLength : bits.length = low.length := by simp [bits]
    let reserve := word.length - maximum
    let choices := low ++ (List.range reserve).map (fun distance => maximum + 1 + distance)
    have hmaxBound : maximum < word.length := by
      have := hword.2.1 maximumIndex hmaximumIndex
      change maximum ≤ maximumIndex at this
      omega
    have hmaxmem : maximum ∈ word := by
      simp [maximum, hmaximumIndex]
    have hmemBound (value : ℕ) (hvalue : value ∈ word) : value ≤ maximum := by
      obtain ⟨index, hindex, heq⟩ := List.mem_iff_getElem.mp hvalue
      have := hmaximum index hindex
      simpa [maximum, List.getD, hindex, heq] using this
    have hceiling : repeatedCeiling word ≤ maximum := by
      simp only [repeatedCeiling, Finset.sup_le_iff, Finset.mem_range]
      intro later hlater earlier hearlier
      split_ifs
      · exact hmaximum later hlater
      · exact Nat.zero_le _
    have hhigh (value : ℕ) (hlarge : maximum < value) :
        active value ↔ value ≤ word.length := by
      change (word ++ [value] ∈ InversionSeqDefs.avoiders (word.length + 1) patterns) ↔ _
      rw [left_append_iff word value hword]
      constructor
      · exact fun h => h.2.1
      · intro hbound
        refine ⟨by omega, hbound, ?_⟩
        intro first second hfirst hsecond hdrop
        right
        have := hmaximum first (by omega)
        change word.getD first 0 ≤ maximum at this
        omega
    have hlowMem (value : ℕ) : value ∈ low ↔ value ≤ maximum ∧ active value := by
      simp [low]
    have hchoicesMem (value : ℕ) : value ∈ choices ↔ active value := by
      simp only [choices, List.mem_append, List.mem_map, List.mem_range, hlowMem]
      constructor
      · rintro (hlow | ⟨distance, hdistance, rfl⟩)
        · exact hlow.2
        · exact (hhigh _ (by omega)).mpr (by dsimp [reserve] at hdistance; omega)
      · intro hvalue
        by_cases hsmall : value ≤ maximum
        · exact Or.inl ⟨hsmall, hvalue⟩
        · have hbound := (hhigh value (by omega)).mp hvalue
          exact Or.inr ⟨value - (maximum + 1), by dsimp [reserve]; omega, by omega⟩
    have hsorted : low.Pairwise (· < ·) := List.pairwise_lt_range.filter _
    have hchoicesSorted : choices.Pairwise (· < ·) := by
      apply List.pairwise_append.mpr
      refine ⟨hsorted, ?_, ?_⟩
      · apply List.pairwise_iff_getElem.mpr
        intro first second hfirst hsecond hlt
        simp only [List.length_map, List.length_range] at hfirst hsecond
        simp only [List.getElem_map, List.getElem_range]
        omega
      · intro first hfirst second hsecond
        have hfirstBound := (hlowMem first).mp hfirst
        obtain ⟨distance, _, rfl⟩ := List.mem_map.mp hsecond
        omega
    have hstate : leftState word maximum = (bits, reserve, decide (active maximum)) := rfl
    have hlength : choices.length = bits.length + reserve := by
      simp [choices, bits]
    have htake (entries : List ℕ) (hsorted : entries.Pairwise (· < ·))
        (index : ℕ) (hindex : index < entries.length) :
        entries.filter (fun value => decide (value < entries[index])) = entries.take index := by
      induction entries generalizing index with
      | nil => simp at hindex
      | cons first rest ih =>
          obtain ⟨hfirst, hrest⟩ := List.pairwise_cons.mp hsorted
          cases index with
          | zero =>
              simp only [List.getElem_cons_zero, List.filter_cons, lt_self_iff_false,
                decide_false, Bool.false_eq_true, ↓reduceIte, List.take_zero]
              apply List.filter_eq_nil_iff.mpr
              intro value hvalue
              have := hfirst value hvalue
              simp; omega
          | succ index =>
              have hindexRest : index < rest.length := by simpa using hindex
              have hfirstLt := hfirst rest[index] (List.getElem_mem hindexRest)
              simpa [hfirstLt, List.take_succ_cons] using
                congrArg (List.cons first) (ih hrest index hindexRest)
    refine ⟨choices, hchoicesSorted.imp (fun hlt => Nat.ne_of_lt hlt),
      hchoicesMem, ?_, ?_⟩
    · change choices.length = (leftState word maximum).1.length +
        (leftState word maximum).2.1
      rw [hstate]
      exact hlength
    intro index hindex
    let value := choices[index]
    have hvalid : active value := (hchoicesMem value).mp (List.getElem_mem hindex)
    have hupdate := (left_children_exact word value maximumIndex hword hvalid
      hmaximumIndex hmaximum).2
    let nextActive (candidate : ℕ) :=
      (word ++ [value]) ++ [candidate] ∈
        InversionSeqDefs.avoiders (word.length + 2) patterns
    have hnext (candidate : ℕ) : nextActive candidate ↔ candidate ≤ word.length + 1 ∧
        ((value < maximum ∧ (maximum < candidate ∨
          (candidate < value ∧ value ∉ word ∧ active candidate))) ∨
        (value = maximum ∧ value ≤ candidate) ∨
        (maximum < value ∧ (candidate ≤ maximum → active candidate))) := hupdate candidate
    have hstateNext : leftState (word ++ [value]) (max maximum value) =
        ((((List.range (max maximum value + 1)).filter
          (fun candidate => decide (nextActive candidate))).map
            (fun candidate => decide (candidate ∈ word ++ [value]))),
          word.length + 1 - max maximum value, decide (nextActive (max maximum value))) := by
      simp only [leftState, List.length_append, List.length_singleton]
      rfl
    rw [show choices[index] = value from rfl, hstateNext, hstate]
    by_cases hlow : index < low.length
    · have hvalue : value = low[index] := by
        dsimp [value, choices]
        exact List.getElem_append_left hlow
      have hsmall : value ≤ maximum := ((hlowMem value).mp
        (hvalue ▸ List.getElem_mem hlow)).1
      have hbit : bits.getD index false = used value := by
        simp [bits, List.getD, hlow, hvalue]
      have hmaxEq : max maximum value = maximum := max_eq_left hsmall
      have hlast : active maximum ∧ index + 1 = low.length ↔ value = maximum := by
        constructor
        · rintro ⟨hactiveMax, hlast⟩
          obtain ⟨lastIndex, hlastIndex, heq⟩ := List.mem_iff_getElem.mp
            ((hlowMem maximum).mpr ⟨le_rfl, hactiveMax⟩)
          have horder := List.pairwise_iff_getElem.mp hsorted
          by_cases hequal : lastIndex = index
          · simpa [hequal, hvalue] using heq
          · have hlt : lastIndex < index := by omega
            have := horder lastIndex index hlastIndex hlow hlt
            rw [heq, ← hvalue] at this
            omega
        · intro heq
          refine ⟨by simpa [heq] using hvalid, ?_⟩
          by_contra hnotLast
          have hnextIndex : index + 1 < low.length := by omega
          have hnextBound := ((hlowMem low[index + 1]).mp (List.getElem_mem hnextIndex)).1
          have := List.pairwise_iff_getElem.mp hsorted index (index + 1) hlow
            hnextIndex (by omega)
          rw [← hvalue, heq] at this
          omega
      simp only [leftChild, hbitsLength, hlow, if_true, hbit]
      by_cases hused : value ∈ word
      · simp only [used, hused, decide_true, if_true]
        by_cases heq : value = maximum
        · have hflag : (decide (active maximum) && decide (index + 1 = low.length)) = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            exact hlast.mpr heq
          rw [hflag]
          simp only [if_true, hmaxEq]
          have hfilter : (List.range (maximum + 1)).filter
              (fun candidate => decide (nextActive candidate)) = [maximum] := by
            rw [List.range_succ, List.filter_append]
            have hnone : (List.range maximum).filter
                (fun candidate => decide (nextActive candidate)) = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro candidate hc
              have hcBound := List.mem_range.mp hc
              simp only [decide_eq_true_eq]
              rw [hnext, heq]
              omega
            have hactiveMax : nextActive maximum := by rw [hnext, heq]; omega
            simp [hnone, hactiveMax]
          have hactiveMax : nextActive maximum := by rw [hnext, heq]; omega
          have hreserve : word.length + 1 - maximum = reserve + 1 := by
            dsimp [reserve]
            omega
          simp [hfilter, hactiveMax, hmaxmem, hreserve]
        · have hlt : value < maximum := by omega
          have hflag : (decide (active maximum) && decide (index + 1 = low.length)) = false := by
            by_cases ha : active maximum
            · have hn : index + 1 ≠ low.length := fun hl => heq (hlast.mp ⟨ha, hl⟩)
              simp [hn]
            · simp [ha]
          rw [hflag]
          simp only [Bool.false_eq_true, if_false, hmaxEq]
          have hfilter : (List.range (maximum + 1)).filter
              (fun candidate => decide (nextActive candidate)) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro candidate hc
            have hcBound := List.mem_range.mp hc
            simp only [decide_eq_true_eq]
            rw [hnext]
            have hcLe : candidate ≤ maximum := by omega
            simp [hused, hlt, Nat.ne_of_lt hlt, Nat.not_lt_of_ge hsmall,
              Nat.not_lt_of_ge hcLe]
          have hnotMax : ¬ nextActive maximum := by
            rw [hnext]
            simp [hlt, hused, Nat.ne_of_lt hlt, Nat.not_lt_of_ge hsmall]
          have hreserve : word.length + 1 - maximum = reserve + 1 := by
            dsimp [reserve]
            omega
          simp [hfilter, hnotMax, hreserve]
      · have hlt : value < maximum := by
          by_contra hnotLt
          have : value = maximum := by omega
          exact hused (this ▸ hmaxmem)
        simp only [used, hused, decide_false, Bool.false_eq_true, ↓reduceIte, hmaxEq]
        have hfilter : (List.range (maximum + 1)).filter
            (fun candidate => decide (nextActive candidate)) = low.take index := by
          have hpred : (List.range (maximum + 1)).filter
                (fun candidate => decide (nextActive candidate)) =
                ((List.range (maximum + 1)).filter
                  (fun candidate => decide (active candidate))).filter
                    (fun candidate => decide (candidate < value)) := by
              rw [List.filter_filter]
              apply List.filter_congr
              intro candidate hc
              have hcBound := List.mem_range.mp hc
              apply Bool.eq_iff_iff.mpr
              simp only [decide_eq_true_eq, Bool.and_eq_true]
              rw [hnext]
              have hcLe : candidate ≤ maximum := by omega
              have hcWord : candidate ≤ word.length + 1 := by omega
              simp only [hcWord, hlt, hused, hcLe, Nat.not_lt_of_ge hcLe,
                Nat.ne_of_lt hlt, Nat.not_lt_of_ge hsmall, true_and, false_and,
                false_or, or_false]
              tauto
          rw [hpred]
          simpa only [hvalue] using htake low hsorted index hlow
        have hmap : (low.take index).map
            (fun candidate => decide (candidate ∈ word ++ [value])) =
            (low.take index).map used := by
          apply List.map_congr_left
          intro candidate hc
          have hcFilter : candidate ∈ low.filter (fun entry => decide (entry < value)) := by
            rwa [hvalue, htake low hsorted index hlow]
          have hcLt : candidate < value := by simpa using (List.mem_filter.mp hcFilter).2
          simp [used, ne_of_lt hcLt]
        have hnotMax : ¬ nextActive maximum := by rw [hnext]; omega
        rw [hfilter, hmap, List.map_take]
        simp only [hnotMax, decide_false]
        have hreserve : word.length + 1 - maximum = reserve + 1 := by
          dsimp [reserve]
          omega
        exact congrArg (fun capacity => ((low.map used).take index, capacity, false)) hreserve
    · have hhighIndex : index - low.length < reserve := by
        rw [hlength, hbitsLength] at hindex
        omega
      have hvalue : value = maximum + 1 + (index - low.length) := by
        simp [value, choices, List.getElem_append_right (Nat.le_of_not_gt hlow)]
      have hlarge : maximum < value := by omega
      have hbound : value ≤ word.length := (hhigh value hlarge).mp hvalid
      have hmaxEq : max maximum value = value := max_eq_right (by omega)
      simp only [leftChild, hbitsLength, hlow, if_false, hmaxEq]
      have hsplit : value = maximum + 1 + (index - low.length) := hvalue
      have hfilter : (List.range (value + 1)).filter
          (fun candidate => decide (nextActive candidate)) =
          low ++ (List.range (index - low.length)).map (maximum + 1 + ·) ++ [value] := by
        have hrange : List.range value = List.range (maximum + 1) ++
            (List.range (index - low.length)).map (maximum + 1 + ·) := by
          rw [hsplit, List.range_add]
        rw [List.range_succ, hrange, List.filter_append, List.filter_append]
        have hlowFilter : (List.range (maximum + 1)).filter
            (fun candidate => decide (nextActive candidate)) = low := by
          apply List.filter_congr
          intro candidate hc
          have hcBound := List.mem_range.mp hc
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq]
          rw [hnext]
          have hcLe : candidate ≤ maximum := by omega
          have hcWord : candidate ≤ word.length + 1 := by omega
          simp [hlarge, Nat.not_lt_of_ge (Nat.le_of_lt hlarge),
            Nat.ne_of_gt hlarge, hcLe, hcWord]
        have hhighFilter : ((List.range (index - low.length)).map (maximum + 1 + ·)).filter
            (fun candidate => decide (nextActive candidate)) =
            (List.range (index - low.length)).map (maximum + 1 + ·) := by
          apply List.filter_eq_self.mpr
          intro candidate hc
          obtain ⟨distance, hdistance, rfl⟩ := List.mem_map.mp hc
          have hd := List.mem_range.mp hdistance
          simp only [decide_eq_true_eq]
          rw [hnext]
          omega
        have hactiveNew : nextActive value := by rw [hnext]; omega
        rw [hlowFilter, hhighFilter]
        simp [hactiveNew]
      have hmapLow : low.map (fun candidate => decide (candidate ∈ word ++ [value])) = bits := by
        apply List.map_congr_left
        intro candidate hc
        have hcBound := ((hlowMem candidate).mp hc).1
        simp [used, show candidate ≠ value by omega]
      have hmapHigh : ((List.range (index - low.length)).map (maximum + 1 + ·)).map
          (fun candidate => decide (candidate ∈ word ++ [value])) =
          List.replicate (index - low.length) false := by
        rw [List.map_map]
        have hnone : (List.range (index - low.length)).map
            (fun distance => decide (maximum + 1 + distance ∈ word ++ [value])) =
            (List.range (index - low.length)).map (fun _ => false) := by
          apply List.map_congr_left
          intro distance hdistance
          have hd := List.mem_range.mp hdistance
          have hnotUsed : maximum + 1 + distance ∉ word := by
            intro hm
            have := hmemBound _ hm
            omega
          simp [hnotUsed, show maximum + 1 + distance ≠ value by omega]
        simpa [Function.comp_def, List.map_const] using hnone
      have hactiveNew : nextActive value := by rw [hnext]; omega
      rw [hfilter, List.map_append, List.map_append, hmapLow, hmapHigh]
      have hreserve : word.length + 1 - value = reserve - (index - low.length) := by
        dsimp [reserve]
        omega
      simp [hactiveNew, hreserve]
  let patterns := [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]
  let future (length : ℕ) (word : List ℕ) : ℕ :=
    {suffix : List ℕ | suffix.length = length ∧
      word ++ suffix ∈ InversionSeqDefs.avoiders (word.length + length) patterns}.ncard
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
  induction depth with
  | zero =>
      intro word maximumIndex hword hmaximumIndex hmaximum
      have hset : {suffix : List ℕ | suffix.length = 0 ∧
          word ++ suffix ∈ InversionSeqDefs.avoiders (word.length + 0) patterns} = {[]} := by
        ext suffix
        simp only [Set.mem_ofPred_eq, List.length_eq_zero_iff, Set.mem_singleton_iff]
        constructor
        · exact And.left
        · rintro rfl
          simpa using hword
      change ({suffix : List ℕ | suffix.length = 0 ∧
        word ++ suffix ∈ InversionSeqDefs.avoiders (word.length + 0) patterns}).ncard = 1
      rw [hset]
      simp
  | succ depth ih =>
      intro word maximumIndex hword hmaximumIndex hmaximum
      let maximum := word.getD maximumIndex 0
      let state := leftState word maximum
      obtain ⟨choices, hnodup, hchoices, hlength, hmatching⟩ :=
        hchildMatching word maximumIndex hword hmaximumIndex hmaximum
      have hstep : future (depth + 1) word =
          ∑ value ∈ Finset.range (word.length + 1), future depth (word ++ [value]) :=
        continuation_card_succ patterns word depth
      have hinvalid (value : ℕ)
          (hbad : word ++ [value] ∉ InversionSeqDefs.avoiders (word.length + 1) patterns) :
          future depth (word ++ [value]) = 0 := by
        have hset : {suffix : List ℕ | suffix.length = depth ∧
            (word ++ [value]) ++ suffix ∈
              InversionSeqDefs.avoiders ((word ++ [value]).length + depth) patterns} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro suffix hsuffix
          apply hbad
          simpa using hprefix (word ++ [value]) suffix
            (by simpa [hsuffix.1] using hsuffix.2)
        change ({suffix : List ℕ | suffix.length = depth ∧
          (word ++ [value]) ++ suffix ∈
            InversionSeqDefs.avoiders ((word ++ [value]).length + depth) patterns}).ncard = 0
        rw [hset]
        simp
      have hsubset : choices.toFinset ⊆ Finset.range (word.length + 1) := by
        intro value hvalue
        have hvalid := (hchoices value).mp (List.mem_toFinset.mp hvalue)
        have hbound := ((left_append_iff word value hword).mp hvalid).2.1
        simp only [Finset.mem_range]
        omega
      have hsumChoices :
          (∑ value ∈ Finset.range (word.length + 1), future depth (word ++ [value])) =
          ∑ value ∈ choices.toFinset, future depth (word ++ [value]) := by
        symm
        apply Finset.sum_subset hsubset
        intro value _hvalue hnot
        apply hinvalid
        intro hvalid
        exact hnot (List.mem_toFinset.mpr ((hchoices value).mpr hvalid))
      have hsumIndices :
          (∑ index ∈ Finset.range choices.length,
            future depth (word ++ [choices.getD index 0])) =
          ∑ value ∈ choices.toFinset, future depth (word ++ [value]) := by
        apply Finset.sum_bij (fun index _ => choices.getD index 0)
        · intro index hindex
          have hi := Finset.mem_range.mp hindex
          apply List.mem_toFinset.mpr
          simp [List.getD, hi]
        · intro first hfirst second hsecond heq
          have hf := Finset.mem_range.mp hfirst
          have hs := Finset.mem_range.mp hsecond
          have hget : choices[first] = choices[second] := by
            simpa [List.getD, hf, hs] using heq
          exact (List.Nodup.getElem_inj_iff hnodup).mp hget
        · intro value hvalue
          obtain ⟨index, hindex, heq⟩ :=
            List.mem_iff_getElem.mp (List.mem_toFinset.mp hvalue)
          refine ⟨index, Finset.mem_range.mpr hindex, ?_⟩
          simpa [List.getD, hindex] using heq
        · intro index hindex
          rfl
      change future (depth + 1) word = leftCount (depth + 1) state.1 state.2.1 state.2.2
      rw [hstep, hsumChoices, ← hsumIndices]
      simp only [leftCount]
      change (∑ index ∈ Finset.range choices.length,
        future depth (word ++ [choices.getD index 0])) =
        ∑ index ∈ Finset.range (state.1.length + state.2.1),
          let child := leftChild state.1 state.2.1 state.2.2 index
          leftCount depth child.1 child.2.1 child.2.2
      have hlengthState : choices.length = state.1.length + state.2.1 := hlength
      conv_rhs => rw [← hlengthState]
      apply Finset.sum_congr rfl
      intro index hindex
      have hi : index < choices.length := Finset.mem_range.mp hindex
      let value := choices[index]
      have hvalid : word ++ [value] ∈ InversionSeqDefs.avoiders
          (word.length + 1) patterns := (hchoices value).mp (List.getElem_mem hi)
      have hget (position : ℕ) (hposition : position < word.length) :
          (word ++ [value]).getD position 0 = word.getD position 0 :=
        List.getD_append word [value] 0 position hposition
      have hlast : (word ++ [value]).getD word.length 0 = value := by
        rw [List.getD_append_right _ _ _ _ le_rfl]
        simp
      let nextIndex := if maximum < value then word.length else maximumIndex
      have hnextIndex : nextIndex < (word ++ [value]).length := by
        dsimp [nextIndex]
        split_ifs <;> simp only [List.length_append, List.length_singleton] <;> omega
      have hnextValue : (word ++ [value]).getD nextIndex 0 = max maximum value := by
        dsimp [nextIndex]
        split_ifs with hlarge
        · rw [hlast, max_eq_right (by omega)]
        · rw [hget maximumIndex hmaximumIndex, max_eq_left (by omega)]
      have hnextMax (position : ℕ) (hposition : position < (word ++ [value]).length) :
          (word ++ [value]).getD position 0 ≤ (word ++ [value]).getD nextIndex 0 := by
        rw [hnextValue]
        by_cases hold : position < word.length
        · rw [hget position hold]
          exact (hmaximum position hold).trans (le_max_left _ _)
        · have heq : position = word.length := by
            simp only [List.length_append, List.length_singleton] at hposition
            omega
          rw [heq, hlast]
          exact le_max_right _ _
      have hcount := ih (word ++ [value]) nextIndex (by simpa using hvalid)
        hnextIndex hnextMax
      rw [hnextValue] at hcount
      have hmatch : leftState (word ++ [value]) (max maximum value) =
          leftChild state.1 state.2.1 state.2.2 index := hmatching index hi
      rw [hmatch] at hcount
      simpa [future, List.getD, hi, value] using hcount

end D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftCounting
