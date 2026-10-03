/- GID: D5/S3/Combinatorics/PopStack/PopStackIncreasing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackIncreasing
   mirror-E: none(waiver:minimum-increasing-inflation)
   anchors: []
   utility: none
   digest: Increasing inflation of the minimum preserves the nine-pattern avoidance class. -/

import D5.S3.Combinatorics.PopStack.PopStackDecreasing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackIncreasing

open PopStackDefs

theorem increasing_minimum_inflation (before suffix : List ℕ)
    (hbefore : ∀ entry ∈ before, 2 ≤ entry)
    (hsuffix : ∀ entry ∈ suffix, 2 ≤ entry)
    (hclass : InC (before ++ 1 :: suffix)) :
    InC (before.map Nat.succ ++ 1 :: 2 :: suffix.map Nat.succ) := by
  let expanded := before.map Nat.succ ++ 1 :: 2 :: suffix.map Nat.succ
  let contract := fun entry : ℕ => if entry = 1 then 1 else entry - 1
  have hpositive : ∀ entry ∈ expanded, 1 ≤ entry := by
    intro entry hentry
    simp only [expanded, List.mem_append, List.mem_cons, List.mem_map] at hentry
    rcases hentry with ⟨old, _, rfl⟩ | rfl | rfl | ⟨old, _, rfl⟩ <;> omega
  have hwhere : ∀ position entry, expanded[position]? = some entry →
      (entry = 1 ∨ entry = 2) →
      (position = before.length ∧ entry = 1) ∨
        (position = before.length + 1 ∧ entry = 2) := by
    intro position entry hget hentry
    by_cases hleft : position < before.length
    · have hh : entry ∈ before.map Nat.succ := by
        apply List.mem_of_getElem?
        simpa only [expanded, List.getElem?_append_left
          (show position < (before.map Nat.succ).length by simpa using hleft)] using hget
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hh
      have hb := hbefore old hold
      omega
    · have hh : (1 :: 2 :: suffix.map Nat.succ)[position - before.length]? =
          some entry := by
        simpa only [expanded, List.getElem?_append_right
          (show (before.map Nat.succ).length ≤ position by simp; omega), List.length_map]
          using hget
      by_cases hfirst : position = before.length
      · subst position
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hh
        exact Or.inl ⟨rfl, hh.symm⟩
      · by_cases hsecond : position = before.length + 1
        · subst position
          simp only [Nat.add_sub_cancel_left, List.getElem?_cons_succ,
            List.getElem?_cons_zero, Option.some.injEq] at hh
          exact Or.inr ⟨rfl, hh.symm⟩
        · obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le
            (show 2 ≤ position - before.length by omega)
          rw [hoffset, show 2 + offset = offset + 1 + 1 by omega] at hh
          have hs : (suffix.map Nat.succ)[offset]? = some entry := by
            simpa only [List.getElem?_cons_succ] using hh
          obtain ⟨old, hold, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hs)
          have hb := hsuffix old hold
          omega
  have htable : ∀ pattern ∈ basis,
      pattern.Perm (List.range' 1 pattern.length) ∧
        ∀ index, index < pattern.length →
          ¬ (pattern.getD index 0 = 1 ∧ pattern.getD (index + 1) 0 = 2) := by
    decide
  intro pattern hpattern hoccurrence
  obtain ⟨hperm, hpairs⟩ := htable pattern hpattern
  obtain ⟨values, hincreasing, hmembers, hsublist, _⟩ := hoccurrence
  have hranks : ∀ rank ∈ pattern, 1 ≤ rank ∧ rank ≤ pattern.length := by
    intro rank hmem
    have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hmem)
    omega
  have hvalueBound : ∀ rank, 1 ≤ rank → rank ≤ pattern.length → rank ≤ values rank := by
    intro rank hlow hhigh
    induction rank with
    | zero => omega
    | succ rank ih =>
      by_cases hzero : rank = 0
      · subst rank
        exact hpositive _ (hmembers 1 (by omega) (by omega))
      · have hh := ih (by omega) (by omega)
        have hi := hincreasing rank (by omega) (by omega)
        omega
  have hnotboth : ¬ (1 ∈ pattern.map values ∧ 2 ∈ pattern.map values) := by
    rintro ⟨hone, htwo⟩
    obtain ⟨oneIndex, honeIndex⟩ := List.mem_iff_getElem?.mp hone
    obtain ⟨twoIndex, htwoIndex⟩ := List.mem_iff_getElem?.mp htwo
    obtain ⟨positions, hpositions⟩ :=
      List.sublist_iff_exists_orderEmbedding_getElem?_eq.mp hsublist
    have honePosition := hpositions oneIndex
    have htwoPosition := hpositions twoIndex
    rw [honeIndex] at honePosition
    rw [htwoIndex] at htwoPosition
    have honeWhere : positions oneIndex = before.length := by
      rcases hwhere _ _ honePosition.symm (Or.inl rfl) with hh | hh <;> omega
    have htwoWhere : positions twoIndex = before.length + 1 := by
      rcases hwhere _ _ htwoPosition.symm (Or.inr rfl) with hh | hh <;> omega
    have hindex : twoIndex = oneIndex + 1 := by
      have hlt : oneIndex < twoIndex := positions.strictMono.lt_iff_lt.mp (by omega)
      by_contra hne
      have ha := positions.strictMono (show oneIndex < oneIndex + 1 by omega)
      have hb := positions.strictMono (show oneIndex + 1 < twoIndex by omega)
      omega
    have hread : ∀ index entry, (pattern.map values)[index]? = some entry →
        pattern.getD index 0 ∈ pattern ∧ values (pattern.getD index 0) = entry := by
      intro index entry hget
      obtain ⟨hb, _⟩ := List.getElem?_eq_some_iff.mp hget
      have hbound : index < pattern.length := by simpa using hb
      refine ⟨?_, ?_⟩
      · rw [List.getD_eq_getElem _ _ hbound]
        exact List.getElem_mem hbound
      · simpa only [List.getElem?_map, List.getElem?_eq_getElem hbound,
          Option.map_some, Option.some.injEq, List.getD_eq_getElem _ _ hbound] using hget
    obtain ⟨honeMem, honeValue⟩ := hread _ _ honeIndex
    obtain ⟨htwoMem, htwoValue⟩ := hread _ _ htwoIndex
    obtain ⟨honeLow, honeHigh⟩ := hranks _ honeMem
    obtain ⟨htwoLow, htwoHigh⟩ := hranks _ htwoMem
    have honeBound := hvalueBound _ honeLow honeHigh
    have htwoBound := hvalueBound _ htwoLow htwoHigh
    have honeRank : pattern.getD oneIndex 0 = 1 := by omega
    have htwoRank : pattern.getD twoIndex 0 = 2 := by
      have hne : pattern.getD oneIndex 0 ≠ pattern.getD twoIndex 0 := by
        intro heq
        rw [heq] at honeValue
        omega
      omega
    apply hpairs oneIndex
      (by obtain ⟨hb, _⟩ := List.getElem?_eq_some_iff.mp honeIndex; simpa using hb)
    exact ⟨honeRank, hindex ▸ htwoRank⟩
  have hcontractStrict : ∀ rank, 1 ≤ rank → rank < pattern.length →
      contract (values rank) < contract (values (rank + 1)) := by
    intro rank hrank hbound
    have hi := hincreasing rank hrank hbound
    have hlo := hvalueBound rank hrank (by omega)
    have hhi := hvalueBound (rank + 1) (by omega) (by omega)
    have hsmall : rank ∈ pattern :=
      hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨hrank, by omega⟩)
    have hlarge : rank + 1 ∈ pattern :=
      hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    have hne : ¬ (values rank = 1 ∧ values (rank + 1) = 2) := by
      rintro ⟨ha, hb⟩
      exact hnotboth ⟨ha ▸ List.mem_map_of_mem hsmall, hb ▸ List.mem_map_of_mem hlarge⟩
    dsimp [contract]
    split <;> split <;> omega
  have hinverse : ∀ entry, 2 ≤ entry → contract (Nat.succ entry) = entry := by
    intro entry hentry
    dsimp only [contract]
    rw [if_neg (by omega)]
    omega
  have hcontracted : expanded.map contract = before ++ 1 :: 1 :: suffix := by
    have hb : before.map (contract ∘ Nat.succ) = before := by
      calc
        before.map (contract ∘ Nat.succ) = before.map id := by
          apply List.map_congr_left
          intro entry hentry
          exact hinverse entry (hbefore entry hentry)
        _ = before := List.map_id _
    have hs : suffix.map (contract ∘ Nat.succ) = suffix := by
      calc
        suffix.map (contract ∘ Nat.succ) = suffix.map id := by
          apply List.map_congr_left
          intro entry hentry
          exact hinverse entry (hsuffix entry hentry)
        _ = suffix := List.map_id _
    simp only [expanded, List.map_append, List.map_cons, List.map_map, hb, hs]
    simp [contract]
  have hsubcontract : (pattern.map (contract ∘ values)).Sublist
      (before ++ 1 :: 1 :: suffix) := by
    rw [← hcontracted]
    simpa only [List.map_map] using hsublist.map contract
  have hnodupSelected : (pattern.map (contract ∘ values)).Nodup := by
    apply hperm.nodup_iff.mpr (List.nodup_range' 1) |>.map_on
    intro left hleft right hright heq
    obtain ⟨hl, hbl⟩ := hranks left hleft
    obtain ⟨hr, hbr⟩ := hranks right hright
    have hmono : ∀ left right, 1 ≤ left → right ≤ pattern.length → left < right →
        contract (values left) < contract (values right) := by
      intro left right ha hb hab
      induction right with
      | zero => omega
      | succ right ih =>
        by_cases heq : left = right
        · subst right; exact hcontractStrict left ha (by omega)
        · have hh := ih (by omega) (by omega)
          have hi := hcontractStrict right (by omega) (by omega)
          omega
    dsimp [Function.comp_def] at heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hh | hh
    · have hi := hmono left right hl hbr hh; omega
    · have hi := hmono right left hr hbl hh; omega
  have hcollapse : ∀ (initial tail selected : List ℕ), selected.Nodup →
      selected.Sublist (initial ++ 1 :: 1 :: tail) →
        selected.Sublist (initial ++ 1 :: tail) := by
    intro initial
    induction initial with
    | nil =>
      intro tail selected hnd hsub
      rw [List.nil_append] at hsub ⊢
      rcases List.sublist_cons_iff.mp hsub with hh | ⟨rest, rfl, hh⟩
      · exact hh
      · rcases List.sublist_cons_iff.mp hh with hh | ⟨rest', heq, _⟩
        · exact hh.cons_cons 1
        · simp only [List.nodup_cons] at hnd
          exact False.elim (hnd.1 (heq ▸ List.mem_cons_self))
    | cons entry initial ih =>
      intro tail selected hnd hsub
      simp only [List.cons_append] at hsub ⊢
      rcases List.sublist_cons_iff.mp hsub with hh | ⟨rest, rfl, hh⟩
      · exact (ih tail selected hnd hh).cons entry
      · exact (ih tail rest (List.nodup_cons.mp hnd).2 hh).cons_cons entry
  have hsubold := hcollapse before suffix _ hnodupSelected hsubcontract
  apply hclass pattern hpattern
  refine ⟨contract ∘ values, hcontractStrict, ?_, hsubold, by simp⟩
  intro rank hrank hbound
  have hmem : rank ∈ pattern :=
    hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨hrank, by omega⟩)
  exact hsubold.subset (List.mem_map_of_mem hmem)

end D5.S3.Combinatorics.PopStack.PopStackIncreasing
