/- GID: D5/S3/Combinatorics/PopStack/PopStackDecreasing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackDecreasing
   mirror-E: none(waiver:decreasing-inflation-pattern-contraction)
   anchors: [mathlib/module/Mathlib.Data.List.NodupEquivFin]
   utility: none
   digest: Decreasing inflation of either of the first two entries preserves basis avoidance. -/

import D5.S3.Combinatorics.PopStack.PopStackInflation
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackDecreasing

open PopStackDefs PopStackInflation

theorem decreasing_early_inflation (beforeList suffix : List ℕ) (pivot : ℕ)
    (hearly : beforeList.length ≤ 1) (hnodup : (beforeList ++ pivot :: suffix).Nodup)
    (hclass : InC (beforeList ++ pivot :: suffix)) :
    InC (inflate (beforeList ++ pivot :: suffix) beforeList.length [2, 1]) := by
  let shift := fun value => if pivot < value then value + 1 else value
  let contract := fun value => if pivot < value then value - 1 else value
  let expanded := beforeList.map shift ++ (pivot + 1) :: pivot :: suffix.map shift
  have hmissing : pivot ∉ beforeList ∧ pivot ∉ suffix := by
    simp only [List.nodup_append, List.nodup_cons] at hnodup
    exact ⟨fun hp => hnodup.2.2 pivot hp pivot (by simp) rfl, hnodup.2.1.1⟩
  have hinverse : ∀ value, contract (shift value) = value := by
    intro value
    dsimp [shift, contract]
    by_cases hlt : pivot < value
    · rw [if_pos hlt, if_pos (show pivot < value + 1 by omega)]
      omega
    · rw [if_neg hlt, if_neg hlt]
  have houtside : ∀ value, value ≠ pivot →
      shift value ≠ pivot ∧ shift value ≠ pivot + 1 := by
    intro value hne
    dsimp [shift]
    split <;> omega
  have hexpanded : inflate (beforeList ++ pivot :: suffix) beforeList.length [2, 1] =
      expanded := by
    simp [inflate, expanded, shift, List.getD_eq_getElem?_getD]
  rw [hexpanded]
  have htable : ∀ pattern ∈ basis,
      pattern.Perm (List.range' 1 pattern.length) ∧
      ∀ index, index ≤ 1 →
        pattern.getD index 0 < pattern.getD (index + 1) 0 ∨
          pattern.getD (index + 1) 0 + 2 ≤ pattern.getD index 0 := by
    decide
  intro pattern hpattern hoccurrence
  obtain ⟨hperm, hpairs⟩ := htable pattern hpattern
  obtain ⟨values, hincreasing, hmembers, hsublist, _⟩ := hoccurrence
  have hranks : ∀ rank ∈ pattern, 1 ≤ rank ∧ rank ≤ pattern.length := by
    intro rank hmem
    have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hmem)
    omega
  have hmonotone : ∀ left right, 1 ≤ left → right ≤ pattern.length → left ≤ right →
      values left ≤ values right := by
    intro left right hl hr hle
    induction right with
    | zero => omega
    | succ right ih =>
      by_cases heq : left = right + 1
      · subst left; exact le_rfl
      · have hh := ih (by omega) (by omega)
        have hi := hincreasing right (by omega) (by omega)
        omega
  have hstrict : ∀ left right, 1 ≤ left → right ≤ pattern.length → left < right →
      values left < values right := by
    intro left right hl hr hlt
    have hi := hincreasing left hl (by omega)
    have hh := hmonotone (left + 1) right (by omega) hr (by omega)
    omega
  have hgap : ∀ left right, 1 ≤ left → right ≤ pattern.length → left + 2 ≤ right →
      values left + 2 ≤ values right := by
    intro left right hl hr hlt
    have hi := hincreasing left hl (by omega)
    have hj := hincreasing (left + 1) (by omega) (by omega)
    change values (left + 1) < values (left + 2) at hj
    have hh := hmonotone (left + 2) right (by omega) hr hlt
    omega
  have hwhere : ∀ position value, expanded[position]? = some value →
      (value = pivot ∨ value = pivot + 1) →
      (position = beforeList.length ∧ value = pivot + 1) ∨
        (position = beforeList.length + 1 ∧ value = pivot) := by
    intro position value hget hvalue
    by_cases hbefore : position < beforeList.length
    · have hh : value ∈ beforeList.map shift := by
        apply List.mem_of_getElem?
        simpa only [expanded, List.getElem?_append_left
          (show position < (beforeList.map shift).length by simpa using hbefore)] using hget
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hh
      have hn := houtside old (fun heq => hmissing.1 (heq ▸ hold))
      tauto
    · have hh : ((pivot + 1) :: pivot :: suffix.map shift)[position - beforeList.length]? =
          some value := by
        simpa only [expanded, List.getElem?_append_right
          (show (beforeList.map shift).length ≤ position by simp; omega), List.length_map]
          using hget
      by_cases hfirst : position = beforeList.length
      · subst position
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hh
        exact Or.inl ⟨rfl, hh.symm⟩
      · by_cases hsecond : position = beforeList.length + 1
        · subst position
          simp only [Nat.add_sub_cancel_left, List.getElem?_cons_succ,
            List.getElem?_cons_zero, Option.some.injEq] at hh
          exact Or.inr ⟨rfl, hh.symm⟩
        · have hafter : 2 ≤ position - beforeList.length := by omega
          obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hafter
          rw [hoffset] at hh
          have hh' : (suffix.map shift)[offset]? = some value := by
            rw [show 2 + offset = offset + 1 + 1 by omega] at hh
            simpa only [List.getElem?_cons_succ] using hh
          obtain ⟨old, hold, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hh')
          have hn := houtside old (fun heq => hmissing.2 (heq ▸ hold))
          tauto
  have hnotboth : ¬ (pivot + 1 ∈ pattern.map values ∧ pivot ∈ pattern.map values) := by
    rintro ⟨hupper, hlower⟩
    obtain ⟨upperIndex, hupperIndex⟩ := List.mem_iff_getElem?.mp hupper
    obtain ⟨lowerIndex, hlowerIndex⟩ := List.mem_iff_getElem?.mp hlower
    obtain ⟨positions, hpositions⟩ :=
      List.sublist_iff_exists_orderEmbedding_getElem?_eq.mp hsublist
    have hupperPosition := hpositions upperIndex
    have hlowerPosition := hpositions lowerIndex
    rw [hupperIndex] at hupperPosition
    rw [hlowerIndex] at hlowerPosition
    have hu : positions upperIndex = beforeList.length := by
      rcases hwhere _ _ hupperPosition.symm (Or.inr rfl) with hh | hh <;> omega
    have hl : positions lowerIndex = beforeList.length + 1 := by
      rcases hwhere _ _ hlowerPosition.symm (Or.inl rfl) with hh | hh <;> omega
    have hindex : lowerIndex = upperIndex + 1 := by
      have hlt : upperIndex < lowerIndex := positions.strictMono.lt_iff_lt.mp (by omega)
      by_contra hne
      have ha := positions.strictMono (show upperIndex < upperIndex + 1 by omega)
      have hb := positions.strictMono (show upperIndex + 1 < lowerIndex by omega)
      omega
    have hbound : upperIndex ≤ 1 := by
      have hge : ∀ index, index ≤ positions index := by
        intro index
        induction index with
        | zero => omega
        | succ index ih =>
          have hh := positions.strictMono (Nat.lt_succ_self index)
          change positions index < positions (index + 1) at hh
          change index + 1 ≤ positions (index + 1)
          omega
      have hh := hge upperIndex
      omega
    have hupperRank : values (pattern.getD upperIndex 0) = pivot + 1 := by
      cases hget : pattern[upperIndex]? with
      | none => simp [List.getElem?_map, hget] at hupperIndex
      | some rank =>
        simpa [List.getElem?_map, List.getD_eq_getElem?_getD, hget] using hupperIndex
    have hlowerRank : values (pattern.getD lowerIndex 0) = pivot := by
      cases hget : pattern[lowerIndex]? with
      | none => simp [List.getElem?_map, hget] at hlowerIndex
      | some rank =>
        simpa [List.getElem?_map, List.getD_eq_getElem?_getD, hget] using hlowerIndex
    have hupperMem : pattern.getD upperIndex 0 ∈ pattern := by
      obtain ⟨hh, _⟩ := List.getElem?_eq_some_iff.mp hupperIndex
      have hb : upperIndex < pattern.length := by simpa using hh
      simp [List.getD_eq_getElem?_getD, hb]
    have hlowerMem : pattern.getD lowerIndex 0 ∈ pattern := by
      obtain ⟨hh, _⟩ := List.getElem?_eq_some_iff.mp hlowerIndex
      have hb : lowerIndex < pattern.length := by simpa using hh
      simp [List.getD_eq_getElem?_getD, hb]
    obtain ⟨hup, hupbound⟩ := hranks _ hupperMem
    obtain ⟨hlow, hlowbound⟩ := hranks _ hlowerMem
    rcases hpairs upperIndex hbound with hh | hh
    · rw [← hindex] at hh
      have hlt := hstrict _ _ hup hlowbound hh
      omega
    · rw [← hindex] at hh
      have hle := hgap _ _ hlow hupbound hh
      omega
  have hcontractStrict : ∀ rank, 1 ≤ rank → rank < pattern.length →
      contract (values rank) < contract (values (rank + 1)) := by
    intro rank hrank hbound
    have hi := hincreasing rank hrank hbound
    have hsmall : rank ∈ pattern :=
      hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨hrank, by omega⟩)
    have hlarge : rank + 1 ∈ pattern :=
      hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    have hne : ¬ (values rank = pivot ∧ values (rank + 1) = pivot + 1) := by
      rintro ⟨ha, hb⟩
      apply hnotboth
      constructor
      · exact hb ▸ List.mem_map_of_mem hlarge
      · exact ha ▸ List.mem_map_of_mem hsmall
    dsimp [contract]
    split <;> split <;> omega
  have hcontracted : expanded.map contract = beforeList ++ pivot :: pivot :: suffix := by
    simp [expanded, List.map_map, Function.comp_def, hinverse, contract]
  have hsubcontract : (pattern.map (contract ∘ values)).Sublist
      (beforeList ++ pivot :: pivot :: suffix) := by
    simpa only [List.map_map, hcontracted] using hsublist.map contract
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
  have hcollapse : ∀ (before after selected : List ℕ), selected.Nodup →
      selected.Sublist (before ++ pivot :: pivot :: after) →
        selected.Sublist (before ++ pivot :: after) := by
    intro before
    induction before with
    | nil =>
      intro after selected hnd hsub
      rw [List.nil_append] at hsub ⊢
      rcases List.sublist_cons_iff.mp hsub with hh | ⟨rest, rfl, hh⟩
      · exact hh
      · rcases List.sublist_cons_iff.mp hh with hh | ⟨rest', heq, _⟩
        · exact hh.cons_cons pivot
        · simp only [List.nodup_cons] at hnd
          exact False.elim (hnd.1 (heq ▸ List.mem_cons_self))
    | cons value before ih =>
      intro after selected hnd hsub
      simp only [List.cons_append] at hsub ⊢
      rcases List.sublist_cons_iff.mp hsub with hh | ⟨rest, rfl, hh⟩
      · exact (ih after selected hnd hh).cons value
      · exact (ih after rest (List.nodup_cons.mp hnd).2 hh).cons_cons value
  have hsubold := hcollapse beforeList suffix _ hnodupSelected hsubcontract
  apply hclass pattern hpattern
  refine ⟨contract ∘ values, hcontractStrict, ?_, hsubold, by simp⟩
  intro rank hrank hbound
  have hmem : rank ∈ pattern :=
    hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨hrank, by omega⟩)
  exact hsubold.subset (List.mem_map_of_mem hmem)

end D5.S3.Combinatorics.PopStack.PopStackDecreasing
