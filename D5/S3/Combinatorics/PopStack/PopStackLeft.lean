/- GID: D5/S3/Combinatorics/PopStack/PopStackLeft
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackLeft
   mirror-E: none(waiver:left-rank-two-insertion)
   anchors: []
   utility: none
   digest: Prepending rank two before a second-position minimum preserves basis avoidance. -/

import D5.S3.Combinatorics.PopStack.PopStackIncreasing
import D5.S3.Combinatorics.PopStack.PopStackPrime

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackLeft

open PopStackDefs

theorem prepend_two_inC (permutation : List ℕ)
    (hnodup : permutation.Nodup)
    (hpositive : ∀ entry ∈ permutation, 1 ≤ entry)
    (hminimum : permutation.getD 1 0 = 1) :
    InC (2 :: permutation.map (fun entry => if entry = 1 then 1 else entry + 1)) ↔
      InC permutation := by
  let shift := fun entry : ℕ => if entry = 1 then 1 else entry + 1
  let down := fun entry : ℕ => if entry = 1 then 1 else entry - 1
  let expanded := 2 :: permutation.map shift
  have hinverse : ∀ entry, 1 ≤ entry → down (shift entry) = entry := by
    intro entry hentry
    dsimp [down, shift]
    split_ifs <;> omega
  have hshiftStrict : ∀ left right, 1 ≤ left → left < right → shift left < shift right := by
    intro left right hpositive hlt
    dsimp [shift]
    split_ifs <;> omega
  have hshiftPositive : ∀ entry, 1 ≤ entry → 1 ≤ shift entry ∧ shift entry ≠ 2 := by
    intro entry hentry
    dsimp [shift]
    split <;> omega
  have hbounds : ∀ entry ∈ expanded, 1 ≤ entry := by
    intro entry hentry
    rcases List.mem_cons.mp hentry with rfl | hentry
    · omega
    · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hentry
      exact (hshiftPositive old (hpositive old hold)).1
  have htable : ∀ pattern ∈ basis,
      pattern.Perm (List.range' 1 pattern.length) ∧ 4 ≤ pattern.length ∧
        (pattern.getD 0 0 ≤ 2 → pattern.getD 0 0 = 2 ∧ pattern.getD 3 0 = 1) := by
    decide
  constructor
  · intro hclass pattern hpattern hoccurrence
    obtain ⟨values, hincreasing, hmembers, hsublist, _⟩ := hoccurrence
    apply hclass pattern hpattern
    refine ⟨shift ∘ values, ?_, ?_, ?_, by simp⟩
    · intro rank hrank hbound
      exact hshiftStrict _ _ (hpositive _ (hmembers rank hrank (by omega)))
        (hincreasing rank hrank hbound)
    · intro rank hrank hbound
      exact List.mem_cons_of_mem 2 (List.mem_map_of_mem (hmembers rank hrank hbound))
    · simpa only [List.map_map] using (hsublist.map shift).cons 2
  · intro hclass pattern hpattern hoccurrence
    obtain ⟨hperm, hlength, hfirst⟩ := htable pattern hpattern
    obtain ⟨values, hincreasing, hmembers, hsublist, _⟩ := hoccurrence
    have hranks : ∀ rank ∈ pattern, 1 ≤ rank ∧ rank ≤ pattern.length := by
      intro rank hmem
      have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hmem)
      omega
    have hvalueBound : ∀ rank, 1 ≤ rank → rank ≤ pattern.length →
        rank ≤ values rank := by
      intro rank hlow hhigh
      induction rank with
      | zero => omega
      | succ rank ih =>
        by_cases hzero : rank = 0
        · subst rank
          exact hbounds _ (hmembers 1 (by omega) (by omega))
        · have hh := ih (by omega) (by omega)
          have hi := hincreasing rank (by omega) (by omega)
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
    have hmissing : 2 ∉ pattern.map values := by
      intro htwo
      obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp htwo
      obtain ⟨positions, hpositions⟩ :=
        List.sublist_iff_exists_orderEmbedding_getElem?_eq.mp hsublist
      have hge : ∀ index, index ≤ positions index := by
        intro index
        induction index with
        | zero => omega
        | succ index ih =>
          have hh := positions.strictMono (Nat.lt_succ_self index)
          change positions index < positions (index + 1) at hh
          omega
      have hposition := hpositions index
      rw [hindex] at hposition
      have hzero : positions index = 0 := by
        by_contra hne
        obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le
          (show 1 ≤ positions index by omega)
        have hget : (permutation.map shift)[offset]? = some 2 := by
          rw [hoffset, Nat.add_comm] at hposition
          simpa only [expanded, List.getElem?_cons_succ] using hposition.symm
        obtain ⟨old, hold, heq⟩ := List.mem_map.mp (List.mem_of_getElem? hget)
        exact (hshiftPositive old (hpositive old hold)).2 heq
      have hindexZero : index = 0 := by have hh := hge index; omega
      subst index
      obtain ⟨hfirstMem, hfirstValue⟩ := hread _ _ hindex
      obtain ⟨hlow, hhigh⟩ := hranks _ hfirstMem
      have hb := hvalueBound _ hlow hhigh
      obtain ⟨hfirstRank, hminRank⟩ := hfirst (by omega)
      rw [hfirstRank] at hfirstValue
      have hminValue : values 1 = 1 := by
        have hp := hbounds _ (hmembers 1 (by omega) (by omega))
        have hi := hincreasing 1 (by omega) (by omega)
        change values 1 < values 2 at hi
        omega
      have hminGet : (pattern.map values)[3]? = some 1 := by
        have hr : pattern[3]? = some 1 := by
          rw [List.getElem?_eq_getElem (by omega)]
          rw [← List.getD_eq_getElem _ 0 (by omega), hminRank]
        simp only [List.getElem?_map, hr, Option.map_some, hminValue]
      have hselectedMin := hpositions 3
      rw [hminGet] at hselectedMin
      have hminPosition : positions 3 = 2 := by
        have hminIndex : 1 < permutation.length := by
          by_contra hn
          have hh : permutation.getD 1 0 = 0 :=
            List.getD_eq_default _ _ (by omega)
          omega
        have hget : permutation[1]? = some 1 := by
          rw [List.getElem?_eq_getElem hminIndex]
          rw [← List.getD_eq_getElem _ 0 hminIndex, hminimum]
        have hexpandedMin : expanded[2]? = some 1 := by
          simp only [expanded, List.getElem?_cons_succ, List.getElem?_map, hget,
            Option.map_some, shift, ↓reduceIte]
        have hexpandedNodup : expanded.Nodup := by
          apply List.nodup_cons.mpr
          refine ⟨?_, hnodup.map_on ?_⟩
          · intro hmem
            obtain ⟨old, hold, heq⟩ := List.mem_map.mp hmem
            exact (hshiftPositive old (hpositive old hold)).2 heq
          · intro left hleft right hright heq
            have hl := hpositive left hleft
            have hr := hpositive right hright
            dsimp [shift] at heq
            split_ifs at heq <;> omega
        apply (List.getElem?_inj
          (List.getElem?_eq_some_iff.mp hselectedMin.symm).1 hexpandedNodup).mp
        exact hselectedMin.symm.trans hexpandedMin.symm
      have hh := hge 3
      omega
    have hsubtail : (pattern.map values).Sublist (permutation.map shift) := by
      rcases List.sublist_cons_iff.mp hsublist with hh | ⟨rest, heq, _⟩
      · exact hh
      · exact False.elim (hmissing (heq ▸ List.mem_cons_self))
    have hmapInverse : (permutation.map shift).map down = permutation := by
      rw [List.map_map]
      calc
        permutation.map (down ∘ shift) = permutation.map id := by
          apply List.map_congr_left
          intro entry hentry
          exact hinverse entry (hpositive entry hentry)
        _ = permutation := List.map_id _
    have hsubold : (pattern.map (down ∘ values)).Sublist permutation := by
      simpa only [List.map_map, hmapInverse] using hsubtail.map down
    apply hclass pattern hpattern
    refine ⟨down ∘ values, ?_, ?_, hsubold, by simp⟩
    · intro rank hrank hbound
      have hi := hincreasing rank hrank hbound
      have hlo := hvalueBound rank hrank (by omega)
      have hhi := hvalueBound (rank + 1) (by omega) (by omega)
      have hlowMem : rank ∈ pattern :=
        hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨hrank, by omega⟩)
      have hhighMem : rank + 1 ∈ pattern :=
        hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      have hlowNe : values rank ≠ 2 := fun heq =>
        hmissing (heq ▸ List.mem_map_of_mem hlowMem)
      have hhighNe : values (rank + 1) ≠ 2 := fun heq =>
        hmissing (heq ▸ List.mem_map_of_mem hhighMem)
      dsimp [Function.comp_def, down]
      split <;> split <;> omega
    · intro rank hrank hbound
      have hmem : rank ∈ pattern :=
        hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨hrank, by omega⟩)
      exact hsubold.subset (List.mem_map_of_mem hmem)

end D5.S3.Combinatorics.PopStack.PopStackLeft
