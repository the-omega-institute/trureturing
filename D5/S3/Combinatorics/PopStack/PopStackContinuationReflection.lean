/- GID: D5/S3/Combinatorics/PopStack/PopStackContinuationReflection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackContinuationReflection
   mirror-E: none(waiver:ordinary-continuation-inverse-intervals)
   anchors: [mathlib/module/Mathlib.Data.Finset.Max]
   utility: none
   digest: Deleting the first entry reverses ordinary continuation and preserves simplicity. -/

import D5.S3.Combinatorics.PopStack.PopStackContinuation
import D5.S3.Combinatorics.PopStack.PopStackReconstruction
import D5.S3.Combinatorics.PopStack.PopStackThirdEntry
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackContinuationReflection

open PopStackDefs PopStackContinuation PopStackInflation PopStackReconstruction

theorem ordinary_continuation_inverse (member : List ℕ)
    (hmemberPerm : member.Perm (List.range' 1 member.length)) (hmemberC : InC member)
    (hmemberSimple : IsSimple member) (memberMinimum : ℕ)
    (hmemberLater : 3 ≤ memberMinimum) (hmemberMinimumBound : memberMinimum < member.length)
    (hmemberMinimum : member.getD memberMinimum 0 = 1)
    (hmemberSecond : member.getD 1 0 < member.length) :
    let predecessor := (member.drop 1).map
      (fun entry => if member.getD 0 0 < entry then entry - 1 else entry)
    predecessor.Perm (List.range' 1 predecessor.length) ∧ InC predecessor ∧
      IsSimple predecessor ∧ predecessor.getD 1 0 < predecessor.length ∧
      predecessor.getD (memberMinimum - 1) 0 = 1 ∧ W predecessor = member := by
  classical
  let alpha := member.getD 0 0
  let down := fun entry => if alpha < entry then entry - 1 else entry
  let upMember := fun entry => if alpha - 1 < entry then entry + 1 else entry
  let permutation := (member.drop 1).map down
  have hmemberLength : 4 ≤ member.length := by omega
  have hmemberNodup := hmemberPerm.nodup_iff.mpr (List.nodup_range' 1)
  have hmemberHead : member = alpha :: member.drop 1 := by
    have hh := List.drop_eq_getElem?_toList_append (l := member) (i := 0)
    rw [List.getElem?_eq_getElem (by omega),
      ← List.getD_eq_getElem member 0 (by omega)] at hh
    simpa only [List.drop_zero, Option.toList_some, List.singleton_append] using hh
  have htailMissing : alpha ∉ member.drop 1 := by
    rw [hmemberHead, List.nodup_cons] at hmemberNodup
    exact hmemberNodup.1
  have htailNodup : (member.drop 1).Nodup := hmemberNodup.drop
  have htailMem : ∀ entry, entry ∈ member.drop 1 ↔
      1 ≤ entry ∧ entry ≤ member.length ∧ entry ≠ alpha := by
    intro entry
    constructor
    · intro hentry
      have hh := List.mem_range'_1.mp
        (hmemberPerm.mem_iff.mp (List.mem_of_mem_drop hentry))
      have hn : entry ≠ alpha := by intro heq; exact htailMissing (heq ▸ hentry)
      omega
    · rintro ⟨hpositive, hupper, hnot⟩
      have hh := hmemberPerm.mem_iff.mpr (List.mem_range'_1.mpr ⟨hpositive, by omega⟩)
      rw [hmemberHead, List.mem_cons] at hh
      exact hh.resolve_left hnot
  have halphaBounds : 1 ≤ alpha ∧ alpha ≤ member.length := by
    have hh := List.mem_range'_1.mp (hmemberPerm.mem_iff.mp (by
      rw [hmemberHead]; simp : alpha ∈ member))
    omega
  have halphaPositive : 1 < alpha := by
    have hn : alpha ≠ 1 := by
      intro heq
      have hh := (List.getD_inj (by omega : 0 < member.length)
        hmemberMinimumBound hmemberNodup).mp (heq.trans hmemberMinimum.symm)
      omega
    omega
  have halphaUpper : alpha < member.length := by
    by_contra hn
    have heq : alpha = member.length := by omega
    have htailPerm : (member.drop 1).Perm (List.range' 1 (member.length - 1)) := by
      apply (List.perm_ext_iff_of_nodup htailNodup (List.nodup_range' _)).mpr
      intro entry
      rw [htailMem, List.mem_range'_1]
      omega
    exact hmemberSimple 1 (member.length - 1) 1 (by omega) (by omega) (by omega)
      (by simpa only [← List.length_drop (l := member) (i := 1), List.take_length]
        using htailPerm)
  have hpermutationLength : permutation.length = member.length - 1 := by
    simp [permutation]
  have hpermutationNodup : permutation.Nodup := htailNodup.map_on (by
    intro first hfirst second hsecond heq
    have hf := (htailMem first).mp hfirst
    have hs := (htailMem second).mp hsecond
    dsimp only [down] at heq
    split_ifs at heq <;> omega)
  have hperm : permutation.Perm (List.range' 1 permutation.length) := by
    apply (List.perm_ext_iff_of_nodup hpermutationNodup (List.nodup_range' _)).mpr
    intro entry
    change entry ∈ (member.drop 1).map down ↔ entry ∈ _
    simp only [List.mem_map, List.mem_range'_1]
    constructor
    · rintro ⟨old, hold, rfl⟩
      have hh := (htailMem old).mp hold
      dsimp only [down]
      split_ifs <;> omega
    · rintro ⟨hpositive, hupper⟩
      by_cases hlow : entry < alpha
      · refine ⟨entry, (htailMem entry).mpr ⟨by omega, by omega, by omega⟩, ?_⟩
        dsimp only [down]; rw [if_neg (by omega)]
      · refine ⟨entry + 1, (htailMem (entry + 1)).mpr
          ⟨by omega, by omega, by omega⟩, ?_⟩
        dsimp only [down]; rw [if_pos (by omega)]; omega
  have hget : ∀ index, index < permutation.length →
      permutation.getD index 0 = down (member.getD (index + 1) 0) := by
    intro index hindex
    change ((member.drop 1).map down).getD index 0 = _
    rw [List.getD_eq_getElem _ 0 (by simp only [List.length_map, List.length_drop]; omega),
      List.getElem_map, List.getElem_drop, ← List.getD_eq_getElem member 0 (by omega)]
    congr 2; omega
  have hthird := PopStackThirdEntry.third_entry_before_minimum member hmemberPerm
    hmemberC hmemberSimple memberMinimum hmemberLater hmemberMinimumBound hmemberMinimum
  have hbetaValue : permutation.getD 1 0 = alpha - 1 := by
    rw [hget 1 (by omega)]
    norm_num only
    change alpha = member.getD 2 0 + 1 at hthird
    dsimp only [down]
    rw [if_neg (by omega)]
    omega
  have hsecond : permutation.getD 1 0 < permutation.length := by rw [hbetaValue]; omega
  have hfirstTop : permutation.getD 0 0 < permutation.length := by
    rw [hget 0 (by omega)]
    norm_num only
    have hnot : member.getD 1 0 ≠ alpha := by
      intro heq
      have hh := (List.getD_inj (by omega : 1 < member.length)
        (by omega : 0 < member.length) hmemberNodup).mp heq
      omega
    dsimp only [down]
    split_ifs <;> omega
  let minimumIndex := memberMinimum - 1
  have hlater : 2 ≤ minimumIndex := by dsimp only [minimumIndex]; omega
  have hminimumBound : minimumIndex < permutation.length := by
    dsimp only [minimumIndex]; omega
  have hminimum : permutation.getD minimumIndex 0 = 1 := by
    rw [hget minimumIndex hminimumBound,
      show minimumIndex + 1 = memberMinimum by dsimp only [minimumIndex]; omega,
      hmemberMinimum]
    dsimp only [down]; rw [if_neg (by omega)]
  have hrecover : permutation.map upMember = member.drop 1 := by
    change ((member.drop 1).map down).map upMember = member.drop 1
    rw [List.map_map]
    calc
      _ = (member.drop 1).map id := by
        apply List.map_congr_left
        intro entry hentry
        have hh := (htailMem entry).mp hentry
        dsimp only [Function.comp_def, upMember, down, id]
        split_ifs <;> omega
      _ = member.drop 1 := List.map_id _
  have hW : W permutation = member := by
    have hhead : alpha - 1 + 1 = alpha := by omega
    change (permutation.getD 1 0 + 1) :: permutation.map
      (fun entry => if permutation.getD 1 0 < entry then entry + 1 else entry) = member
    rw [hbetaValue, hhead]
    change alpha :: permutation.map upMember = member
    rw [hrecover]
    exact hmemberHead.symm
  have hupMono : StrictMono upMember := by
    intro first second hlt
    dsimp only [upMember]
    split_ifs <;> omega
  have hC : InC permutation := by
    intro pattern hpattern hocc
    obtain ⟨ranks, hinc, hmem, hsub, _⟩ := hocc
    apply hmemberC pattern hpattern
    refine ⟨upMember ∘ ranks, ?_, ?_, ?_, by simp⟩
    · intro rank hpositive hupper
      exact hupMono (hinc rank hpositive hupper)
    · intro rank hpositive hupper
      apply List.mem_of_mem_drop
      rw [← hrecover]
      exact List.mem_map.mpr ⟨_, hmem rank hpositive hupper, rfl⟩
    · have hh := hsub.map upMember
      rw [hrecover, List.map_map] at hh
      exact hh.trans (List.drop_sublist 1 member)
  have hsimple : IsSimple (W permutation) := by rw [hW]; exact hmemberSimple
  change permutation.Perm _ ∧ InC permutation ∧ IsSimple permutation ∧
    permutation.getD 1 0 < permutation.length ∧
    permutation.getD (memberMinimum - 1) 0 = 1 ∧ W permutation = member
  refine ⟨hperm, hC, ?_, hsecond, hminimum, hW⟩
  let beta := permutation.getD 1 0
  let shift := fun entry => if beta < entry then entry + 1 else entry
  let expanded := W permutation
  have hshape : expanded = (beta + 1) :: permutation.map shift := rfl
  have hnewLength : expanded.length = permutation.length + 1 := by simp [expanded, W]
  change IsSimple expanded at hsimple
  have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
  have hbounds : ∀ entry ∈ permutation, 1 ≤ entry ∧ entry ≤ permutation.length := by
    intro entry hentry
    have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hentry)
    omega
  have hfirstPositive : 1 < permutation.getD 0 0 := by
    have hmem : permutation.getD 0 0 ∈ permutation := by
      rw [List.getD_eq_getElem _ 0 (by omega)]
      exact List.getElem_mem (by omega)
    have hb := hbounds _ hmem
    have hn : permutation.getD 0 0 ≠ 1 := by
      intro heq
      have hh := (List.getD_inj (by omega : 0 < permutation.length)
        hminimumBound hnodup).mp (heq.trans hminimum.symm)
      omega
    omega
  have hbetaPositive : 1 < beta := by
    have hmem : beta ∈ permutation := by
      dsimp only [beta]
      rw [List.getD_eq_getElem _ 0 (by omega)]
      exact List.getElem_mem (by omega)
    have hb := hbounds _ hmem
    have hn : beta ≠ 1 := by
      intro heq
      have hh := (List.getD_inj (by omega : 1 < permutation.length)
        hminimumBound hnodup).mp (heq.trans hminimum.symm)
      omega
    omega
  have hshiftMono : StrictMono shift := by
    intro first second hlt
    dsimp only [shift]
    split_ifs <;> omega
  have hmissing : ∀ entry, shift entry ≠ beta + 1 := by
    intro entry
    dsimp only [shift]
    split_ifs <;> omega
  have hnewNodup : expanded.Nodup := by
    rw [hshape, List.nodup_cons]
    refine ⟨?_, hnodup.map hshiftMono.injective⟩
    intro hmem
    obtain ⟨entry, _, heq⟩ := List.mem_map.mp hmem
    exact hmissing entry heq
  have hrestr : ∀ start count lower, 2 ≤ count → count < permutation.length →
      start + count ≤ permutation.length →
      ((permutation.drop start).take count).Perm (List.range' lower count) →
      start = 1 ∧ lower ≤ beta ∧ beta + 1 < lower + count := by
    intro start count lower hcount hproper hbound hinterval
    have hnewSlice : ((expanded.drop (start + 1)).take count) =
        ((permutation.drop start).take count).map shift := by
      simp [hshape, List.drop_succ_cons, ← List.map_drop, ← List.map_take]
    have hcross : lower ≤ beta ∧ beta + 1 < lower + count := by
      by_contra hn
      have hrange : (List.range' lower count).map shift =
          List.range' (if beta < lower then lower + 1 else lower) count := by
        simp only [List.range'_eq_map_range, List.map_map]
        apply List.map_congr_left
        intro offset hoffset
        have hb := List.mem_range.mp hoffset
        dsimp only [Function.comp_def, shift]
        by_cases hlow : beta < lower
        · rw [if_pos hlow, if_pos (by omega)]
          omega
        · rw [if_neg hlow, if_neg (by omega)]
      have hnewInterval := hinterval.map shift
      rw [hrange, ← hnewSlice] at hnewInterval
      exact hsimple (start + 1) count _ hcount (by omega) (by omega) hnewInterval
    have hbetaMem : beta ∈ (permutation.drop start).take count :=
      hinterval.mem_iff.mpr (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    obtain ⟨offset, hoffset, hget⟩ := List.mem_iff_getElem.mp hbetaMem
    have hoffsetBound : offset < count := by
      simp only [List.length_take, List.length_drop] at hoffset
      omega
    rw [List.getElem_take, List.getElem_drop] at hget
    have hposition : start + offset = 1 := by
      apply (List.getD_inj (by omega) (by omega) hnodup).mp
      rw [List.getD_eq_getElem _ 0 (by omega)]
      exact hget
    have hstartSmall : start ≤ 1 := by omega
    have hnotZero : start ≠ 0 := by
      intro heq
      subst start
      have hnewPrefix : (expanded.take (count + 1)).Perm (List.range' lower (count + 1)) := by
        apply (List.perm_ext_iff_of_nodup hnewNodup.take (List.nodup_range' _)).mpr
        intro entry
        have hpref : expanded.take (count + 1) =
            (beta + 1) :: (permutation.take count).map shift := by simp [hshape]
        rw [hpref, List.mem_cons]
        constructor
        · rintro (rfl | hmem)
          · apply List.mem_range'_1.mpr; omega
          · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hmem
            have hh := List.mem_range'_1.mp
              (hinterval.mem_iff.mp (by simpa only [List.drop_zero] using hold))
            apply List.mem_range'_1.mpr
            dsimp only [shift]
            split_ifs <;> omega
        · intro hmem
          have hb := List.mem_range'_1.mp hmem
          by_cases heq : entry = beta + 1
          · exact Or.inl heq
          right
          by_cases hlow : entry ≤ beta
          · refine List.mem_map.mpr ⟨entry, ?_, ?_⟩
            · simpa only [List.drop_zero] using hinterval.mem_iff.mpr
                (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
            · dsimp only [shift]; rw [if_neg (by omega)]
          · refine List.mem_map.mpr ⟨entry - 1, ?_, ?_⟩
            · simpa only [List.drop_zero] using hinterval.mem_iff.mpr
                (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
            · dsimp only [shift]; rw [if_pos (by omega)]; omega
      exact hsimple 0 (count + 1) lower (by omega) (by omega) (by omega)
        (by simpa only [List.drop_zero] using hnewPrefix)
    exact ⟨by omega, hcross⟩
  by_contra hnonsimple
  have hexists : ∃ count lower, 2 ≤ count ∧ count < permutation.length ∧
      1 + count ≤ permutation.length ∧
      ((permutation.drop 1).take count).Perm (List.range' lower count) := by
    simp only [IsSimple, not_forall, not_not] at hnonsimple
    obtain ⟨start, count, lower, hcount, hproper, hbound, hinterval⟩ := hnonsimple
    have hh := hrestr start count lower hcount hproper hbound hinterval
    exact ⟨count, lower, hcount, hproper, by omega, by simpa only [hh.1] using hinterval⟩
  obtain ⟨oldCount, oldLower, holdCount, holdProper, holdBound, holdInterval⟩ := hexists
  let candidates := (Finset.range permutation.length).filter fun count =>
    2 ≤ count ∧ ∃ lower, 1 + count ≤ permutation.length ∧
      ((permutation.drop 1).take count).Perm (List.range' lower count)
  have holdMem : oldCount ∈ candidates := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr holdProper, holdCount, oldLower, holdBound, holdInterval⟩
  obtain ⟨count, hcountMem, hmax⟩ :=
    Finset.exists_max_image candidates id ⟨oldCount, holdMem⟩
  obtain ⟨hcountRange, hcount, lower, hbound, hinterval⟩ := Finset.mem_filter.mp hcountMem
  have hproper := Finset.mem_range.mp hcountRange
  have hcross := hrestr 1 count lower hcount hproper hbound hinterval
  have hcovered : ∀ index size bottom, 2 ≤ size → size < permutation.length →
      index + size ≤ permutation.length →
      ((permutation.drop index).take size).Perm (List.range' bottom size) →
      1 ≤ index ∧ index + size ≤ 1 + count := by
    intro index size bottom hsize hsizeProper hsizeBound hother
    have hi := (hrestr index size bottom hsize hsizeProper hsizeBound hother).1
    have hm : size ∈ candidates := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hsizeProper, hsize, bottom, by omega,
        by simpa only [hi] using hother⟩
    have hh := hmax size hm
    dsimp only [id] at hh
    omega
  let before := permutation.take 1
  let values := (permutation.drop 1).take count
  let after := permutation.drop (1 + count)
  have hsplit : before ++ values ++ after = permutation := by
    dsimp [before, values, after]
    rw [← List.drop_drop, List.append_assoc, List.take_append_drop,
      List.take_append_drop]
  have hvaluesLength : values.length = count := by
    simp only [values, List.length_take, List.length_drop]; omega
  have hbeforeLength : before.length = 1 := by simp [before]; omega
  have hafterLength : after.length = permutation.length - (1 + count) := by simp [after]
  obtain ⟨skeleton, block, hskeletonPerm, hblockPerm, hskeletonLength, hblockLength,
    hinflate, hquotient⟩ := reconstruct_interval before values after lower
      (by simpa only [hsplit] using hperm) (by simpa only [hvaluesLength] using hinterval)
      (by omega)
  have hquotient' := hquotient (by simpa only [hsplit, hbeforeLength, hvaluesLength]
    using hcovered)
  rw [hsplit] at hinflate hquotient'
  rw [hbeforeLength] at hinflate
  have hskeletonSimple := hquotient'.2.1
  have hskeletonLower : 2 ≤ skeleton.length := by omega
  have hskeletonNotThree : skeleton.length ≠ 3 := by
    intro hthree
    obtain ⟨first, second, third, hthreeShape⟩ := List.length_eq_three.mp hthree
    have hpermThree : [first, second, third].Perm (List.range' 1 3) := by
      simpa only [hthreeShape, List.length_cons, List.length_nil, Nat.reduceAdd]
        using hskeletonPerm
    have hentries : ∀ entry ∈ [first, second, third],
        entry = 1 ∨ entry = 2 ∨ entry = 3 := by
      intro entry hentry
      have hh := hpermThree.mem_iff.mp hentry
      simpa only [List.range'_succ, List.range'_zero, List.mem_cons, List.not_mem_nil,
        or_false, Nat.reduceAdd] using hh
    have hf := hentries first (by simp)
    have hs := hentries second (by simp)
    have ht := hentries third (by simp)
    have hn := hpermThree.nodup_iff.mpr (List.nodup_range' _)
    rw [hthreeShape] at hskeletonSimple
    rcases hf with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl <;>
      rcases ht with rfl | rfl | rfl
    all_goals try simp at hn
    all_goals first
      | exact hskeletonSimple 0 2 1 (by decide) (by decide) (by decide) (by decide)
      | exact hskeletonSimple 0 2 2 (by decide) (by decide) (by decide) (by decide)
      | exact hskeletonSimple 1 2 1 (by decide) (by decide) (by decide) (by decide)
      | exact hskeletonSimple 1 2 2 (by decide) (by decide) (by decide) (by decide)
  cases skeleton with
  | nil => simp at hskeletonLower
  | cons first rest =>
    cases rest with
    | nil => simp at hskeletonLower
    | cons pivot tail =>
      have hblockNormalized : block.Perm (List.range' 1 block.length) := hblockPerm
      have hblockSize : block.length = count := by omega
      have hblockNodup := hblockPerm.nodup_iff.mpr (List.nodup_range' _)
      have hblockBounds : ∀ entry ∈ block, 1 ≤ entry ∧ entry ≤ count := by
        intro entry hentry
        have hh := List.mem_range'_1.mp (hblockPerm.mem_iff.mp hentry)
        omega
      let up := fun entry => if pivot < entry then entry + count - 1 else entry
      let lift := fun entry => pivot + entry - 1
      have hqshape : permutation = up first :: (block.map lift ++ tail.map up) := by
        rw [← hinflate]
        simp [inflate, up, lift, hblockSize]
      have hslice : ((permutation.drop 1).take count) = block.map lift := by
        rw [hqshape]
        change (block.map lift ++ tail.map up).take count = block.map lift
        rw [
          List.take_append_of_le_length (by simp only [List.length_map]; omega),
          ← List.map_take, ← hblockSize, List.take_length]
      have hfirstValue : permutation.getD 0 0 = up first := by simp [hqshape]
      have hbetaValue : beta = lift (block.getD 0 0) := by
        have hnblock : 0 < block.length := by omega
        dsimp only [beta]
        rw [hqshape]
        change (block.map lift ++ tail.map up).getD 0 0 = _
        rw [List.getD_append _ _ 0 0 (by simp only [List.length_map]; omega)]
        rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_map,
          ← List.getD_eq_getElem _ 0 hnblock]
      have hblockFirstBounds := hblockBounds (block.getD 0 0) (by
        rw [List.getD_eq_getElem _ 0 (by omega)]; exact List.getElem_mem (by omega))
      have hpivotBounds : 1 ≤ pivot ∧ pivot ≤ tail.length + 2 := by
        have hh := List.mem_range'_1.mp (hskeletonPerm.mem_iff.mp
          (by simp : pivot ∈ first :: pivot :: tail))
        simp only [List.length_cons] at hh
        omega
      have hfirstBounds : 1 ≤ first ∧ first ≤ tail.length + 2 := by
        have hh := List.mem_range'_1.mp (hskeletonPerm.mem_iff.mp
          (by simp : first ∈ first :: pivot :: tail))
        simp only [List.length_cons] at hh
        omega
      have hascent : Occurs [1, 2] block := by
        have hnext : beta + 1 ∈ block.map lift := by
          rw [← hslice]
          exact hinterval.mem_iff.mpr (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
        obtain ⟨upper, hupperMem, hupperValue⟩ := List.mem_map.mp hnext
        obtain ⟨head, remaining, hblockShape⟩ :=
          List.exists_cons_of_length_pos (l := block) (by omega)
        have hhead : block.getD 0 0 = head := by simp [hblockShape]
        have horder : head < upper := by dsimp [lift] at *; omega
        have hupperTail : upper ∈ remaining := by
          rw [hblockShape, List.mem_cons] at hupperMem
          exact hupperMem.resolve_left (by omega)
        have hpair : [head, upper].Sublist block := by
          rw [hblockShape]
          exact (List.singleton_sublist.mpr hupperTail).cons_cons head
        let witness := fun rank => if rank = 1 then head else upper
        refine ⟨witness, ?_, ?_, ?_, by simp⟩
        · intro rank hpositive hupper
          have heq : rank = 1 := by simp at hupper; omega
          subst rank; simpa [witness] using horder
        · intro rank hpositive hupper
          have heq : rank = 1 ∨ rank = 2 := by simp at hupper; omega
          rcases heq with rfl | rfl <;> apply hpair.subset <;> simp [witness]
        · simpa [witness] using hpair
      by_cases hlarge : 4 ≤ (first :: pivot :: tail).length
      · by_cases hpivot : pivot = 1
        · subst pivot
          have hqshapeOne : permutation = (first + count - 1) ::
              (block ++ tail.map (fun entry => entry + count - 1)) := by
            have hskeletonNodup := hskeletonPerm.nodup_iff.mpr (List.nodup_range' _)
            have hfirstNot : first ≠ 1 := by
              intro heq; subst first; simp at hskeletonNodup
            have htailPositive : ∀ entry ∈ tail, 1 < entry := by
              intro entry hentry
              have hh := List.mem_range'_1.mp (hskeletonPerm.mem_iff.mp
                (by simp [hentry] : entry ∈ first :: 1 :: tail))
              have hn : entry ≠ 1 := by
                have hn := (List.nodup_cons.mp (List.nodup_cons.mp hskeletonNodup).2).1
                intro heq; exact hn (heq ▸ hentry)
              omega
            rw [hqshape]
            have hblockMap : block.map lift = block := by
              simp [lift]
            have htailMap : tail.map up = tail.map
                (fun entry => entry + count - 1) := by
              apply List.map_congr_left
              intro entry hentry
              dsimp only [up]
              rw [if_pos (htailPositive entry hentry)]
            rw [hblockMap, htailMap]
            dsimp only [up]
            rw [if_pos (by omega)]
          have hbetaBlock : block.getD 0 0 = beta := by simpa [lift] using hbetaValue.symm
          have hbetaSmall : beta < count := by
            have hnext : beta + 1 ∈ block := by
              have hh := hinterval.mem_iff.mpr
                (List.mem_range'_1.mpr ⟨by omega, by omega⟩ :
                  beta + 1 ∈ List.range' lower count)
              rw [hslice] at hh
              simpa [lift] using hh
            have hb := hblockBounds _ hnext
            omega
          have hfirstLarge : 2 < first := by
            have hn := hskeletonPerm.nodup_iff.mpr (List.nodup_range' _)
            have hnotOne : first ≠ 1 := by intro heq; subst first; simp at hn
            have hnotTwo : first ≠ 2 := by
              intro heq; subst first
              apply hskeletonSimple 0 2 1 (by decide) (by omega) (by simp)
              simp only [List.drop_zero, List.take_succ_cons, List.take_zero]
              exact (by decide : [2, 1].Perm (List.range' 1 2))
            omega
          have htwoTail : 2 ∈ tail := by
            have hh := hskeletonPerm.mem_iff.mpr
              (List.mem_range'_1.mpr ⟨by omega, by simp only [List.length_cons]; omega⟩ :
                2 ∈ List.range' 1 (first :: 1 :: tail).length)
            simp only [List.mem_cons] at hh
            exact (hh.resolve_left (by omega)).resolve_left (by decide)
          obtain ⟨head, remaining, hblockShape⟩ :=
            List.exists_cons_of_length_pos (l := block) (by omega)
          have hhead : head = beta := by simpa [hblockShape] using hbetaBlock
          subst head
          have hcut : ∃ low high, low < beta ∧ beta < high ∧
              [high, low].Sublist remaining := by
            by_contra hn
            have hdistinct : ∀ entry ∈ remaining, entry ≠ beta := by
              rw [hblockShape, List.nodup_cons] at hblockNodup
              intro entry hentry heq; exact hblockNodup.1 (heq ▸ hentry)
            have separate : ∀ rest : List ℕ, (∀ entry ∈ rest, entry ≠ beta) →
                (∀ low high, low < beta → beta < high → ¬ [high, low].Sublist rest) →
                ∃ left right, rest = left ++ right ∧
                  (∀ entry ∈ left, entry < beta) ∧ (∀ entry ∈ right, beta < entry) := by
              intro rest
              induction rest with
              | nil => intro _ _; exact ⟨[], [], rfl, by simp⟩
              | cons entry rest ih =>
                intro hne hno
                by_cases hlow : entry < beta
                · obtain ⟨left, right, heq, hleft, hright⟩ := ih
                    (fun other hother => hne other (by simp [hother]))
                    (fun low high hlo hhi hsub => hno low high hlo hhi (hsub.cons entry))
                  refine ⟨entry :: left, right, by simp [heq], ?_, hright⟩
                  intro other hother
                  rcases List.mem_cons.mp hother with rfl | hother
                  · exact hlow
                  · exact hleft other hother
                · have hhigh : beta < entry := by have hh := hne entry (by simp); omega
                  refine ⟨[], entry :: rest, rfl, by simp, ?_⟩
                  intro other hother
                  rcases List.mem_cons.mp hother with rfl | hother
                  · exact hhigh
                  · have hh := hne other (by simp [hother])
                    by_contra hnot
                    exact hno other entry (by omega) hhigh
                      ((List.singleton_sublist.mpr hother).cons_cons entry)
            obtain ⟨left, right, heq, hleft, hright⟩ := separate remaining hdistinct
              (by intro low high hlo hhi hsub; exact hn ⟨low, high, hlo, hhi, hsub⟩)
            have hprefSub : (beta :: left).Sublist block := by
              rw [hblockShape, heq]
              exact (List.sublist_append_left left right).cons_cons beta
            have hprefPerm : (beta :: left).Perm (List.range' 1 beta) := by
              apply (List.perm_ext_iff_of_nodup (hblockNodup.sublist hprefSub)
                (List.nodup_range' _)).mpr
              intro entry
              constructor
              · intro hentry
                have hb := hblockBounds entry (hprefSub.subset hentry)
                have hle : entry ≤ beta := by
                  rcases List.mem_cons.mp hentry with rfl | hentry
                  · omega
                  · have hh := hleft entry hentry; omega
                apply List.mem_range'_1.mpr; omega
              · intro hentry
                have hb := List.mem_range'_1.mp hentry
                have hall : entry ∈ block := hblockPerm.mem_iff.mpr
                  (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
                rw [hblockShape, heq, List.mem_cons, List.mem_append] at hall
                rcases hall with rfl | hall | hall
                · simp
                · exact List.mem_cons_of_mem _ hall
                · have hh := hright entry hall; omega
            have hprefLength : (beta :: left).length = beta := by
              simpa only [List.length_range'] using hprefPerm.length_eq
            have hprefSlice : (permutation.drop 1).take beta = beta :: left := by
              rw [hqshapeOne]
              change (block ++ tail.map (fun entry => entry + count - 1)).take beta = _
              rw [hblockShape, heq, ← List.cons_append, List.append_assoc]
              have hh : (((beta :: left) ++
                  (right ++ tail.map (fun entry => entry + count - 1))).take
                  (beta :: left).length) = beta :: left := List.take_left
              simpa only [hprefLength] using hh
            have hh := hrestr 1 beta 1 (by omega) (by omega) (by omega)
              (by rw [hprefSlice]; exact hprefPerm)
            omega
          obtain ⟨low, high, hlo, hhi, hsub⟩ := hcut
          have hselected : [first + count - 1, beta, high, low, count + 1].Sublist
              permutation := by
            rw [hqshapeOne]
            apply List.Sublist.cons_cons
            have hblockSub : [beta, high, low].Sublist block := by
              rw [hblockShape]; exact hsub.cons_cons beta
            have htailSub : [count + 1].Sublist
                (tail.map (fun entry => entry + count - 1)) := by
              exact List.singleton_sublist.mpr (List.mem_map.mpr
                ⟨2, htwoTail, by omega⟩)
            simpa using hblockSub.append htailSub
          have hhighBounds := hblockBounds high
            (by rw [hblockShape]; exact List.mem_cons_of_mem _ (hsub.subset (by simp)))
          let witness := fun rank => match rank with
            | 1 => low
            | 2 => beta
            | 3 => high
            | 4 => count + 1
            | _ => first + count - 1
          apply hC [5, 2, 3, 1, 4] (by decide)
          refine ⟨witness, ?_, ?_, ?_, by simp⟩
          · intro rank hpositive hupper
            have hcases : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by
              simp at hupper; omega
            rcases hcases with rfl | rfl | rfl | rfl <;>
              simp only [witness, Nat.reduceAdd] <;> omega
          · intro rank hpositive hupper
            have hcases : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 ∨ rank = 5 := by
              simp at hupper; omega
            rcases hcases with rfl | rfl | rfl | rfl | rfl <;>
              apply hselected.subset <;> simp [witness]
          · simpa [witness] using hselected
        · have hocc := ascending_second_inflation first pivot tail block
            (by simpa using hskeletonPerm) hskeletonSimple (by simp at hlarge; omega)
            hpivot hblockNormalized hascent
          rw [hinflate] at hocc
          exact hC [2, 3, 4, 1] (by decide) hocc
      · have htwo : (first :: pivot :: tail).length = 2 := by omega
        have htail : tail = [] := by simpa using htwo
        subst tail
        have hfirstCases : first = 1 ∨ first = 2 := by
          have hh := List.mem_range'_1.mp (hskeletonPerm.mem_iff.mp
            (by simp : first ∈ [first, pivot]))
          simp only [List.length_cons, List.length_nil] at hh
          omega
        have hpivotCases : pivot = 1 ∨ pivot = 2 := by
          have hh := List.mem_range'_1.mp (hskeletonPerm.mem_iff.mp
            (by simp : pivot ∈ [first, pivot]))
          simp only [List.length_cons, List.length_nil] at hh
          omega
        have hn := hskeletonPerm.nodup_iff.mpr (List.nodup_range' _)
        rcases hfirstCases with rfl | rfl <;> rcases hpivotCases with rfl | rfl
        · simp at hn
        · have hh : permutation.getD 0 0 = 1 := by simpa [up] using hfirstValue
          omega
        · have hh : permutation.getD 0 0 = count + 1 := by
            simpa [up, Nat.add_comm] using hfirstValue
          have hwholeLength : permutation.length = count + 1 := by
            rw [hqshape]
            simp [hblockSize]
          omega
        · simp at hn

end D5.S3.Combinatorics.PopStack.PopStackContinuationReflection
