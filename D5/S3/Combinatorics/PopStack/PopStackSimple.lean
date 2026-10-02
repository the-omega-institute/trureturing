/- GID: D5/S3/Combinatorics/PopStack/PopStackSimple
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackSimple
   mirror-E: none(waiver:augmented-family-recursive-counting)
   anchors: [mathlib/module/Mathlib.Data.List.Permutation]
   utility: none
   digest: Counting the three minimum-position branches gives the Fibonacci enumeration. -/
import D5.S3.Combinatorics.PopStack.PopStackThirdEquivalence
import D5.S3.Combinatorics.PopStack.PopStackContinuationReflection
import D5.S3.Combinatorics.PopStack.PopStackContinuationAvoidance
import Mathlib.Data.List.Permutation
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.PopStack.PopStackSimple
open PopStackDefs PopStackExtra PopStackParallel PopStackVerticalContinuation
open PopStackMinimumBijection PopStackThirdBijection PopStackContinuation
open PopStackContinuationAvoidance PopStackContinuationReflection
open PopStackMaximumShape PopStackMaximumIntervals
open PopStackMaximumInsertion PopStackMaximumDeletion
theorem result : PopStackDefs.claim := by
  have hcontinuation (size : ℕ) (hsize : 4 ≤ size) :
      let source := {permutation : List ℕ | permutation ∈ augmented size ∧
        permutation.idxOf 1 ≠ 1}
      let target := {permutation : List ℕ | permutation ∈ augmented (size + 1) ∧
        3 ≤ permutation.idxOf 1}
      Set.BijOn V source target ∧
        (∀ permutation ∈ source, undoV (V permutation) = permutation) ∧
        (∀ permutation ∈ target, V (undoV permutation) = permutation) := by
    classical
    have hPlength : ∀ half, (P half).length = 2 * half := fun _ => List.length_ofFn
    have hElength : ∀ half, (E half).length = 2 * half + 1 := by
      intro half
      simp only [E, List.length_append, List.length_map, List.length_singleton, hPlength]
    have hindex : ∀ (permutation : List ℕ) index,
        permutation.Perm (List.range' 1 permutation.length) → index < permutation.length →
        permutation.getD index 0 = 1 → permutation.idxOf 1 = index := by
      intro permutation index hperm hbound hvalue
      have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
      have hh := List.get_idxOf hnodup ⟨index, hbound⟩
      have hget : permutation.get ⟨index, hbound⟩ = 1 := by
        simpa only [List.get_eq_getElem, List.getD_eq_getElem _ 0 hbound] using hvalue
      simpa only [hget] using hh
    have hPentry : ∀ half index, index < 2 * half → (P half).getD index 0 =
        if index % 2 = 0 then half - index / 2 else 2 * half - index / 2 := by
      intro half index hindex; rw [List.getD_eq_getElem _ _ (by rw [hPlength]; exact hindex)]
      simp only [P, List.getElem_ofFn]
    have hEentry : ∀ half index, index < 2 * half → (E half).getD index 0 =
        (if index % 2 = 0 then half - index / 2 else 2 * half - index / 2) + 1 := by
      intro half index hindex; rw [E, List.getD_append _ _ _ _ (by simp [hPlength]; omega)]
      rw [List.getD_eq_getElem _ _ (by simp [hPlength]; omega), List.getElem_map]
      rw [← List.getD_eq_getElem _ 0 (by rw [hPlength]; exact hindex), hPentry _ _ hindex]
    have hPfacts : ∀ half, 2 ≤ half → (P half).getD 1 0 = 2 * half ∧
        (P half).idxOf 1 = 2 * half - 2 ∧
        (P half).Perm (List.range' 1 (2 * half)) ∧ InC (P half) ∧ IsSimple (P half) := by
      intro half hhalf; obtain ⟨hperm, _, hC, hsimple⟩ := parallel_simple half (by omega)
      refine ⟨?_, ?_, hperm, hC, hsimple⟩
      · rw [hPentry _ _ (by omega)]; simp
      · apply hindex _ _ (by simpa only [hPlength] using hperm) (by rw [hPlength]; omega)
        rw [hPentry _ _ (by omega)]
        split_ifs <;> omega
    have hEfacts : ∀ half, 2 ≤ half → (E half).getD 1 0 = 2 * half + 1 ∧
        (E half).idxOf 1 = 2 * half ∧
        (E half).Perm (List.range' 1 (2 * half + 1)) ∧ InC (E half) := by
      intro half hhalf; obtain ⟨hperm, hC, _⟩ := odd_extra half (by omega)
      refine ⟨?_, ?_, hperm, hC⟩
      · rw [hEentry _ _ (by omega)]; simp
      · apply hindex _ _ (by simpa only [hElength] using hperm) (by rw [hElength]; omega)
        rw [E, List.getD_append_right _ _ _ _ (by simp [hPlength])]; simp [hPlength]
    have hmember : ∀ current permutation, 4 ≤ current → permutation ∈ augmented current →
        permutation.length = current ∧ permutation.Perm (List.range' 1 current) ∧
        InC permutation ∧ (IsSimple permutation ∨ permutation = E (current / 2)) := by
      intro current permutation hcurrent hmem
      rcases hmem with hsimple | hextra
      · exact ⟨by simpa using hsimple.1.length_eq, hsimple.1, hsimple.2.1,
          Or.inl hsimple.2.2⟩
      · have hodd : current % 2 = 1 ∧ 3 ≤ current := by
          by_contra hnot
          simp only [if_neg hnot, Set.mem_empty_iff_false] at hextra
        have heq : permutation = E (current / 2) := by
          simpa only [if_pos hodd, Set.mem_singleton_iff] using hextra
        subst permutation
        obtain ⟨hperm, hC, _⟩ := odd_extra (current / 2) (by omega)
        have hcurrentEq : 2 * (current / 2) + 1 = current := by omega
        exact ⟨by rw [hElength, hcurrentEq], by simpa only [hcurrentEq] using hperm,
          hC, Or.inr rfl⟩
    have hverticalAssertion :
        let source := {permutation : List ℕ | permutation ∈ augmented size ∧
          permutation.getD 1 0 = size ∧ 2 ≤ permutation.idxOf 1}
        let target := {permutation : List ℕ | permutation ∈ augmented (size + 1) ∧
          permutation.getD 1 0 = size + 1 ∧ 3 ≤ permutation.idxOf 1}
        Set.BijOn V source target ∧
          (∀ permutation ∈ source, undoV (V permutation) = permutation) ∧
          (∀ permutation ∈ target, V (undoV permutation) = permutation) := by
      classical
      let source := {permutation : List ℕ | permutation ∈ augmented size ∧
        permutation.getD 1 0 = size ∧ 2 ≤ permutation.idxOf 1}
      let target := {permutation : List ℕ | permutation ∈ augmented (size + 1) ∧
        permutation.getD 1 0 = size + 1 ∧ 3 ≤ permutation.idxOf 1}
      change Set.BijOn V source target ∧
        (∀ permutation ∈ source, undoV (V permutation) = permutation) ∧
        (∀ permutation ∈ target, V (undoV permutation) = permutation)
      have hswitch : ∀ half, 2 ≤ half → V (P half) = E half ∧
          undoV (E half) = P half ∧ V (E half) = P (half + 1) ∧
          undoV (P (half + 1)) = E half := by
        intro half hhalf; have hPnotE : ∀ current, P current ≠ E current := by
          intro current heq; have hh := congrArg List.length heq; rw [hPlength, hElength] at hh
          omega
        have hEappend : (E half).map
            (fun entry => if half + 2 ≤ entry then entry + 1 else entry) ++ [half + 2] =
            P (half + 1) := by
          apply List.ext_getElem
          · simp [hPlength, hElength]; omega
          · intro index hleft hright
            have hbound : index < 2 * (half + 1) := by simpa only [hPlength] using hright
            rw [← List.getD_eq_getElem _ 0 hleft, ← List.getD_eq_getElem _ 0 hright]
            rw [hPentry _ _ hbound]
            by_cases hold : index < 2 * half
            · rw [List.getD_append _ _ _ _ (by simp [hElength]; omega)]
              rw [List.getD_eq_getElem _ _ (by simp [hElength]; omega), List.getElem_map,
                ← List.getD_eq_getElem _ 0 (by rw [hElength]; omega), hEentry _ _ hold]
              split_ifs <;> omega
            · by_cases hlast : index = 2 * half
              · subst index
                rw [List.getD_append _ _ _ _ (by simp [hElength])]
                rw [List.getD_eq_getElem _ _ (by simp [hElength]), List.getElem_map,
                  ← List.getD_eq_getElem _ 0 (by rw [hElength]; omega)]
                rw [E, List.getD_append_right _ _ _ _ (by simp [hPlength])]; simp [hPlength]
              · have hfinal : index = 2 * half + 1 := by omega
                subst index
                rw [List.getD_append_right _ _ _ _ (by simp [hElength])]; simp [hElength]; omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp [V, hPlength]
        · have hquot : (2 * half + 1) / 2 = half := by omega
          simp only [undoV, hElength, hquot, if_true]
        · have hnot : E half ≠ P half := Ne.symm (hPnotE half)
          have hquot : (2 * half + 1) / 2 = half := by omega
          have hrank : (2 * half + 1 + 3) / 2 = half + 2 := by omega
          simpa only [V, hElength, hquot, hrank, if_neg hnot, if_true] using hEappend
        · have hquot : 2 * (half + 1) / 2 = half + 1 := by omega
          simp only [undoV, hPlength, hquot, if_neg (hPnotE _), if_true, Nat.add_sub_cancel]
      have hPmember : ∀ half, 2 ≤ half → P half ∈ augmented (2 * half) := by
        intro half hhalf
        obtain ⟨_, _, hperm, hC, hsimple⟩ := hPfacts half hhalf; exact Or.inl ⟨hperm, hC, hsimple⟩
      have hEmember : ∀ half, 2 ≤ half → E half ∈ augmented (2 * half + 1) := by
        intro half hhalf
        right
        have hodd : (2 * half + 1) % 2 = 1 ∧ 3 ≤ 2 * half + 1 := by omega
        have hquot : (2 * half + 1) / 2 = half := by omega
        simp only [if_pos hodd, hquot, Set.mem_singleton_iff]
      have hforward : ∀ permutation ∈ source,
          V permutation ∈ target ∧ undoV (V permutation) = permutation := by
        intro permutation hsource; obtain ⟨haugmented, hmaximum, hlater⟩ := hsource
        obtain ⟨hlength, hpermSize, hC, hsimpleOr⟩ := hmember size permutation hsize haugmented
        have hperm : permutation.Perm (List.range' 1 permutation.length) := by
          simpa only [hlength] using hpermSize
        have hhalf : 2 ≤ size / 2 := by omega
        by_cases hisP : permutation = P (permutation.length / 2)
        · have hsizeEq : size = 2 * (size / 2) := by
            have hh := congrArg List.length hisP; simpa only [hPlength, hlength] using hh
          have heq : permutation = P (size / 2) := by simpa only [hlength] using hisP
          obtain ⟨hV, hundo, _, _⟩ := hswitch _ hhalf; rw [heq, hV]
          refine ⟨⟨?_, ?_, ?_⟩, hundo⟩
          · simpa only [show 2 * (size / 2) + 1 = size + 1 from by omega] using
              hEmember (size / 2) hhalf
          · simpa only [← hsizeEq] using (hEfacts _ hhalf).1
          · rw [(hEfacts _ hhalf).2.1]; omega
        by_cases hisE : permutation = E (permutation.length / 2)
        · have hsizeEq : size = 2 * (size / 2) + 1 := by
            have hh := congrArg List.length hisE; simpa only [hElength, hlength] using hh
          have heq : permutation = E (size / 2) := by simpa only [hlength] using hisE
          obtain ⟨_, _, hV, hundo⟩ := hswitch _ hhalf; rw [heq, hV]
          refine ⟨⟨?_, ?_, ?_⟩, hundo⟩
          · simpa only [show 2 * (size / 2 + 1) = size + 1 from by omega] using
              hPmember (size / 2 + 1) (by omega)
          · rw [(hPfacts (size / 2 + 1) (by omega)).1]; omega
          · rw [(hPfacts (size / 2 + 1) (by omega)).2.1]; omega
        have hsimple : IsSimple permutation := by
          rcases hsimpleOr with hh | heq
          · exact hh
          · exact False.elim (hisE (by simpa only [hlength] using heq))
        have hmaximumLength : permutation.getD 1 0 = permutation.length := by
          simpa only [hlength] using hmaximum
        obtain ⟨hupper, hlower⟩ := (maximum_second_shape permutation hperm
          (by omega) hmaximumLength).2 hC hsimple
        have hbonds := (maximum_second_intervals permutation hperm (by omega)
          hmaximumLength hupper hlower).2.mpr (Or.inl hsimple)
        have hone : 1 ∈ permutation :=
          hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
        have hminimumBound := List.idxOf_lt_length_iff.mpr hone
        have hminimum : permutation.getD (permutation.idxOf 1) 0 = 1 := by
          rw [List.getD_eq_getElem _ _ hminimumBound, List.getElem_idxOf]
        obtain ⟨hnewPerm, hnewMaximum, hnewMinimum, hnewC, hnewSimple,
          hnewNotP, hnewNotE, hrecover⟩ := maximum_second_insertion permutation hperm
            (by omega) hmaximumLength hupper hlower hbonds (permutation.idxOf 1)
            hlater hminimumBound hminimum hisP hisE
        let rank := if permutation.idxOf 1 % 2 = 0 then
          permutation.getD 0 0 - permutation.idxOf 1 / 2 + 1
          else permutation.length - (permutation.idxOf 1 - 1) / 2 + 1
        let member := (permutation.map
          (fun entry => if rank ≤ entry then entry + 1 else entry)).insertIdx
            (permutation.idxOf 1) rank
        change member.Perm (List.range' 1 member.length) at hnewPerm
        change member.getD 1 0 = member.length at hnewMaximum
        change member.getD (permutation.idxOf 1 + 1) 0 = 1 at hnewMinimum
        change member ≠ P (member.length / 2) at hnewNotP
        change member ≠ E (member.length / 2) at hnewNotE
        change (member.eraseIdx (permutation.idxOf 1)).map
          (fun entry => if rank < entry then entry - 1 else entry) = permutation at hrecover
        have hV : V permutation = member := by
          simp only [V, if_neg hisP, if_neg hisE,
            if_neg (by omega : ¬ permutation.getD 1 0 < permutation.length)]
          rfl
        have hnewLength : member.length = size + 1 := by
          simp only [member, List.length_insertIdx, List.length_map]
          split_ifs <;> omega
        have hnewIndex : member.idxOf 1 = permutation.idxOf 1 + 1 :=
          hindex member _ hnewPerm (by omega) hnewMinimum
        have hnewRank : member.getD (permutation.idxOf 1) 0 = rank := by
          simp only [member, List.getD_eq_getElem _ _ (by omega :
            permutation.idxOf 1 < member.length)]
          exact List.getElem_insertIdx_self (by
            change permutation.idxOf 1 < member.length
            omega)
        rw [hV]
        refine ⟨⟨Or.inl ⟨?_, hnewC, hnewSimple⟩, ?_, ?_⟩, ?_⟩
        · simpa only [hnewLength] using hnewPerm
        · simpa only [hnewLength] using hnewMaximum
        · rw [hnewIndex]; omega
        · simp only [undoV, if_neg hnewNotE, if_neg hnewNotP,
            if_neg (by omega : ¬ member.getD 1 0 < member.length), hnewIndex,
            Nat.add_sub_cancel, hnewRank]
          exact hrecover
      have hbackward : ∀ permutation ∈ target,
          undoV permutation ∈ source ∧ V (undoV permutation) = permutation := by
        intro permutation htarget; obtain ⟨haugmented, hmaximum, hlater⟩ := htarget
        obtain ⟨hlength, hpermSize, hC, hsimpleOr⟩ :=
          hmember (size + 1) permutation (by omega) haugmented
        have hperm : permutation.Perm (List.range' 1 permutation.length) := by
          simpa only [hlength] using hpermSize
        by_cases hisE : permutation = E (permutation.length / 2)
        · have hsizeEq : size + 1 = 2 * ((size + 1) / 2) + 1 := by
            have hh := congrArg List.length hisE; simpa only [hElength, hlength] using hh
          have hhalf : 2 ≤ (size + 1) / 2 := by omega
          have heq : permutation = E ((size + 1) / 2) := by simpa only [hlength] using hisE
          obtain ⟨hV, hundo, _, _⟩ := hswitch _ hhalf; rw [heq, hundo]
          refine ⟨⟨?_, ?_, ?_⟩, hV⟩
          · simpa only [show 2 * ((size + 1) / 2) = size from by omega] using
              hPmember ((size + 1) / 2) hhalf
          · rw [(hPfacts _ hhalf).1]; omega
          · rw [(hPfacts _ hhalf).2.1]; omega
        by_cases hisP : permutation = P (permutation.length / 2)
        · have hsizeEq : size + 1 = 2 * ((size + 1) / 2) := by
            have hh := congrArg List.length hisP; simpa only [hPlength, hlength] using hh
          have hhalf : 2 ≤ (size + 1) / 2 - 1 := by omega
          have heq : permutation = P ((size + 1) / 2 - 1 + 1) := by
            rw [hisP, hlength]; congr 1; omega
          obtain ⟨_, _, hV, hundo⟩ := hswitch _ hhalf; rw [heq, hundo]
          refine ⟨⟨?_, ?_, ?_⟩, hV⟩
          · simpa only [show 2 * ((size + 1) / 2 - 1) + 1 = size from by omega] using
              hEmember ((size + 1) / 2 - 1) hhalf
          · rw [(hEfacts _ hhalf).1]; omega
          · rw [(hEfacts _ hhalf).2.1]; omega
        have hsimple : IsSimple permutation := by
          rcases hsimpleOr with hh | heq
          · exact hh
          · exact False.elim (hisE (by simpa only [hlength] using heq))
        have hmaximumLength : permutation.getD 1 0 = permutation.length := by
          simpa only [hlength] using hmaximum
        obtain ⟨hupper, hlower⟩ := (maximum_second_shape permutation hperm
          (by omega) hmaximumLength).2 hC hsimple
        have hbonds := (maximum_second_intervals permutation hperm (by omega)
          hmaximumLength hupper hlower).2.mpr (Or.inl hsimple)
        have hone : 1 ∈ permutation :=
          hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
        have hminimumBound := List.idxOf_lt_length_iff.mpr hone
        have hminimum : permutation.getD (permutation.idxOf 1) 0 = 1 := by
          rw [List.getD_eq_getElem _ _ hminimumBound, List.getElem_idxOf]
        obtain ⟨hnewPerm, hnewC, hnewSimple, hnewMaximum, hnewMinimum,
          hnewNotP, hnewNotE, hrecover⟩ := maximum_second_deletion permutation hperm
            (by omega) hmaximumLength hupper hlower hbonds (permutation.idxOf 1)
            hlater hminimumBound hminimum hisP hisE
        let cut := permutation.idxOf 1 - 1
        let rank := permutation.getD cut 0
        let predecessor := (permutation.eraseIdx cut).map
          (fun entry => if rank < entry then entry - 1 else entry)
        change predecessor.Perm (List.range' 1 predecessor.length) at hnewPerm
        change predecessor.getD 1 0 = predecessor.length at hnewMaximum
        change predecessor.getD cut 0 = 1 at hnewMinimum
        change predecessor ≠ P (predecessor.length / 2) at hnewNotP
        change predecessor ≠ E (predecessor.length / 2) at hnewNotE
        have hundo : undoV permutation = predecessor := by
          simp only [undoV, if_neg hisE, if_neg hisP,
            if_neg (by omega : ¬ permutation.getD 1 0 < permutation.length)]
          rfl
        have hnewLength : predecessor.length = size := by
          simp only [predecessor, List.length_map, List.length_eraseIdx]
          split_ifs <;> omega
        have hnewIndex : predecessor.idxOf 1 = cut :=
          hindex predecessor _ hnewPerm (by omega) hnewMinimum
        rw [hundo]
        refine ⟨⟨Or.inl ⟨?_, hnewC, hnewSimple⟩, ?_, ?_⟩, ?_⟩
        · simpa only [hnewLength] using hnewPerm
        · simpa only [hnewLength] using hnewMaximum
        · rw [hnewIndex]; dsimp only [cut]; omega
        · simp only [V, if_neg hnewNotP, if_neg hnewNotE,
            if_neg (by omega : ¬ predecessor.getD 1 0 < predecessor.length), hnewIndex]
          exact hrecover
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · intro permutation hsource; exact (hforward permutation hsource).1
      · intro first hfirst second hsecond heq; have hh := congrArg undoV heq
        simpa only [(hforward first hfirst).2, (hforward second hsecond).2] using hh
      · intro permutation htarget; exact ⟨undoV permutation, (hbackward permutation htarget).1,
          (hbackward permutation htarget).2⟩
      · intro permutation hsource; exact (hforward permutation hsource).2
      · intro permutation htarget; exact (hbackward permutation htarget).2
    obtain ⟨hvertical, hverticalLeft, hverticalRight⟩ := hverticalAssertion
    let source := {permutation : List ℕ | permutation ∈ augmented size ∧
      permutation.idxOf 1 ≠ 1}
    let target := {permutation : List ℕ | permutation ∈ augmented (size + 1) ∧
      3 ≤ permutation.idxOf 1}
    change Set.BijOn V source target ∧
      (∀ permutation ∈ source, undoV (V permutation) = permutation) ∧
      (∀ permutation ∈ target, V (undoV permutation) = permutation)
    have hEfirst : ∀ half, 1 ≤ half → (E half).getD 0 0 = half + 1 := by
      intro half hhalf; rw [E, List.getD_append _ _ _ _ (by simp [hPlength]; omega)]
      rw [List.getD_eq_getElem _ _ (by simp [hPlength]; omega), List.getElem_map]; simp [P]
    have hnotExceptional : ∀ permutation : List ℕ, 4 ≤ permutation.length →
        permutation.getD 1 0 < permutation.length →
        permutation ≠ P (permutation.length / 2) ∧
        permutation ≠ E (permutation.length / 2) := by
      intro permutation hlength hsecond
      constructor
      · intro heq; have hh := congrArg List.length heq; rw [hPlength] at hh
        have hv := (hPfacts (permutation.length / 2) (by omega)).1
        rw [← heq] at hv; omega
      · intro heq; have hh := congrArg List.length heq; rw [hElength] at hh
        have hv := (hEfacts (permutation.length / 2) (by omega)).1
        rw [← heq] at hv; omega
    have hbounds : ∀ (permutation : List ℕ) index,
        permutation.Perm (List.range' 1 permutation.length) → index < permutation.length →
        1 ≤ permutation.getD index 0 ∧ permutation.getD index 0 ≤ permutation.length := by
      intro permutation index hperm hindex; have hmem : permutation.getD index 0 ∈ permutation := by
        rw [List.getD_eq_getElem _ 0 hindex]; exact List.getElem_mem hindex
      have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hmem); omega
    have hforward : ∀ permutation ∈ source,
        V permutation ∈ target ∧ undoV (V permutation) = permutation := by
      intro permutation hsource; obtain ⟨haugmented, hnotSecond⟩ := hsource
      obtain ⟨hlength, hpermSize, hC, hsimpleOr⟩ := hmember size permutation hsize haugmented
      have hperm : permutation.Perm (List.range' 1 permutation.length) := by
        simpa only [hlength] using hpermSize
      have hone : 1 ∈ permutation :=
        hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      have hminimumBound := List.idxOf_lt_length_iff.mpr hone
      have hminimum : permutation.getD (permutation.idxOf 1) 0 = 1 := by
        rw [List.getD_eq_getElem _ _ hminimumBound, List.getElem_idxOf]
      have hlater : 2 ≤ permutation.idxOf 1 := by
        by_contra hnot
        have hzero : permutation.idxOf 1 = 0 := by omega
        have hfirst : permutation.getD 0 0 = 1 := by simpa only [hzero] using hminimum
        rcases hsimpleOr with hsimple | hextra
        · have hhead : permutation = 1 :: permutation.drop 1 := by
            have hh := List.drop_eq_getElem?_toList_append (l := permutation) (i := 0)
            rw [List.getElem?_eq_getElem (by omega),
              ← List.getD_eq_getElem permutation 0 (by omega), hfirst] at hh
            simpa only [List.drop_zero, Option.toList_some, List.singleton_append] using hh
          have htailLength : (permutation.drop 1).length + 1 = permutation.length := by
            simp only [List.length_drop]; omega
          have hrest := (List.Perm.of_eq hhead.symm).trans hperm
          rw [← htailLength, List.range'_succ] at hrest
          have hh := hsimple 1 (permutation.drop 1).length 2 (by omega) (by omega) (by omega)
          rw [List.take_length] at hh; exact hh hrest.cons_inv
        · have hh := hEfirst (size / 2) (by omega); rw [← hextra, hfirst] at hh; omega
      have hsecondBound := hbounds permutation 1 hperm (by omega)
      by_cases hmaximum : permutation.getD 1 0 = size
      · have hverticalSource := And.intro haugmented (And.intro hmaximum hlater)
        have hverticalTarget := hvertical.mapsTo hverticalSource
        exact ⟨⟨hverticalTarget.1, hverticalTarget.2.2⟩,
          hverticalLeft permutation hverticalSource⟩
      have hsecond : permutation.getD 1 0 < permutation.length := by omega
      obtain ⟨hnotP, hnotE⟩ := hnotExceptional permutation (by omega) hsecond
      have hsimple : IsSimple permutation := by
        rcases hsimpleOr with hh | heq
        · exact hh
        · exact False.elim (hnotE (by simpa only [hlength] using heq))
      let alpha := permutation.getD 0 0
      let beta := permutation.getD 1 0
      have hhead : permutation = alpha :: permutation.drop 1 := by
        have hh := List.drop_eq_getElem?_toList_append (l := permutation) (i := 0)
        rw [List.getElem?_eq_getElem (by omega),
          ← List.getD_eq_getElem permutation 0 (by omega)] at hh
        simpa only [List.drop_zero, Option.toList_some, List.singleton_append] using hh
      have hpair : permutation = alpha :: beta :: permutation.drop 2 := by
        have hh := List.drop_eq_getElem?_toList_append (l := permutation) (i := 1)
        rw [List.getElem?_eq_getElem (by omega),
          ← List.getD_eq_getElem permutation 0 (by omega)] at hh
        calc
          permutation = alpha :: permutation.drop 1 := hhead
          _ = alpha :: beta :: permutation.drop 2 := by
            congr 1
      have hbond : alpha ≠ beta + 1 := by
        intro heq; have hh := hsimple 0 2 beta (by omega) (by omega) (by omega); rw [hpair] at hh
        simp only [List.drop_zero, List.take_succ_cons, List.take_zero] at hh
        apply hh
        rw [List.range'_succ, List.range'_succ, List.range'_zero, heq]; exact List.Perm.swap _ _ []
      have halphaBound := hbounds permutation 0 hperm (by omega)
      have halphaNotMaximum : alpha ≠ permutation.length := by
        intro heq; have htailLength : (permutation.drop 1).length + 1 = permutation.length := by
          simp only [List.length_drop]; omega
        have hrange : (List.range' 1 permutation.length).Perm
            (permutation.length :: List.range' 1 (permutation.drop 1).length) := by
          rw [← htailLength, List.range'_1_concat]; simpa only [Nat.add_comm] using
            List.perm_append_singleton (1 + (permutation.drop 1).length)
              (List.range' 1 (permutation.drop 1).length)
        have hrest := hperm.trans hrange; have hrest' := (List.Perm.of_eq hhead.symm).trans hrest
        rw [heq] at hrest'
        have hh := hsimple 1 (permutation.drop 1).length 1 (by omega) (by omega) (by omega)
        rw [List.take_length] at hh; exact hh hrest'.cons_inv
      obtain ⟨hnewC, hnewProperties⟩ := ordinary_continuation permutation hperm
        (by omega) hC hsecond hbond
      obtain ⟨hnewPermSize, hnewSimple⟩ := hnewProperties (by omega) hsimple
      have hnewLength : (W permutation).length = size + 1 := by simp [W, hlength]
      have hnewPerm : (W permutation).Perm (List.range' 1 (W permutation).length) := by
        simpa only [hnewLength, hlength] using hnewPermSize
      let shift := fun entry => if beta < entry then entry + 1 else entry
      have hshiftZero : shift 0 = 0 := by simp [shift, beta]
      have hshiftGet : ∀ index, (permutation.map shift).getD index 0 =
          shift (permutation.getD index 0) := by
        intro index; simpa only [hshiftZero] using (List.getD_map permutation 0 (n := index) shift)
      have hnewSecond : (W permutation).getD 1 0 < (W permutation).length := by
        change (permutation.map shift).getD 0 0 < (W permutation).length; rw [hshiftGet, hnewLength]
        change (if beta < alpha then alpha + 1 else alpha) < size + 1
        split_ifs <;> omega
      obtain ⟨hnewNotP, hnewNotE⟩ := hnotExceptional (W permutation) (by omega) hnewSecond
      have hnewMinimum : (W permutation).getD (permutation.idxOf 1 + 1) 0 = 1 := by
        change (permutation.map shift).getD (permutation.idxOf 1) 0 = 1; rw [hshiftGet, hminimum]
        dsimp only [shift, beta]
        split_ifs <;> omega
      have hnewIndex : (W permutation).idxOf 1 = permutation.idxOf 1 + 1 :=
        hindex _ _ hnewPerm (by omega) hnewMinimum
      have hV : V permutation = W permutation := by
        simp only [V, if_neg hnotP, if_neg hnotE, if_pos hsecond]
      rw [hV]
      refine ⟨⟨Or.inl ⟨?_, hnewC, hnewSimple⟩, ?_⟩, ?_⟩
      · simpa only [hlength] using hnewPermSize
      · rw [hnewIndex]; omega
      · simp only [undoV, if_neg hnewNotE, if_neg hnewNotP, if_pos hnewSecond]
        change (permutation.map shift).map
          (fun entry => if beta + 1 < entry then entry - 1 else entry) = permutation
        have hcancel : ∀ entry, (if beta + 1 < shift entry then shift entry - 1
            else shift entry) = entry := by
          intro entry; dsimp only [shift]
          split_ifs <;> omega
        simp only [List.map_map, Function.comp_def, hcancel]; simp
    have hbackward : ∀ permutation ∈ target,
        undoV permutation ∈ source ∧ V (undoV permutation) = permutation := by
      intro permutation htarget; obtain ⟨haugmented, hlater⟩ := htarget
      obtain ⟨hlength, hpermSize, hC, hsimpleOr⟩ :=
        hmember (size + 1) permutation (by omega) haugmented
      have hperm : permutation.Perm (List.range' 1 permutation.length) := by
        simpa only [hlength] using hpermSize
      have hsecondBound := hbounds permutation 1 hperm (by omega)
      by_cases hmaximum : permutation.getD 1 0 = size + 1
      · have hverticalTarget := And.intro haugmented (And.intro hmaximum hlater)
        obtain ⟨predecessor, hpredecessor, hV⟩ := hvertical.surjOn hverticalTarget
        have hundo := hverticalLeft predecessor hpredecessor; rw [hV] at hundo; rw [hundo]
        refine ⟨⟨hpredecessor.1, ?_⟩, hV⟩
        have hh := hpredecessor.2.2; omega
      have hsecond : permutation.getD 1 0 < permutation.length := by omega
      obtain ⟨hnotP, hnotE⟩ := hnotExceptional permutation (by omega) hsecond
      have hsimple : IsSimple permutation := by
        rcases hsimpleOr with hh | heq
        · exact hh
        · exact False.elim (hnotE (by simpa only [hlength] using heq))
      have hone : 1 ∈ permutation :=
        hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      have hminimumBound := List.idxOf_lt_length_iff.mpr hone
      have hminimum : permutation.getD (permutation.idxOf 1) 0 = 1 := by
        rw [List.getD_eq_getElem _ _ hminimumBound, List.getElem_idxOf]
      obtain ⟨hnewPerm, hnewC, hnewSimple, hnewSecond, hnewMinimum, hrecover⟩ :=
        ordinary_continuation_inverse permutation hperm hC hsimple (permutation.idxOf 1)
          hlater hminimumBound hminimum hsecond
      let predecessor := (permutation.drop 1).map
        (fun entry => if permutation.getD 0 0 < entry then entry - 1 else entry)
      change predecessor.Perm (List.range' 1 predecessor.length) at hnewPerm
      change predecessor.getD 1 0 < predecessor.length at hnewSecond
      have hnewLength : predecessor.length = size := by
        simp only [predecessor, List.length_map, List.length_drop]; omega
      have hnewIndex : predecessor.idxOf 1 = permutation.idxOf 1 - 1 :=
        hindex predecessor _ hnewPerm (by omega) hnewMinimum
      obtain ⟨hnewNotP, hnewNotE⟩ := hnotExceptional predecessor (by omega) hnewSecond
      have hundo : undoV permutation = predecessor := by
        simp only [undoV, if_neg hnotE, if_neg hnotP, if_pos hsecond]; rfl
      rw [hundo]
      refine ⟨⟨Or.inl ⟨?_, hnewC, hnewSimple⟩, ?_⟩, ?_⟩
      · simpa only [hnewLength] using hnewPerm
      · rw [hnewIndex]; omega
      · simp only [V, if_neg hnewNotP, if_neg hnewNotE, if_pos hnewSecond]; exact hrecover
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro permutation hsource; exact (hforward permutation hsource).1
    · intro first hfirst second hsecond heq; have hh := congrArg undoV heq
      simpa only [(hforward first hfirst).2, (hforward second hsecond).2] using hh
    · intro permutation htarget; exact ⟨undoV permutation, (hbackward permutation htarget).1,
        (hbackward permutation htarget).2⟩
    · intro permutation hsource; exact (hforward permutation hsource).2
    · intro permutation htarget; exact (hbackward permutation htarget).2
  have hPhi : ∀ size : ℕ, 4 ≤ size → Set.BijOn (Phi size)
      {member : List ℕ | member ∈ simples size ∧ member.getD 1 0 = 1}
      {member : List ℕ | member ∈ simples size ∧ member.getD 2 0 = 1} := by
    intro size hsize; exact (PopStackThirdEquivalence.third_minimum_bijection size hsize).1
  let valid := fun member : List ℕ =>
    ∀ start ∈ List.range member.length, ∀ count ∈ List.range (member.length + 1),
      ∀ lower ∈ List.range (member.length + 1), 2 ≤ count → count < member.length →
        start + count ≤ member.length →
        ¬ ((member.drop start).take count).Perm (List.range' lower count)
  let small := fun size : ℕ => ((List.range' 1 size).permutations'.toFinset).filter
    (fun member => valid member ∧ member ≠ [2, 3, 4, 1])
  classical
  have hvalid : ∀ member : List ℕ,
      member.Perm (List.range' 1 member.length) → (IsSimple member ↔ valid member) := by
    intro member hp
    constructor
    · intro hs start _ count _ lower _ hc ht hb; exact hs start count lower hc ht hb
    · intro hv start count lower hc ht hb hi; have hbottom : lower ∈ member := by
        exact List.mem_of_mem_drop (List.mem_of_mem_take
          (hi.mem_iff.mpr (List.mem_range'_1.mpr ⟨le_rfl, by omega⟩)))
      have hl := (List.mem_range'_1.mp (hp.mem_iff.mp hbottom)).2
      exact hv start (List.mem_range.mpr (by omega)) count
        (List.mem_range.mpr (by omega)) lower (List.mem_range.mpr (by omega)) hc ht hb hi
  have hsmallC : ∀ size : ℕ, size ≤ 4 → ∀ member : List ℕ,
      member.Perm (List.range' 1 size) → (InC member ↔ member ≠ [2, 3, 4, 1]) := by
    intro size hsize member hp; have hl : member.length = size := by simpa using hp.length_eq
    constructor
    · intro hC heq
      apply hC [2, 3, 4, 1] (by simp [basis])
      subst member
      refine ⟨id, ?_, ?_, by simp, by simp⟩
      · intro rank hr ht; exact Nat.lt_succ_self rank
      · intro rank hr ht; simp only [List.length_cons, List.length_nil] at ht
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by omega
        rcases hh with rfl | rfl | rfl | rfl <;> simp
    · intro hne pattern hb ho
      obtain ⟨values, hinc, hmem, hsub, _⟩ := ho; have hbound : pattern.length ≤ size := by
        simpa only [List.length_map, hl] using hsub.length_le
      have hpattern : pattern = [2, 3, 4, 1] := by
        simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | rfl | simp only [List.length_cons, List.length_nil] at hbound; omega
      subst pattern
      have hb1 := List.mem_range'_1.mp (hp.mem_iff.mp (hmem 1 (by omega) (by simp)))
      have hb4 := List.mem_range'_1.mp (hp.mem_iff.mp (hmem 4 (by omega) (by simp)))
      have hi1 := hinc 1 (by omega) (by simp); have hi2 := hinc 2 (by omega) (by simp)
      have hi3 := hinc 3 (by omega) (by simp); simp only [Nat.reduceAdd] at hi1 hi2 hi3
      have hvalues : values 1 = 1 ∧ values 2 = 2 ∧ values 3 = 3 ∧ values 4 = 4 := by omega
      have hsub' : [2, 3, 4, 1].Sublist member := by
        simpa only [List.map_cons, List.map_nil, hvalues.1, hvalues.2.1,
          hvalues.2.2.1, hvalues.2.2.2] using hsub
      exact hne (hsub'.eq_of_length (by simp only [List.length_cons, List.length_nil]; omega)).symm
  have hsmall : ∀ size : ℕ, size ≤ 4 → simples size = (small size : Set (List ℕ)) := by
    intro size hsize
    ext member
    simp only [simples, Set.mem_ofPred_eq, Finset.mem_coe, small, Finset.mem_filter,
      List.mem_toFinset, List.mem_permutations']
    constructor
    · rintro ⟨hp, hC, hs⟩
      have hl : member.length = size := by simpa using hp.length_eq
      exact ⟨hp, (hvalid member (by simpa [hl] using hp)).mp hs,
        (hsmallC size hsize member hp).mp hC⟩
    · rintro ⟨hp, hv, hne⟩
      have hl : member.length = size := by simpa using hp.length_eq
      exact ⟨hp, (hsmallC size hsize member hp).mpr hne,
        (hvalid member (by simpa [hl] using hp)).mpr hv⟩
  have hzero : (simples 0).ncard = 1 := by
    rw [hsmall 0 (by omega), Set.ncard_coe_finset]; dsimp [small, valid]
    decide
  have hone : (simples 1).ncard = 1 := by
    rw [hsmall 1 (by omega), Set.ncard_coe_finset]; dsimp [small, valid]
    decide
  have htwo : (simples 2).ncard = 2 := by
    rw [hsmall 2 (by omega), Set.ncard_coe_finset]; dsimp [small, valid]
    decide
  have hthree : simples 3 = ∅ := by
    rw [hsmall 3 (by omega)]; have hh : small 3 = ∅ := by dsimp [small, valid]; decide
    rw [hh]; simp
  have hfour : simples 4 = {[2, 4, 1, 3], [3, 1, 4, 2]} := by
    rw [hsmall 4 (by omega)]
    have hh : small 4 = {[2, 4, 1, 3], [3, 1, 4, 2]} := by dsimp [small, valid]; decide
    rw [hh]; simp
  have hfinite : ∀ size : ℕ, (simples size).Finite := by
    intro size
    apply (List.finite_toSet (List.range' 1 size).permutations).subset
    intro member hm; exact List.mem_permutations.mpr hm.1
  have haugFinite : ∀ size : ℕ, (augmented size).Finite := by
    intro size
    unfold augmented
    apply (hfinite size).union
    split_ifs <;> simp
  have hposition : ∀ size : ℕ, 4 ≤ size → ∀ member ∈ augmented size,
      1 ≤ member.idxOf 1 ∧
      (member.getD 1 0 = 1 ↔ member.idxOf 1 = 1) ∧
      (member.getD 2 0 = 1 ↔ member.idxOf 1 = 2) ∧
      (member.idxOf 1 = 1 ∨ member.idxOf 1 = 2 → member ∈ simples size) := by
    intro size hsize member hm
    have hsimpleCase : member ∈ simples size →
        1 ≤ member.idxOf 1 ∧
        (member.getD 1 0 = 1 ↔ member.idxOf 1 = 1) ∧
        (member.getD 2 0 = 1 ↔ member.idxOf 1 = 2) := by
      rintro ⟨hp, _, hs⟩
      have hl : member.length = size := by simpa using hp.length_eq
      have hnd := hp.nodup_iff.mpr (List.nodup_range' _)
      have hmin : 1 ∈ member := hp.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
      have hi := List.idxOf_lt_length_of_mem hmin
      have hget : member.getD (member.idxOf 1) 0 = 1 := by
        rw [List.getD_eq_getElem _ _ hi, List.getElem_idxOf]
      have hfirst : member.getD 0 0 ≠ 1 := by
        intro hh
        cases member with
        | nil => simp at hl; omega
        | cons first tail =>
          have hf : first = 1 := by simpa using hh
          subst first
          have ht : tail.Perm (List.range' 2 tail.length) := by
            rw [← hl, List.length_cons, List.range'_succ] at hp; exact hp.cons_inv
          exact hs 1 tail.length 2 (by simp only [List.length_cons] at hl; omega)
            (by simp) (by simp; omega) (by simpa using ht)
      have hread : ∀ index, index < size →
          (member.getD index 0 = 1 ↔ member.idxOf 1 = index) := by
        intro index hb
        constructor
        · intro heq; have hh := hnd.idxOf_getElem index (show index < member.length by omega)
          rw [← List.getD_eq_getElem member 0 (by omega), heq] at hh; exact hh
        · intro heq; simpa only [heq] using hget
      exact ⟨by by_contra hh; have heq : member.idxOf 1 = 0 := by omega
                exact hfirst (heq ▸ hget), hread 1 (by omega), hread 2 (by omega)⟩
    rcases hm with hs | he
    · exact ⟨(hsimpleCase hs).1, (hsimpleCase hs).2.1, (hsimpleCase hs).2.2,
        fun _ => hs⟩
    · have hodd : size % 2 = 1 ∧ 3 ≤ size := by
        by_contra hh
        simp only [if_neg hh, Set.mem_empty_iff_false] at he
      have heq : member = E (size / 2) := by
        simpa only [if_pos hodd, Set.mem_singleton_iff] using he
      subst member
      have hhalf : 2 ≤ size / 2 := by omega
      have hlen : (P (size / 2)).length = 2 * (size / 2) := List.length_ofFn
      have hmissing : 1 ∉ (P (size / 2)).map Nat.succ := by
        intro hh; obtain ⟨old, ho, he⟩ := List.mem_map.mp hh
        have hp := (parallel_simple (size / 2) (by omega)).1
        have hb := (List.mem_range'_1.mp (hp.mem_iff.mp ho)).1; omega
      have hi : (E (size / 2)).idxOf 1 = size - 1 := by
        simp [E, List.idxOf_append, hmissing, hlen]; omega
      have hg1 : (E (size / 2)).getD 1 0 ≠ 1 := by
        intro hh
        apply hmissing
        have hb : 1 < ((P (size / 2)).map Nat.succ).length := by simp [hlen]; omega
        have he : ((P (size / 2)).map Nat.succ)[1] = 1 := by
          unfold E at hh
          rw [List.getD_eq_getElem _ 0 (by simp [hlen]; omega),
            List.getElem_append_left hb] at hh
          exact hh
        exact he ▸ List.getElem_mem hb
      have hg2 : (E (size / 2)).getD 2 0 ≠ 1 := by
        intro hh
        apply hmissing
        have hb : 2 < ((P (size / 2)).map Nat.succ).length := by simp [hlen]; omega
        have he : ((P (size / 2)).map Nat.succ)[2] = 1 := by
          unfold E at hh
          rw [List.getD_eq_getElem _ 0 (by simp [hlen]; omega),
            List.getElem_append_left hb] at hh
          exact hh
        exact he ▸ List.getElem_mem hb
      exact ⟨by rw [hi]; omega,
        ⟨fun hh => (hg1 hh).elim, fun hh => by rw [hi] at hh; omega⟩,
        ⟨fun hh => (hg2 hh).elim, fun hh => by rw [hi] at hh; omega⟩,
        by intro hh; rw [hi] at hh; omega⟩
  let second := fun size : ℕ =>
    {member : List ℕ | member ∈ simples size ∧ member.getD 1 0 = 1}
  let third := fun size : ℕ =>
    {member : List ℕ | member ∈ simples size ∧ member.getD 2 0 = 1}
  let rest := fun size : ℕ =>
    {member : List ℕ | member ∈ augmented size ∧ 3 ≤ member.idxOf 1}
  let remaining := fun size : ℕ =>
    {member : List ℕ | member ∈ augmented size ∧ member.idxOf 1 ≠ 1}
  have hsecond : ∀ size, 4 ≤ size → second size =
      {member : List ℕ | member ∈ augmented size ∧ member.idxOf 1 = 1} := by
    intro size hsize
    ext member
    constructor
    · rintro ⟨hs, hg⟩
      have ha : member ∈ augmented size := Or.inl hs
      exact ⟨ha, ((hposition size hsize member ha).2.1.mp hg)⟩
    · rintro ⟨ha, hi⟩
      exact ⟨(hposition size hsize member ha).2.2.2 (Or.inl hi),
        (hposition size hsize member ha).2.1.mpr hi⟩
  have hthird : ∀ size, 4 ≤ size → third size =
      {member : List ℕ | member ∈ augmented size ∧ member.idxOf 1 = 2} := by
    intro size hsize
    ext member
    constructor
    · rintro ⟨hs, hg⟩
      have ha : member ∈ augmented size := Or.inl hs
      exact ⟨ha, (hposition size hsize member ha).2.2.1.mp hg⟩
    · rintro ⟨ha, hi⟩
      exact ⟨(hposition size hsize member ha).2.2.2 (Or.inr hi),
        (hposition size hsize member ha).2.2.1.mpr hi⟩
  have hcount : ∀ size, 5 ≤ size →
      (augmented size).ncard + (augmented (size - 2)).ncard =
        3 * (augmented (size - 1)).ncard := by
    intro size hsize; have hM := (minimum_two_bijection size (by omega)).1.ncard_eq
    have hN := (hPhi size (by omega)).ncard_eq
    change (augmented (size - 1)).ncard = (second size).ncard at hM
    change (second size).ncard = (third size).ncard at hN
    have hPrevious := (minimum_two_bijection (size - 1) (by omega)).1.ncard_eq
    change (augmented ((size - 1) - 1)).ncard = (second (size - 1)).ncard at hPrevious
    rw [show size - 1 - 1 = size - 2 by omega] at hPrevious
    have hV := (hcontinuation (size - 1) (by omega)).1.ncard_eq
    change (remaining (size - 1)).ncard = (rest ((size - 1) + 1)).ncard at hV
    rw [show size - 1 + 1 = size by omega] at hV
    have hpartition : augmented size = (second size ∪ third size) ∪ rest size := by
      rw [hsecond size (by omega), hthird size (by omega)]
      ext member
      simp only [Set.mem_union, Set.mem_ofPred_eq, rest]
      constructor
      · intro ha; have hi := (hposition size (by omega) member ha).1
        by_cases h1 : member.idxOf 1 = 1
        · exact Or.inl (Or.inl ⟨ha, h1⟩)
        by_cases h2 : member.idxOf 1 = 2
        · exact Or.inl (Or.inr ⟨ha, h2⟩)
        exact Or.inr ⟨ha, by omega⟩
      · rintro ((⟨ha, _⟩ | ⟨ha, _⟩) | ⟨ha, _⟩) <;> exact ha
    have hdisjoint : Disjoint (second size) (third size) := by
      rw [hsecond size (by omega), hthird size (by omega), Set.disjoint_left]
      rintro member ⟨_, h1⟩ ⟨_, h2⟩
      omega
    have hdisjointRest : Disjoint (second size ∪ third size) (rest size) := by
      rw [hsecond size (by omega), hthird size (by omega), Set.disjoint_left]
      rintro member (⟨_, h1⟩ | ⟨_, h2⟩) ⟨_, hr⟩ <;> omega
    have hMfinite : (second size).Finite := (hfinite size).subset (fun _ h => h.1)
    have hNfinite : (third size).Finite := (hfinite size).subset (fun _ h => h.1)
    have hRfinite : (rest size).Finite := (haugFinite size).subset (fun _ h => h.1)
    have hsum : (augmented size).ncard =
        (second size).ncard + (third size).ncard + (rest size).ncard := by
      rw [hpartition, Set.ncard_union_eq hdisjointRest (hMfinite.union hNfinite) hRfinite,
        Set.ncard_union_eq hdisjoint hMfinite hNfinite]
    have hremaining : remaining (size - 1) ∪ second (size - 1) = augmented (size - 1) := by
      rw [hsecond (size - 1) (by omega)]
      ext member
      simp only [Set.mem_union, Set.mem_ofPred_eq, remaining]
      by_cases hh : member.idxOf 1 = 1 <;> simp [hh]
    have hdisjointPrevious : Disjoint (remaining (size - 1)) (second (size - 1)) := by
      rw [hsecond (size - 1) (by omega), Set.disjoint_left]
      rintro member ⟨_, hne⟩ ⟨_, heq⟩
      exact hne heq
    have hcomplement : (augmented (size - 1)).ncard =
        (remaining (size - 1)).ncard + (second (size - 1)).ncard := by
      rw [← hremaining]; exact Set.ncard_union_eq hdisjointPrevious
        ((haugFinite (size - 1)).subset (fun _ h => h.1))
        ((hfinite (size - 1)).subset (fun _ h => h.1))
    omega
  have hb3 : (augmented 3).ncard = 1 := by simp [augmented, hthree]
  have hb4 : (augmented 4).ncard = 2 := by simp [augmented, hfour]
  have hfib : ∀ size : ℕ, 3 ≤ size → (augmented size).ncard = Nat.fib (2 * size - 5) := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
      intro hsize
      by_cases h3 : size = 3
      · subst size; exact hb3
      by_cases h4 : size = 4
      · subst size; exact hb4
      have hlarge : 5 ≤ size := by omega
      have hrec := hcount size hlarge; rw [ih (size - 1) (by omega) (by omega),
        ih (size - 2) (by omega) (by omega)] at hrec
      let index := 2 * size - 9
      have h1 := Nat.fib_add_two (n := index); have h2 := Nat.fib_add_two (n := index + 1)
      have h3 := Nat.fib_add_two (n := index + 2)
      rw [show index + 1 + 1 = index + 2 by omega] at h2
      rw [show index + 2 + 1 = index + 3 by omega] at h3
      have he1 : index = 2 * (size - 2) - 5 := by dsimp [index]; omega
      have he2 : index + 2 = 2 * (size - 1) - 5 := by dsimp [index]; omega
      have he3 : index + 4 = 2 * size - 5 := by dsimp [index]; omega
      rw [show index + 1 + 2 = index + 3 by omega] at h2
      rw [show index + 2 + 2 = index + 4 by omega] at h3
      have heq : Nat.fib (2 * size - 5) + Nat.fib (2 * (size - 2) - 5) =
          3 * Nat.fib (2 * (size - 1) - 5) := by
        rw [← he1, ← he2, ← he3]; omega
      omega
  refine ⟨hzero, hone, htwo, ?_⟩
  intro size hsize; have hf := hfib size hsize
  by_cases hodd : size % 2 = 1
  · have he := odd_extra (size / 2) (by omega)
    have hnot : E (size / 2) ∉ simples size := fun hh => he.2.2.1 hh.2.2
    have hadd : (augmented size).ncard = (simples size).ncard + 1 := by
      rw [augmented, if_pos ⟨hodd, hsize⟩, Set.union_comm, ← Set.insert_eq,
        Set.ncard_insert_of_notMem hnot (hfinite size)]
    rw [hodd]; omega
  · have heven : size % 2 = 0 := by omega
    simpa only [augmented, heven, Nat.zero_ne_one, false_and, if_false,
      Set.union_empty, Nat.sub_zero] using hf
end D5.S3.Combinatorics.PopStack.PopStackSimple
