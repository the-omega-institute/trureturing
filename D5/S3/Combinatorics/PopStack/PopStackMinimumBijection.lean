/- GID: D5/S3/Combinatorics/PopStack/PopStackMinimumBijection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackMinimumBijection
   mirror-E: none(waiver:recursive-minimum-two-bijection)
   anchors: []
   utility: none
   digest: Recursive minimum insertion matches augmented parents with minimum-second simples. -/

import D5.S3.Combinatorics.PopStack.PopStackM3Disjoint
import D5.S3.Combinatorics.PopStack.PopStackVerticalContinuation
import D5.S3.Combinatorics.PopStack.PopStackDecreasing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackMinimumBijection

open PopStackDefs PopStackInflation PopStackFamilies PopStackParallel PopStackExtra
open PopStackDecomposition PopStackM3Disjoint PopStackVerticalContinuation
open PopStackPrime

noncomputable section

open Classical in
mutual
  def T : ℕ → List ℕ → List ℕ
    | 0, _ => []
    | size + 1, permutation =>
      if IsSimple permutation then
        if permutation.getD 1 0 = 1 then
          let parent := undoT size permutation
          if IsSimple parent then (inflate parent 0 [2, 1]).map Nat.succ |>.insertIdx 1 1
          else (B size).map Nat.succ |>.insertIdx 1 1
        else permutation.map Nat.succ |>.insertIdx 1 1
      else (B size).map Nat.succ |>.insertIdx 1 1

  def undoT : ℕ → List ℕ → List ℕ
    | 0, _ => []
    | size + 1, permutation =>
      let predecessor := (permutation.eraseIdx 1).map Nat.pred
      if IsSimple predecessor then predecessor
      else if predecessor = B size then
        if (size + 1) % 2 = 0 then E (size / 2)
        else T size (E ((size - 1) / 2))
      else T size (deflateFirst predecessor)
end

theorem minimum_two_bijection (size : ℕ) (hsize : 4 ≤ size) :
    let source := augmented (size - 1)
    let target := {permutation : List ℕ | permutation ∈ simples size ∧
      permutation.getD 1 0 = 1}
    Set.BijOn (T size) source target ∧
      (∀ permutation ∈ source, undoT size (T size permutation) = permutation) ∧
      (∀ permutation ∈ target, T size (undoT size permutation) = permutation) := by
  classical
  have hbranches (permutation : List ℕ) (hlength : 4 ≤ permutation.length)
      (hperm : permutation.Perm (List.range' 1 permutation.length)) :
      (IsSimple permutation ∧ permutation.getD 1 0 ≠ 1 →
          ¬ ∃ skeleton : List ℕ, skeleton.Perm (List.range' 1 skeleton.length) ∧
            IsSimple skeleton ∧ InC skeleton ∧ 4 ≤ skeleton.length ∧
            skeleton.length + 1 = permutation.length ∧
            permutation = inflate skeleton 0 [2, 1]) ∧
      (IsSimple permutation ∧ permutation.getD 1 0 ≠ 1 →
          permutation ≠ B permutation.length) ∧
      ((∃ skeleton : List ℕ, skeleton.Perm (List.range' 1 skeleton.length) ∧
          IsSimple skeleton ∧ InC skeleton ∧ 4 ≤ skeleton.length ∧
          skeleton.length + 1 = permutation.length ∧
          permutation = inflate skeleton 0 [2, 1]) →
        permutation ≠ B permutation.length) ∧
      (∀ skeleton : List ℕ, 1 ≤ skeleton.length →
        deflateFirst (inflate skeleton 0 [2, 1]) = skeleton) ∧
      (∀ member : List ℕ, 2 ≤ member.length →
        member.getD 0 0 = member.getD 1 0 + 1 →
        (∀ value ∈ member.drop 2, value ≠ member.getD 1 0 + 1) →
        inflate (deflateFirst member) 0 [2, 1] = member) := by
    classical
    have hfirstRecovery :
      (∀ skeleton : List ℕ, 1 ≤ skeleton.length →
        deflateFirst (inflate skeleton 0 [2, 1]) = skeleton) ∧
      (∀ permutation : List ℕ, 2 ≤ permutation.length →
        permutation.getD 0 0 = permutation.getD 1 0 + 1 →
        (∀ value ∈ permutation.drop 2, value ≠ permutation.getD 1 0 + 1) →
        inflate (deflateFirst permutation) 0 [2, 1] = permutation) := by
      constructor
      · intro skeleton hlength
        cases skeleton with
        | nil => simp at hlength
        | cons pivot tail =>
          let shift := fun value => if pivot < value then value + 1 else value
          let contract := fun value => if pivot < value then value - 1 else value
          have hshape : inflate (pivot :: tail) 0 [2, 1] =
              (pivot + 1) :: pivot :: tail.map shift := by
            simp [inflate, shift]
          rw [hshape]
          change pivot :: (tail.map shift).map contract = pivot :: tail
          rw [List.map_map]
          congr 1
          calc
            tail.map (contract ∘ shift) = tail.map id := by
              apply List.map_congr_left
              intro value _
              dsimp [contract, shift]
              split_ifs <;> omega
            _ = tail := List.map_id _
      · intro permutation hlength hhead hmissing
        cases permutation with
        | nil => simp at hlength
        | cons first rest =>
          cases rest with
          | nil => simp at hlength
          | cons pivot tail =>
            have hfirst : first = pivot + 1 := by simpa using hhead
            subst first
            let shift := fun value => if pivot < value then value + 1 else value
            let contract := fun value => if pivot < value then value - 1 else value
            have hcontract : deflateFirst ((pivot + 1) :: pivot :: tail) =
                pivot :: tail.map contract := by
              simp [deflateFirst, contract]
            rw [hcontract]
            have hshape : inflate (pivot :: tail.map contract) 0 [2, 1] =
                (pivot + 1) :: pivot :: (tail.map contract).map shift := by
              simp [inflate, shift]
            rw [hshape, List.map_map]
            congr 2
            calc
              tail.map (shift ∘ contract) = tail.map id := by
                apply List.map_congr_left
                intro value hvalue
                have hnot : value ≠ pivot + 1 := by simpa using hmissing value (by simpa)
                dsimp [shift, contract]
                split_ifs <;> omega
              _ = tail := List.map_id _
    have hlastNotMinimum : ∀ list : List ℕ, 3 ≤ list.length →
        list.Perm (List.range' 1 list.length) → IsSimple list →
        list.getD (list.length - 1) 0 ≠ 1 := by
      intro list hlist hlistPerm hsimple hlast
      have hlastSlice : list.drop (list.length - 1) =
          [list.getD (list.length - 1) 0] := by
        apply List.ext_getElem
        · simp only [List.length_drop, List.length_cons, List.length_nil]
          omega
        · intro index hleft hright
          have hzero : index = 0 := by
            simp only [List.length_cons, List.length_nil] at hright
            omega
          subst index
          simp only [List.getElem_drop, Nat.add_zero]
          change list[list.length - 1] = list.getD (list.length - 1) 0
          exact (List.getD_eq_getElem list 0 (by omega)).symm
      have hdecompose : list = list.take (list.length - 1) ++ [1] := by
        calc
          list = list.take (list.length - 1) ++ list.drop (list.length - 1) :=
            (List.take_append_drop (list.length - 1) list).symm
          _ = _ := by rw [hlastSlice, hlast]
      have hrange : List.range' 1 list.length =
          1 :: List.range' 2 (list.length - 1) := by
        have hsize : list.length = (list.length - 1) + 1 := by omega
        conv_lhs => rw [hsize, List.range'_succ]
      have hprefix : (list.take (list.length - 1)).Perm
          (List.range' 2 (list.length - 1)) := by
        have hpermutation := hlistPerm
        conv_lhs at hpermutation => rw [hdecompose]
        rw [hrange] at hpermutation
        have hpermutation' :=
          (List.perm_append_singleton 1 (list.take (list.length - 1))).symm.trans
            hpermutation
        exact hpermutation'.cons_inv
      have hbound : 2 ≤ list.length - 1 := by omega
      have hproper : list.length - 1 < list.length := by omega
      have htake : 0 + (list.length - 1) ≤ list.length := by omega
      have := hsimple 0 (list.length - 1) 2 hbound hproper htake
        (by simpa using hprefix)
      exact this
    have hinflateLength : ∀ skeleton : List ℕ,
        skeleton.length + 1 = permutation.length →
        (inflate skeleton 0 [2, 1]).length = permutation.length := by
      intro skeleton hsize
      simp only [inflate, List.length_append, List.length_take, List.length_map,
        List.length_drop, List.length_cons, List.length_nil]
      omega
    refine ⟨?_, ?_, ?_, hfirstRecovery⟩
    · rintro ⟨hsimple, _⟩ ⟨skeleton, hskeletonPerm, hskeletonSimple, _, hskeletonLarge,
        hskeletonLength, rfl⟩
      have hblockSlice : ([2, 1].drop 0).take 2 = [2, 1] := by simp
      have hblock := (inflation_intervals skeleton [2, 1] 0 hskeletonPerm hskeletonSimple
        hskeletonLarge (by omega)
          (by simpa only [List.length_cons, List.length_nil, List.range'_succ,
            List.range'_zero, List.append_nil] using (List.Perm.swap 1 2 []))
          (by simp)).2 0 2 1 (by simp) (by simp)
        (by rw [hblockSlice]; exact List.Perm.swap 1 2 [])
      have hbad := hsimple 0 2 (skeleton.getD 0 0) (by simp) (by
        rw [hinflateLength skeleton hskeletonLength]
        omega) (by omega) hblock
      exact hbad
    · rintro ⟨hsimple, _⟩ heq
      have hB := (prefix_families (permutation.length - 1) (by omega)).2.2
        (A (permutation.length - 1)) |>.mpr (Or.inl rfl) |>.1
      have hBshape : B permutation.length =
          (A (permutation.length - 1)).map Nat.succ ++ [1] := by
        simp [B, show permutation.length ≠ 2 by omega]
      have hprefix : ((B permutation.length).take (permutation.length - 1)).Perm
          (List.range' 2 (permutation.length - 1)) := by
        have hAlength : (A (permutation.length - 1)).length = permutation.length - 1 := by
          simpa only [List.length_range'] using hB.length_eq
        rw [hBshape, List.take_append_of_le_length (by
          simp only [List.length_map, hAlength]
          omega)]
        rw [List.take_of_length_le (by
          simp only [List.length_map, hAlength]
          omega)]
        have hshift : ((A (permutation.length - 1)).map Nat.succ).Perm
            (List.range' 2 (permutation.length - 1)) := by
          have hrange : (List.range' 1 (permutation.length - 1)).map Nat.succ =
              List.range' 2 (permutation.length - 1) := by
            simpa only [Nat.succ_eq_add_one] using
              (List.range'_succ_left (s := 1) (n := permutation.length - 1)).symm
          simpa only [hrange] using hB.map Nat.succ
        simpa using hshift
      rw [← heq] at hprefix
      exact hsimple 0 (permutation.length - 1) 2 (by omega) (by omega) (by omega) hprefix
    · rintro ⟨skeleton, hskeletonPerm, hskeletonSimple, _, hskeletonLarge,
        hskeletonLength, hshape⟩ heq
      have hlastSkeleton := hlastNotMinimum skeleton (by omega) hskeletonPerm hskeletonSimple
      have hinflateLast : (inflate skeleton 0 [2, 1]).getD
          ((inflate skeleton 0 [2, 1]).length - 1) 0 ≠ 1 := by
        let pivot := skeleton.getD 0 0
        let shift := fun value => if pivot < value then value + 1 else value
        have htailLength : (skeleton.drop 1).length = skeleton.length - 1 := by
          simp only [List.length_drop]
        have htailPositive : 1 ≤ (skeleton.drop 1).length := by
          rw [htailLength]
          omega
        change (([2, 1].map (fun value => pivot + value - 1) ++
          (skeleton.drop 1).map shift).getD
            (([2, 1].map (fun value => pivot + value - 1) ++
              (skeleton.drop 1).map shift).length - 1) 0 ≠ 1)
        rw [List.getD_append_right _ _ _ _ (by simp; omega)]
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]
        have hidx :
            ([2, 1].map (fun value => pivot + value - 1) ++
              (skeleton.drop 1).map shift).length - 1 -
                ([2, 1].map (fun value => pivot + value - 1)).length =
              (skeleton.drop 1).length - 1 := by
          simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
          omega
        simp only [hidx]
        have htailElem : (skeleton.drop 1)[(skeleton.drop 1).length - 1]'(by omega) =
            skeleton[skeleton.length - 1]'(by omega) := by
          rw [List.getElem_drop]
          congr 1
          simp only [List.length_drop]
          omega
        rw [htailElem]
        rw [List.getD_eq_getElem _ _ (by omega)] at hlastSkeleton
        have hlastPositive : 1 ≤ skeleton[skeleton.length - 1]'(by omega) := by
          exact (List.mem_range'_1.mp (hskeletonPerm.mem_iff.mp
            (List.getElem_mem (by omega)))).1
        have hlastNotOne : skeleton[skeleton.length - 1]'(by omega) ≠ 1 := by
          exact hlastSkeleton
        have hlastAtLeastTwo : 2 ≤ skeleton[skeleton.length - 1]'(by omega) := by
          omega
        dsimp [shift]
        split_ifs with hcut
        · omega
        · convert hlastNotOne using 1
      have hBLast := (prefix_families permutation.length (by omega)).2.1
      have hBlen : (B permutation.length).length = permutation.length := by
        exact (congrArg List.length heq).symm
      have hBLast' : (B permutation.length).getD
          ((B permutation.length).length - 1) 0 = 1 := by
        rw [hBlen]
        exact hBLast
      have hEq : inflate skeleton 0 [2, 1] = B permutation.length := hshape.symm.trans heq
      have hLastEq := congrArg (fun list : List ℕ => list.getD (list.length - 1) 0) hEq
      exact hinflateLast (hLastEq.trans hBLast')
  have hB : ∀ length, 3 ≤ length →
      (B length).Perm (List.range' 1 length) ∧ InC (B length) ∧
      ¬ IsSimple (B length) := by
    intro length hlength
    have hf := (prefix_families length (by omega)).2.2 (B length)
    obtain ⟨hperm, hD, _⟩ := hf.mpr (Or.inr rfl)
    have hC := (PopStackChains.two_decreasing_chains (B length)
      (hperm.nodup_iff.mpr (List.nodup_range' _))).2 hD
    refine ⟨hperm, hC, ?_⟩
    have hAlength : (A (length - 1)).length = length - 1 := by
      have ha := (prefix_families (length - 1) (by omega)).2.2 (A (length - 1))
      exact (ha.mpr (Or.inl rfl)).1.length_eq.trans (List.length_range' ..)
    have hAp := ((prefix_families (length - 1) (by omega)).2.2
      (A (length - 1))).mpr (Or.inl rfl) |>.1
    have hprefix : ((B length).take (length - 1)).Perm
        (List.range' 2 (length - 1)) := by
      have hh := hAp.map Nat.succ
      rw [show (List.range' 1 (length - 1)).map Nat.succ =
        List.range' 2 (length - 1) from by
          simpa only [Nat.succ_eq_add_one] using (List.range'_succ_left ..).symm] at hh
      simpa [B, show length ≠ 2 by omega, List.take_append, hAlength] using hh
    intro hsimple
    exact hsimple 0 (length - 1) 2 (by omega)
      (by have hh := hperm.length_eq; simp at hh; omega)
      (by have hh := hperm.length_eq; simp at hh; omega) (by simpa using hprefix)
  have hInsert : ∀ permutation : List ℕ,
      permutation.Perm (List.range' 1 permutation.length) → 3 ≤ permutation.length →
      InC permutation →
      let member := (permutation.map Nat.succ).insertIdx 1 1
      member.Perm (List.range' 1 (permutation.length + 1)) ∧ InC member ∧
        member.getD 1 0 = 1 ∧ (member.eraseIdx 1).map Nat.pred = permutation ∧
        (IsSimple member ↔
          (IsSimple permutation ∧ permutation.getD 1 0 ≠ 1) ∨
          (∃ skeleton : List ℕ, skeleton.Perm (List.range' 1 skeleton.length) ∧
            IsSimple skeleton ∧ InC skeleton ∧ 4 ≤ skeleton.length ∧
            skeleton.length + 1 = permutation.length ∧
            permutation = inflate skeleton 0 [2, 1]) ∨ permutation = B permutation.length) := by
    intro permutation hperm hlength hC
    let member := (permutation.map Nat.succ).insertIdx 1 1
    have hmemberLength : member.length = permutation.length + 1 := by
      simp [member, List.length_insertIdx, show 1 ≤ permutation.length by omega]
    have hmemberPerm : member.Perm (List.range' 1 (permutation.length + 1)) := by
      have hp := hperm.map Nat.succ
      have hrange : (List.range' 1 permutation.length).map Nat.succ =
          List.range' 2 permutation.length := by
        simpa only [Nat.succ_eq_add_one] using (List.range'_succ_left ..).symm
      rw [hrange] at hp
      exact (List.perm_insertIdx _ _ (by simp; omega)).trans
        (by simpa only [List.range'_succ] using hp.cons 1)
    have hpositive : ∀ entry ∈ permutation, 1 ≤ entry := by
      intro entry hentry
      exact (List.mem_range'_1.mp (hperm.mem_iff.mp hentry)).1
    have hmemberC : InC member :=
      (PopStackMinimum.minimum_insertion_inC permutation hpositive 1
        (by omega) (by omega)).mpr hC
    have hsecond : member.getD 1 0 = 1 := by
      cases permutation with
      | nil => simp at hlength
      | cons first tail => simp [member]
    have hdelete : (member.eraseIdx 1).map Nat.pred = permutation := by
      simp [member, List.eraseIdx_insertIdx_self, List.map_map, Function.comp_def]
    have hdecomp := minimum_two_decomposition member (by omega)
      (by simpa only [hmemberLength] using hmemberPerm) hmemberC hsecond
    refine ⟨hmemberPerm, hmemberC, hsecond, hdelete, ?_⟩
    simpa only [hdelete] using hdecomp.2.2.2.2
  have hInflate : ∀ skeleton : List ℕ,
      skeleton.Perm (List.range' 1 skeleton.length) → 4 ≤ skeleton.length →
      InC skeleton →
      (inflate skeleton 0 [2, 1]).Perm (List.range' 1 (skeleton.length + 1)) ∧
        InC (inflate skeleton 0 [2, 1]) ∧
        (inflate skeleton 0 [2, 1]).length = skeleton.length + 1 ∧
        ¬ IsSimple (inflate skeleton 0 [2, 1]) := by
    intro skeleton hperm hlength hC
    cases skeleton with
    | nil => simp at hlength
    | cons pivot tail =>
      let shift := fun entry : ℕ => if pivot < entry then entry + 1 else entry
      have hshape : inflate (pivot :: tail) 0 [2, 1] =
          (pivot + 1) :: pivot :: tail.map shift := by simp [inflate, shift]
      have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
      have hpivot := List.mem_range'_1.mp (hperm.mem_iff.mp (show pivot ∈ pivot :: tail by
        simp))
      have hinj : Function.Injective shift := by
        intro first second heq
        dsimp [shift] at heq
        split_ifs at heq <;> omega
      have hmissing : pivot + 1 ∉ (pivot :: tail).map shift := by
        intro hh
        obtain ⟨entry, _, heq⟩ := List.mem_map.mp hh
        dsimp [shift] at heq
        split_ifs at heq <;> omega
      have hnormalized : ((pivot + 1) :: (pivot :: tail).map shift).Perm
          (List.range' 1 ((pivot :: tail).length + 1)) := by
        apply (List.perm_ext_iff_of_nodup
          (List.nodup_cons.mpr ⟨hmissing, hnodup.map hinj⟩) (List.nodup_range' _)).mpr
        intro entry
        constructor
        · intro hentry
          rcases List.mem_cons.mp hentry with rfl | hentry
          · apply List.mem_range'_1.mpr
            simp only [List.length_cons] at hpivot ⊢
            omega
          · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hentry
            have hb := List.mem_range'_1.mp (hperm.mem_iff.mp hold)
            apply List.mem_range'_1.mpr
            simp only [List.length_cons] at hb ⊢
            dsimp [shift]
            split_ifs <;> omega
        · intro hentry
          have hb := List.mem_range'_1.mp hentry
          by_cases heq : entry = pivot + 1
          · exact List.mem_cons.mpr (Or.inl heq)
          · apply List.mem_cons.mpr ∘ Or.inr
            by_cases hless : entry ≤ pivot
            · exact List.mem_map.mpr ⟨entry, hperm.mem_iff.mpr
                (List.mem_range'_1.mpr (by omega)), by simp [shift, hless]⟩
            · exact List.mem_map.mpr ⟨entry - 1, hperm.mem_iff.mpr
                (List.mem_range'_1.mpr (by omega)), by
                  dsimp [shift]; rw [if_pos (by omega)]; omega⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [hshape, List.map_cons, shift, lt_self_iff_false, ite_false]
          using hnormalized
      · simpa using PopStackDecreasing.decreasing_early_inflation [] tail pivot
          (by simp) hnodup hC
      · simp [hshape]
      · intro hsimple
        have hpair : (((inflate (pivot :: tail) 0 [2, 1]).drop 0).take 2).Perm
            (List.range' pivot 2) := by
          simp only [hshape, List.drop_zero, List.take_succ_cons, List.take_zero]
          simpa only [List.range'_succ, List.range'_zero] using List.Perm.swap pivot
            (pivot + 1) []
        simp only [List.length_cons] at hlength
        exact hsimple 0 2 pivot (by omega) (by simp [hshape]; omega)
          (by simp [hshape]) hpair
  have hNoThree : ∀ permutation : List ℕ,
      permutation.Perm (List.range' 1 3) → ¬ IsSimple permutation := by
    intro permutation hperm hsimple
    have hlength : permutation.length = 3 := by simpa using hperm.length_eq
    obtain ⟨first, second, third, hshape⟩ :
        ∃ first second third, permutation = [first, second, third] := by
      cases permutation with
      | nil => simp at hlength
      | cons first tail =>
        cases tail with
        | nil => simp at hlength
        | cons second tail =>
          cases tail with
          | nil => simp at hlength
          | cons third tail =>
            cases tail with
            | nil => exact ⟨first, second, third, rfl⟩
            | cons fourth tail => simp at hlength
    subst permutation
    have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
    have hb : ∀ entry ∈ [first, second, third], entry = 1 ∨ entry = 2 ∨ entry = 3 := by
      intro entry hentry
      simpa [List.range'_succ] using hperm.mem_iff.mp hentry
    rcases hb first (by simp) with rfl | rfl | rfl <;>
      rcases hb second (by simp) with rfl | rfl | rfl <;>
      rcases hb third (by simp) with rfl | rfl | rfl
    all_goals try simp at hnodup
    all_goals first
      | exact hsimple 0 2 1 (by decide) (by decide) (by decide) (by decide)
      | exact hsimple 0 2 2 (by decide) (by decide) (by decide) (by decide)
      | exact hsimple 1 2 1 (by decide) (by decide) (by decide) (by decide)
      | exact hsimple 1 2 2 (by decide) (by decide) (by decide) (by decide)
  have hAll : ∀ length, 4 ≤ length →
      let source := augmented (length - 1)
      let target := {permutation : List ℕ | permutation ∈ simples length ∧
        permutation.getD 1 0 = 1}
      Set.MapsTo (T length) source target ∧ Set.MapsTo (undoT length) target source ∧
        (∀ permutation ∈ source, undoT length (T length permutation) = permutation) ∧
        (∀ permutation ∈ target, T length (undoT length permutation) = permutation) := by
    intro length
    induction length using Nat.strong_induction_on with
    | h length ih =>
      intro hlength
      cases length with
      | zero => omega
      | succ previous =>
        have hprevious : 3 ≤ previous := by omega
        let source := augmented previous
        let target := {permutation : List ℕ | permutation ∈ simples (previous + 1) ∧
          permutation.getD 1 0 = 1}
        change Set.MapsTo (T (previous + 1)) source target ∧
          Set.MapsTo (undoT (previous + 1)) target source ∧
          (∀ permutation ∈ source,
            undoT (previous + 1) (T (previous + 1) permutation) = permutation) ∧
          (∀ permutation ∈ target,
            T (previous + 1) (undoT (previous + 1) permutation) = permutation)
        have hsource : ∀ permutation, permutation ∈ source ↔
            (permutation.Perm (List.range' 1 previous) ∧ InC permutation ∧
              IsSimple permutation) ∨
              (previous % 2 = 1 ∧ permutation = E (previous / 2)) := by
          intro permutation
          simp [source, augmented, simples, hprevious]
        have hconstruct : ∀ predecessor : List ℕ,
            predecessor.Perm (List.range' 1 previous) → InC predecessor →
            ((predecessor.map Nat.succ).insertIdx 1 1 ∈ target ↔
              (IsSimple predecessor ∧ predecessor.getD 1 0 ≠ 1) ∨
              (∃ skeleton : List ℕ, skeleton.Perm (List.range' 1 skeleton.length) ∧
                IsSimple skeleton ∧ InC skeleton ∧ 4 ≤ skeleton.length ∧
                skeleton.length + 1 = previous ∧
                predecessor = inflate skeleton 0 [2, 1]) ∨ predecessor = B previous) ∧
              (((predecessor.map Nat.succ).insertIdx 1 1).eraseIdx 1).map Nat.pred =
                predecessor := by
          intro predecessor hp hC
          have hlen : predecessor.length = previous := by simpa using hp.length_eq
          obtain ⟨hperm, hclass, hmin, hdel, hsimple⟩ :=
            hInsert predecessor (by simpa [hlen] using hp) (by omega) hC
          refine ⟨?_, hdel⟩
          change (_ ∧ _ ∧ _) ∧ _ ↔ _
          rw [show predecessor.length = previous from hlen] at hperm hsimple
          simp only [hperm, hclass, hmin, true_and, and_true]
          exact hsimple
        have hBconstruct := hconstruct (B previous) (hB previous hprevious).1
          (hB previous hprevious).2.1
        have hBtarget := hBconstruct.1.mpr (Or.inr (Or.inr rfl))
        have hBnot := (hB previous hprevious).2.2
        have hforward : ∀ permutation ∈ source,
            T (previous + 1) permutation ∈ target ∧
              undoT (previous + 1) (T (previous + 1) permutation) = permutation := by
          intro permutation hmember
          rcases (hsource permutation).mp hmember with hsimple | hextra
          · obtain ⟨hperm, hC, hsimple⟩ := hsimple
            have hlen : permutation.length = previous := by simpa using hperm.length_eq
            by_cases hminimum : permutation.getD 1 0 = 1
            · have hlarge : 4 ≤ previous := by
                by_contra hh
                have heq : previous = 3 := by omega
                exact hNoThree permutation (by simpa [heq] using hperm) hsimple
              obtain ⟨hprevForward, hprevBackward, hprevLeft, hprevRight⟩ :=
                ih previous (by omega) hlarge
              have hprevTarget : permutation ∈
                  {member : List ℕ | member ∈ simples previous ∧ member.getD 1 0 = 1} :=
                ⟨⟨hperm, hC, hsimple⟩, hminimum⟩
              have hparent := hprevBackward hprevTarget
              have hrecover := hprevRight permutation hprevTarget
              let parent := undoT previous permutation
              change parent ∈ augmented (previous - 1) at hparent
              change T previous parent = permutation at hrecover
              rcases hparent with hparent | hparent
              · obtain ⟨hparentPerm, hparentC, hparentSimple⟩ := hparent
                have hparentLen : parent.length = previous - 1 := by
                  simpa using hparentPerm.length_eq
                have hparentLarge : 4 ≤ parent.length := by
                  by_contra hh
                  have hthree : previous - 1 = 3 := by omega
                  exact hNoThree parent (by simpa [hthree] using hparentPerm) hparentSimple
                obtain ⟨hinfPerm, hinfC, hinfLen, hinfNot⟩ := hInflate parent
                  (by simpa [hparentLen] using hparentPerm) hparentLarge hparentC
                have hinfLen' : (inflate parent 0 [2, 1]).length = previous := by omega
                have hinfPerm' : (inflate parent 0 [2, 1]).Perm
                    (List.range' 1 previous) := by
                  simpa only [show parent.length + 1 = previous by omega] using hinfPerm
                have hctor := hconstruct (inflate parent 0 [2, 1]) hinfPerm' hinfC
                have hbranch : ∃ skeleton : List ℕ,
                    skeleton.Perm (List.range' 1 skeleton.length) ∧ IsSimple skeleton ∧
                    InC skeleton ∧ 4 ≤ skeleton.length ∧
                    skeleton.length + 1 = previous ∧
                    inflate parent 0 [2, 1] = inflate skeleton 0 [2, 1] :=
                  ⟨parent, by simpa [hparentLen] using hparentPerm, hparentSimple,
                    hparentC, hparentLarge, by omega, rfl⟩
                have hdisj := hbranches (inflate parent 0 [2, 1])
                  (by omega) (by simpa [hinfLen'] using hinfPerm')
                have hnotB := hdisj.2.2.1 (by simpa [hinfLen'] using hbranch)
                have hdeflate := hdisj.2.2.2.1 parent (by omega)
                have hT : T (previous + 1) permutation =
                    ((inflate parent 0 [2, 1]).map Nat.succ).insertIdx 1 1 := by
                  simp only [T, if_pos hsimple, if_pos hminimum, parent,
                    if_pos hparentSimple]
                refine ⟨by rw [hT]; exact hctor.1.mpr (Or.inr (Or.inl hbranch)), ?_⟩
                rw [hT]
                simpa only [undoT, hctor.2, if_neg hinfNot,
                  show inflate parent 0 [2, 1] ≠ B previous by simpa [hinfLen'] using hnotB,
                  if_false, hdeflate] using hrecover
              · have hextra : (previous - 1) % 2 = 1 ∧
                    parent = E ((previous - 1) / 2) := by
                  simpa [show 3 ≤ previous - 1 by omega] using hparent
                have hparentNot : ¬ IsSimple parent := by
                  rw [hextra.2]
                  exact (odd_extra ((previous - 1) / 2) (by omega)).2.2.1
                have hT : T (previous + 1) permutation =
                    ((B previous).map Nat.succ).insertIdx 1 1 := by
                  simp only [T, if_pos hsimple, if_pos hminimum, parent,
                    if_neg hparentNot]
                refine ⟨by rw [hT]; exact hBtarget, ?_⟩
                rw [hT]
                have hodd : (previous + 1) % 2 ≠ 0 := by omega
                simpa only [undoT, hBconstruct.2, if_neg hBnot, ite_self, if_true,
                  if_neg hodd, ← hextra.2] using hrecover
            · have hctor := hconstruct permutation hperm hC
              have hT : T (previous + 1) permutation =
                  (permutation.map Nat.succ).insertIdx 1 1 := by
                simp only [T, if_pos hsimple, if_neg hminimum]
              refine ⟨by rw [hT]; exact hctor.1.mpr (Or.inl ⟨hsimple, hminimum⟩), ?_⟩
              rw [hT]
              simp only [undoT, hctor.2, if_pos hsimple]
          · obtain ⟨hodd, rfl⟩ := hextra
            have hnot := (odd_extra (previous / 2) (by omega)).2.2.1
            have hT : T (previous + 1) (E (previous / 2)) =
                ((B previous).map Nat.succ).insertIdx 1 1 := by
              simp only [T, if_neg hnot]
            refine ⟨by rw [hT]; exact hBtarget, ?_⟩
            rw [hT]
            simp only [undoT, hBconstruct.2, if_neg hBnot, if_true,
              if_pos (show (previous + 1) % 2 = 0 by omega)]
        have hbackward : ∀ permutation ∈ target,
            undoT (previous + 1) permutation ∈ source ∧
              T (previous + 1) (undoT (previous + 1) permutation) = permutation := by
          intro permutation hmember
          obtain ⟨⟨hperm, hC, hsimple⟩, hminimum⟩ := hmember
          have hlen : permutation.length = previous + 1 := by simpa using hperm.length_eq
          obtain ⟨hprePerm, hpreC, hpreLen, hrestore, hdecomp⟩ :=
            minimum_two_decomposition permutation (by omega)
              (by simpa [hlen] using hperm) hC hminimum
          let predecessor := (permutation.eraseIdx 1).map Nat.pred
          change predecessor.Perm (List.range' 1 predecessor.length) at hprePerm
          change InC predecessor at hpreC
          change predecessor.length + 1 = permutation.length at hpreLen
          change (predecessor.map Nat.succ).insertIdx 1 1 = permutation at hrestore
          have hpreLen' : predecessor.length = previous := by omega
          rcases hdecomp.mp hsimple with hnormal | hinflation | hskew
          · obtain ⟨hpreSimple, hpreMinimum⟩ := hnormal
            change IsSimple predecessor at hpreSimple
            change predecessor.getD 1 0 ≠ 1 at hpreMinimum
            have hundo : undoT (previous + 1) permutation = predecessor := by
              simp only [undoT, predecessor, if_pos hpreSimple]
            refine ⟨?_, ?_⟩
            · rw [hundo]
              exact (hsource predecessor).mpr (Or.inl
                ⟨by simpa [hpreLen'] using hprePerm, hpreC, hpreSimple⟩)
            · rw [hundo]
              simpa only [T, if_pos hpreSimple, if_neg hpreMinimum] using hrestore
          · obtain ⟨skeleton, hsperm, hssimple, hsC, hslarge, hslen, hshape⟩ := hinflation
            change predecessor = inflate skeleton 0 [2, 1] at hshape
            change skeleton.length + 1 = predecessor.length at hslen
            have hslen' : skeleton.length = previous - 1 := by omega
            obtain ⟨_, _, _, hinfNot⟩ := hInflate skeleton hsperm hslarge hsC
            have hpreNot : ¬ IsSimple predecessor := by simpa [hshape] using hinfNot
            have hdisj := hbranches predecessor (by omega) hprePerm
            have hnotB : predecessor ≠ B previous := by
              simpa [hpreLen'] using hdisj.2.2.1
                ⟨skeleton, hsperm, hssimple, hsC, hslarge, hslen, hshape⟩
            have hdeflate : deflateFirst predecessor = skeleton := by
              rw [hshape]
              exact hdisj.2.2.2.1 skeleton (by omega)
            have hundo : undoT (previous + 1) permutation = T previous skeleton := by
              simp only [undoT, predecessor, if_neg hpreNot, if_neg hnotB, hdeflate]
            have hlarge : 4 ≤ previous := by omega
            obtain ⟨hprevForward, _, hprevLeft, _⟩ := ih previous (by omega) hlarge
            have hsMember : skeleton ∈ augmented (previous - 1) := by
              apply Set.mem_union_left
              exact ⟨by simpa [hslen'] using hsperm, hsC, hssimple⟩
            have hchild := hprevForward hsMember
            have hchildSimple := hchild.1.2.2
            have hchildMinimum := hchild.2
            have hparent := hprevLeft skeleton hsMember
            refine ⟨?_, ?_⟩
            · rw [hundo]
              exact (hsource (T previous skeleton)).mpr (Or.inl hchild.1)
            · rw [hundo]
              simpa only [T, if_pos hchildSimple, if_pos hchildMinimum, hparent,
                if_pos hssimple, ← hshape] using hrestore
          · change predecessor = B predecessor.length at hskew
            have hshape : predecessor = B previous := by simpa [hpreLen'] using hskew
            have hpreNot : ¬ IsSimple predecessor := by simpa [hshape] using hBnot
            by_cases heven : (previous + 1) % 2 = 0
            · have hundo : undoT (previous + 1) permutation = E (previous / 2) := by
                simp only [undoT, predecessor, if_neg hpreNot, if_pos hshape, if_pos heven]
              have hnot := (odd_extra (previous / 2) (by omega)).2.2.1
              refine ⟨?_, ?_⟩
              · rw [hundo]
                exact (hsource _).mpr (Or.inr ⟨by omega, rfl⟩)
              · rw [hundo]
                simpa only [T, if_neg hnot, hshape] using hrestore
            · have hlarge : 4 ≤ previous := by omega
              have hundo : undoT (previous + 1) permutation =
                  T previous (E ((previous - 1) / 2)) := by
                simp only [undoT, predecessor, if_neg hpreNot, if_pos hshape, if_neg heven]
              obtain ⟨hprevForward, _, hprevLeft, _⟩ := ih previous (by omega) hlarge
              have hsMember : E ((previous - 1) / 2) ∈ augmented (previous - 1) := by
                apply Set.mem_union_right
                simp [show (previous - 1) % 2 = 1 by omega, show 3 ≤ previous - 1 by omega]
              have hchild := hprevForward hsMember
              have hchildSimple := hchild.1.2.2
              have hchildMinimum := hchild.2
              have hparent := hprevLeft (E ((previous - 1) / 2)) hsMember
              have hnot := (odd_extra ((previous - 1) / 2) (by omega)).2.2.1
              refine ⟨?_, ?_⟩
              · rw [hundo]
                exact (hsource _).mpr (Or.inl hchild.1)
              · rw [hundo]
                simpa only [T, if_pos hchildSimple, if_pos hchildMinimum, hparent,
                  if_neg hnot, hshape] using hrestore
        exact ⟨fun _ hp => (hforward _ hp).1, fun _ hp => (hbackward _ hp).1,
          fun _ hp => (hforward _ hp).2, fun _ hp => (hbackward _ hp).2⟩
  obtain ⟨hforward, hbackward, hleft, hright⟩ := hAll size hsize
  refine ⟨⟨hforward, ?_, ?_⟩, hleft, hright⟩
  · intro first hfirst second hsecond heq
    simpa only [hleft first hfirst, hleft second hsecond] using congrArg (undoT size) heq
  · intro permutation hpermutation
    exact ⟨undoT size permutation, hbackward hpermutation, hright permutation hpermutation⟩

end

end D5.S3.Combinatorics.PopStack.PopStackMinimumBijection
