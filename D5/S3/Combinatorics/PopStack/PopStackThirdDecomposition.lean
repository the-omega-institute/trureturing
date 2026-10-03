/- GID: D5/S3/Combinatorics/PopStack/PopStackThirdDecomposition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackThirdDecomposition
   mirror-E: none(waiver:minimum-third-deletion-classification)
   anchors: [mathlib/module/Mathlib.Data.List.Sort]
   utility: none
   digest: Minimum-third deletion separates prime second inflation and two small quotients. -/
import D5.S3.Combinatorics.PopStack.PopStackCrossing
import D5.S3.Combinatorics.PopStack.PopStackPrime
import D5.S3.Combinatorics.PopStack.PopStackMinimum
import D5.S3.Combinatorics.PopStack.PopStackLeftDecomposition
import D5.S3.Combinatorics.PopStack.PopStackTerminalIntervals
import Mathlib.Data.List.Sort
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.PopStack.PopStackThirdDecomposition
open PopStackDefs PopStackInflation PopStackCrossing PopStackPrime PopStackChains
open PopStackLeftDecomposition
theorem minimum_three_decomposition (member : List ℕ) (hlength : 5 ≤ member.length)
    (hperm : member.Perm (List.range' 1 member.length)) (hminimum : member.getD 2 0 = 1) :
    (InC member ∧ IsSimple member) ↔
    let predecessor := (member.eraseIdx 2).map Nat.pred
    predecessor.Perm (List.range' 1 predecessor.length) ∧ InC predecessor ∧
      predecessor.length + 1 = member.length ∧
      (predecessor.map Nat.succ).insertIdx 2 1 = member ∧
      ((IsSimple predecessor ∧ 3 ≤ predecessor.idxOf 1) ∨
        (∃! skeleton : List ℕ, skeleton.Perm (List.range' 1 skeleton.length) ∧
          IsSimple skeleton ∧ InC skeleton ∧ 4 ≤ skeleton.length ∧
          skeleton.getD 1 0 ≠ 1 ∧ skeleton.length + 1 = predecessor.length ∧
          predecessor = inflate skeleton 1 [2, 1]) ∨
        (∃! parent : List ℕ, parent.Perm (List.range' 1 parent.length) ∧ InC parent ∧
          IsSimple parent ∧ parent.getD 1 0 = 1 ∧ parent.length + 1 = member.length ∧
          member = 2 :: parent.map (fun entry => if entry = 1 then 1 else entry + 1)) ∨
        (∃! skeleton : List ℕ, skeleton.Perm (List.range' 1 skeleton.length) ∧
          InC skeleton ∧ IsSimple skeleton ∧ skeleton.getD 1 0 = 1 ∧
          4 ≤ skeleton.length ∧ skeleton.length + 2 = member.length ∧
          member = 2 :: (inflate skeleton 1 [1, 2]).map
            (fun entry => if entry = 1 then 1 else entry + 1)) ∨
        (InD predecessor ∧ predecessor.getD (predecessor.length - 1) 0 = 1 ∧
          predecessor = PopStackTerminalGap.R predecessor.length)) := by
  have minimum_insertion_simple (permutation : List ℕ)
      (hpositive : ∀ value ∈ permutation, 1 ≤ value)
      (gap : ℕ) (hinterior : 0 < gap ∧ gap < permutation.length) :
      IsSimple ((permutation.map Nat.succ).insertIdx gap 1) ↔
        (∀ index size lower, 2 ≤ size → size < permutation.length →
          index + size ≤ permutation.length →
          ((permutation.drop index).take size).Perm (List.range' lower size) →
          index < gap ∧ gap < index + size ∧ 2 ≤ lower) ∧
        permutation.getD (gap - 1) 0 ≠ 1 ∧ permutation.getD gap 0 ≠ 1 := by
    let expanded := (permutation.map Nat.succ).insertIdx gap 1
    have hlength : expanded.length = permutation.length + 1 := by
      simp [expanded, List.length_insertIdx, hinterior.2.le]
    have hsegments : ∀ index size, index + size ≤ expanded.length →
        ((expanded.drop index).take size) =
          if index + size ≤ gap then ((permutation.drop index).take size).map Nat.succ
          else if gap < index then ((permutation.drop (index - 1)).take size).map Nat.succ
          else (((permutation.drop index).take (size - 1)).map Nat.succ).insertIdx
            (gap - index) 1 := by
      intro index size hbound; rw [hlength] at hbound
      split_ifs with hbefore hafter <;> apply List.ext_getElem? <;> intro offset
      all_goals
        simp only [List.getElem?_take, List.getElem?_drop, List.getElem?_map,
          expanded, List.getElem?_insertIdx, List.length_map, List.length_take,
          List.length_drop]
        split_ifs <;> first | rfl | (congr 2 <;> omega) | omega
    have hmapRange : ∀ lower size,
        (List.range' lower size).map Nat.succ = List.range' (lower + 1) size := by
      intro lower size; simpa only [Nat.succ_eq_add_one] using
        (List.range'_succ_left (s := lower) (n := size)).symm
    have hpredRange : ∀ lower size, 1 ≤ lower →
        (List.range' lower size).map Nat.pred = List.range' (lower - 1) size := by
      intro lower size hlower
      simpa only [← Nat.pred_eq_sub_one] using (List.map_sub_range' hlower size)
    have hpredSucc : ∀ segment : List ℕ, (segment.map Nat.succ).map Nat.pred = segment := by
      intro segment; simp [List.map_map, Function.comp_def]
    have hsegmentPositive : ∀ index size value,
        value ∈ (permutation.drop index).take size → 1 ≤ value := by
      intro index size value hmem
      exact hpositive value (List.mem_of_mem_drop (List.mem_of_mem_take hmem))
    have hget : ∀ index, permutation.getD index 0 = 1 ↔
        ((permutation.drop index).take 1) = [1] := by
      intro index; simp only [List.take_one, List.head?_eq_getElem?, List.getElem?_drop,
        List.getD_eq_getElem?_getD]
      cases permutation[index]? <;> simp
    constructor
    · intro hsimple; change IsSimple expanded at hsimple
      have hintervals : ∀ index size lower, 2 ≤ size → size < permutation.length →
          index + size ≤ permutation.length →
          ((permutation.drop index).take size).Perm (List.range' lower size) →
          index < gap ∧ gap < index + size ∧ 2 ≤ lower := by
        intro index size lower hsize hproper hbound hperm
        have hshift : (((permutation.drop index).take size).map Nat.succ).Perm
            (List.range' (lower + 1) size) := by
          simpa only [hmapRange] using hperm.map Nat.succ
        have hcross : index < gap ∧ gap < index + size := by
          by_cases hbefore : index + size ≤ gap
          · have hnew := hsimple index size (lower + 1) hsize (by omega) (by rw [hlength]; omega)
            rw [hsegments index size (by rw [hlength]; omega), if_pos hbefore] at hnew
            exact False.elim (hnew hshift)
          · by_cases hafter : gap ≤ index
            · have hnew := hsimple (index + 1) size (lower + 1) hsize (by omega)
                (by rw [hlength]; omega)
              rw [hsegments (index + 1) size (by rw [hlength]; omega),
                if_neg (by omega), if_pos (by omega)] at hnew
              simp only [Nat.add_sub_cancel_right] at hnew; exact False.elim (hnew hshift)
            · omega
        have hlower : 1 ≤ lower := by
          have hm : lower ∈ List.range' lower size := List.mem_range'_1.mpr ⟨by omega, by omega⟩
          exact hsegmentPositive index size lower (hperm.mem_iff.mpr hm)
        have hlarge : 2 ≤ lower := by
          by_contra hsmall
          have heq : lower = 1 := (by omega); subst lower; have hinsert : gap - index ≤
              (((permutation.drop index).take size).map Nat.succ).length := by
            simp only [List.length_map, List.length_take, List.length_drop]; omega
          have hnew := hsimple index (size + 1) 1 (by omega) (by rw [hlength]; omega)
            (by rw [hlength]; omega)
          rw [hsegments index (size + 1) (by rw [hlength]; omega),
            if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_right] at hnew
          apply hnew; apply (List.perm_insertIdx _ _ hinsert).trans
          simpa only [List.range'_succ] using hshift.cons 1
        exact ⟨hcross.1, hcross.2, hlarge⟩
      refine ⟨hintervals, ?_, ?_⟩
      · intro heq; have hnew := hsimple (gap - 1) 2 1 (by omega) (by rw [hlength]; omega)
          (by rw [hlength]; omega)
        rw [hsegments (gap - 1) 2 (by rw [hlength]; omega),
          if_neg (by omega), if_neg (by omega)] at hnew
        have hsingle := (hget (gap - 1)).mp heq
        simp only [show 2 - 1 = 1 by omega, hsingle, List.map_cons, List.map_nil,
          show gap - (gap - 1) = 1 by omega] at hnew
        exact hnew (by decide)
      · intro heq; have hnew := hsimple gap 2 1 (by omega) (by rw [hlength]; omega)
          (by rw [hlength]; omega)
        rw [hsegments gap 2 (by rw [hlength]; omega), if_neg (by omega), if_neg (by omega)] at hnew
        have hsingle := (hget gap).mp heq
        simp only [show 2 - 1 = 1 by omega, hsingle, List.map_cons, List.map_nil,
          Nat.sub_self] at hnew
        exact hnew (by decide)
    · rintro ⟨hintervals, hleft, hright⟩ index size lower hsize hproper hbound hperm
      change ((expanded.drop index).take size).Perm (List.range' lower size) at hperm
      change size < expanded.length at hproper; change index + size ≤ expanded.length at hbound
      have hpositiveNew : ∀ value ∈ expanded, 1 ≤ value := by
        intro value hmem; rw [List.mem_insertIdx (show gap ≤ (permutation.map Nat.succ).length by
          simpa using hinterior.2.le)] at hmem
        rcases hmem with heq | hmem
        · omega
        · obtain ⟨old, _, rfl⟩ := List.mem_map.mp hmem; omega
      have hlower : 1 ≤ lower := by
        have hm : lower ∈ List.range' lower size := List.mem_range'_1.mpr ⟨by omega, by omega⟩
        exact hpositiveNew lower
          (List.mem_of_mem_drop (List.mem_of_mem_take (hperm.mem_iff.mpr hm)))
      by_cases hbefore : index + size ≤ gap
      · rw [hsegments index size hbound, if_pos hbefore] at hperm
        have hold : ((permutation.drop index).take size).Perm (List.range' (lower - 1) size) := by
          simpa only [hpredSucc, hpredRange lower size hlower] using hperm.map Nat.pred
        have hh := hintervals index size (lower - 1) hsize (by omega) (by omega) hold; omega
      · by_cases hafter : gap < index
        · rw [hsegments index size hbound, if_neg hbefore, if_pos hafter] at hperm
          have hold : ((permutation.drop (index - 1)).take size).Perm
              (List.range' (lower - 1) size) := by
            simpa only [hpredSucc, hpredRange lower size hlower] using hperm.map Nat.pred
          have hh := hintervals (index - 1) size (lower - 1) hsize
            (by rw [hlength] at hbound; omega) (by rw [hlength] at hbound; omega) hold
          omega
        · rw [hsegments index size hbound, if_neg hbefore, if_neg hafter] at hperm
          have hinsert : gap - index ≤
              (((permutation.drop index).take (size - 1)).map Nat.succ).length := by
            simp only [List.length_map, List.length_take, List.length_drop]; rw [hlength] at hbound
            omega
          have hone : 1 ∈ List.range' lower size := hperm.mem_iff.mp
            ((List.mem_insertIdx hinsert).mpr (Or.inl rfl))
          have heq : lower = 1 := by have hh := List.mem_range'_1.mp hone; omega
          subst lower; have hshift : (((permutation.drop index).take (size - 1)).map Nat.succ).Perm
              (List.range' 2 (size - 1)) := by
            have hh := (List.perm_insertIdx _ _ hinsert).symm.trans hperm
            rw [show size = (size - 1) + 1 by omega, List.range'_succ] at hh; exact hh.cons_inv
          have hold : ((permutation.drop index).take (size - 1)).Perm
              (List.range' 1 (size - 1)) := by
            simpa only [hpredSucc, hpredRange 2 (size - 1) (by omega)] using hshift.map Nat.pred
          by_cases hlong : 3 ≤ size
          · have hh := hintervals index (size - 1) 1 (by omega)
              (by rw [hlength] at hproper; omega) (by rw [hlength] at hbound; omega) hold
            omega
          · have heq : size = 2 := by omega
            subst size; have hsingle : ((permutation.drop index).take 1) = [1] := by
              simpa only [show 2 - 1 = 1 by omega, List.range'_succ, List.range'_zero]
                using List.perm_singleton.mp hold
            have hv := (hget index).mpr hsingle
            by_cases hsame : index = gap
            · subst index; exact hright hv
            · have heq : index = gap - 1 := by omega
              subst index; exact hleft hv
  have skew_minimum_class (permutation : List ℕ) (hpositive : ∀ entry ∈ permutation, 1 ≤ entry) :
      InC (permutation.map Nat.succ ++ [1]) → InD permutation := by
    let extended := permutation.map Nat.succ ++ [1]
    have hlift : ∀ pattern : List ℕ, 1 ≤ pattern.length →
        (∀ rank ∈ pattern, 1 ≤ rank) → Occurs pattern permutation →
        Occurs (pattern.map Nat.succ ++ [1]) extended := by
      intro pattern hlength hranks hocc; obtain ⟨values, hinc, hmem, hsub, _⟩ := hocc
      let ranks := fun rank => if rank = 1 then 1 else (values (rank - 1)).succ
      have hnewLength : (pattern.map Nat.succ ++ [1]).length = pattern.length + 1 := by
        simp only [List.length_append, List.length_map, List.length_singleton]
      refine ⟨ranks, ?_, ?_, ?_, by simp⟩
      · intro rank hfirst hlast; rw [hnewLength] at hlast
        by_cases hminimum : rank = 1
        · subst rank
          have hvalue := hpositive (values 1) (hmem 1 (by omega) hlength); dsimp only [ranks]
          simp only [ite_true, Nat.reduceAdd, Nat.reduceEqDiff, ite_false, Nat.reduceSub]; omega
        · have hh := hinc (rank - 1) (by omega) (by omega)
          have heq : rank - 1 + 1 = rank := (by omega); rw [heq] at hh; dsimp only [ranks]
          rw [if_neg hminimum, if_neg (by omega)]; simp only [Nat.add_sub_cancel]; omega
      · intro rank hfirst hlast; rw [hnewLength] at hlast
        by_cases hminimum : rank = 1
        · simp only [ranks, hminimum, ite_true, extended, List.mem_append,
            List.mem_singleton, or_true]
        · have hh := hmem (rank - 1) (by omega) (by omega); dsimp only [ranks]; rw [if_neg hminimum]
          exact List.mem_append_left [1] (List.mem_map.mpr ⟨values (rank - 1), hh, rfl⟩)
      · have hselection : (pattern.map Nat.succ ++ [1]).map ranks =
            (pattern.map values).map Nat.succ ++ [1] := by
          rw [List.map_append, List.map_map, List.map_map]
          have hmap : pattern.map (ranks ∘ Nat.succ) = pattern.map (Nat.succ ∘ values) := by
            apply List.map_congr_left; intro rank hrank; have hh := hranks rank hrank
            dsimp only [Function.comp_apply, ranks]; rw [if_neg (by omega)]
            simp only [Nat.succ_sub_one]
          rw [hmap]; simp only [List.map_cons, List.map_nil, ranks, ite_true]
        rw [hselection]; exact (hsub.map Nat.succ).append (List.Sublist.refl [1])
    intro hC; have h123 : ¬ Occurs [1, 2, 3] permutation := by
      intro hocc; have hh := hlift [1, 2, 3] (by decide) (by
        intro rank hrank
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hrank; omega) hocc
      exact hC [2, 3, 4, 1] (by decide) hh
    have h3142 : ¬ Occurs [3, 1, 4, 2] permutation := by
      intro hocc; have hh := hlift [3, 1, 4, 2] (by decide) (by
        intro rank hrank
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hrank; omega) hocc
      exact hC [4, 2, 5, 3, 1] (by decide) hh
    have h3412 : ¬ Occurs [3, 4, 1, 2] permutation := by
      intro hocc; have hh := hlift [3, 4, 1, 2] (by decide) (by
        intro rank hrank
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hrank; omega) hocc
      exact hC [4, 5, 2, 3, 1] (by decide) hh
    exact ⟨h123, h3142, h3412⟩
  classical
  constructor
  swap
  · let predecessor := (member.eraseIdx 2).map Nat.pred
    rintro ⟨hprePerm, hpreC, hpreLength, hinverse, hcases⟩
    change predecessor.Perm (List.range' 1 predecessor.length) at hprePerm
    change InC predecessor at hpreC; change predecessor.length + 1 = member.length at hpreLength
    change (predecessor.map Nat.succ).insertIdx 2 1 = member at hinverse
    have hpositive : ∀ entry ∈ predecessor, 1 ≤ entry := by
      intro entry hentry; exact (List.mem_range'_1.mp (hprePerm.mem_iff.mp hentry)).1
    have hmemberC : InC member := by
      rw [← hinverse]; exact (PopStackMinimum.minimum_insertion_inC predecessor hpositive 2
        (by omega) (by omega)).mpr hpreC
    refine ⟨hmemberC, ?_⟩
    rcases hcases with hsimple | hinflation | hparent | hleftInflation | hterminal
    · obtain ⟨hsimple, hposition⟩ := hsimple; change 3 ≤ predecessor.idxOf 1 at hposition
      rw [← hinverse]; apply (minimum_insertion_simple predecessor hpositive 2
        ⟨by omega, by omega⟩).mpr
      have hnodup := hprePerm.nodup_iff.mpr (List.nodup_range' 1)
      have hneighbor : ∀ index, index = 1 ∨ index = 2 → predecessor.getD index 0 ≠ 1 := by
        intro index hi heq; have hb : index < predecessor.length := by omega
        have hg : predecessor[index]'hb = 1 := (by rw [← List.getD_eq_getElem _ _ hb]; exact heq)
        have hh := hnodup.idxOf_getElem index hb; rw [hg] at hh; omega
      refine ⟨?_, by simpa using hneighbor 1 (Or.inl rfl), hneighbor 2 (Or.inr rfl)⟩
      intro start count lower hc hp hb hi; exact False.elim (hsimple start count lower hc hp hb hi)
    · obtain ⟨skeleton, hskeletonPerm, hskeletonSimple, hskeletonC, hskeletonLength,
        hnotMinimum, hlengthEq, hshape⟩ := hinflation.exists
      change predecessor = inflate skeleton 1 [2, 1] at hshape
      have hinside := (inflation_intervals skeleton [2, 1] 1 hskeletonPerm
        hskeletonSimple hskeletonLength (by omega) (by decide) (by decide)).1
      have hsecondPositive : 2 ≤ skeleton.getD 1 0 := by
        have hindex : 1 < skeleton.length := by omega
        have hb := List.mem_range'_1.mp (hskeletonPerm.mem_iff.mp (List.getElem_mem hindex))
        rw [← List.getD_eq_getElem _ 0 hindex] at hb; omega
      cases skeleton with
      | nil => simp at hskeletonLength
      | cons first rest =>
        cases rest with
        | nil => simp at hskeletonLength
        | cons second tail =>
          have hsecond : 2 ≤ second := by simpa using hsecondPositive
          let shift := fun entry : ℕ => if second < entry then entry + 1 else entry
          have hfirstShape : predecessor =
              shift first :: (second + 1) :: second :: tail.map shift := by
            simpa [inflate, shift] using hshape
          rw [← hinverse]; apply (minimum_insertion_simple predecessor hpositive 2
            ⟨by omega, by omega⟩).mpr
          refine ⟨?_, by simp [hfirstShape]; omega, by simp [hfirstShape]; omega⟩
          intro start count lower hc hp hb hi
          have hh := hinside start count lower hc (by rw [← hshape]; exact hp)
            (by rw [← hshape]; exact hb) (by rw [← hshape]; exact hi)
          simp only [List.length_cons, List.length_nil] at hh; have hs : start = 1 := by omega
          have hcount : count = 2 := by omega
          have hpairs : ((predecessor.drop start).take count) = [second + 1, second] := by
            simp [hs, hcount, hfirstShape]
          rw [hpairs] at hi; have hlow := List.mem_range'_1.mp (hi.mem_iff.mp
            (show second ∈ [second + 1, second] by simp))
          have hhigh := List.mem_range'_1.mp (hi.mem_iff.mp
            (show second + 1 ∈ [second + 1, second] by simp))
          exact ⟨by omega, by omega, by omega⟩
    · obtain ⟨parent, hp, hC, hs, hm, hl, heq⟩ := hparent.exists; rw [heq]
      apply (prepend_two_decomposition parent hp (by omega) hm).1.mpr
      intro start count lower hc hproper hb hi
      exact False.elim (hs start count lower hc hproper hb hi)
    · obtain ⟨skeleton, hskeletonPerm, hskeletonC, hskeletonSimple, hminimum,
        hskeletonLength, hlengthEq, hshape⟩ := hleftInflation.exists
      have hinside := (inflation_intervals skeleton [1, 2] 1 hskeletonPerm
        hskeletonSimple hskeletonLength (by omega) (by decide) (by decide)).1
      cases skeleton with
      | nil => simp at hskeletonLength
      | cons first rest =>
        cases rest with
        | nil => simp at hskeletonLength
        | cons second tail =>
          have hsecond : second = 1 := by simpa using hminimum
          subst second; have hnodup := hskeletonPerm.nodup_iff.mpr (List.nodup_range' 1)
          have hfirst : 2 ≤ first := by
            have hb := List.mem_range'_1.mp (hskeletonPerm.mem_iff.mp
              (show first ∈ first :: 1 :: tail by simp))
            have hn := (List.nodup_cons.mp hnodup).1
            have hh : first ≠ 1 := by intro heq; exact hn (by simp [heq])
            omega
          have htail : ∀ entry ∈ tail, 2 ≤ entry := by
            intro entry hentry; have hb := List.mem_range'_1.mp (hskeletonPerm.mem_iff.mp
              (show entry ∈ first :: 1 :: tail by simp [hentry]))
            have hn := (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).1
            have hh : entry ≠ 1 := by intro heq; exact hn (heq ▸ hentry)
            omega
          have hmap : tail.map (fun entry => if 1 < entry then entry + 1 else entry) =
              tail.map Nat.succ := by
            apply List.map_congr_left; intro entry hentry; have hb := htail entry hentry
            simp only [if_pos (by omega : 1 < entry), Nat.succ_eq_add_one]
          have hinflate : inflate (first :: 1 :: tail) 1 [1, 2] =
              (first + 1) :: 1 :: 2 :: tail.map Nat.succ := by
            simp [inflate, if_pos (by omega : 1 < first), hmap]
          have hremove : (first :: tail).Perm (List.range' 2 (tail.length + 1)) := by
            have hh := (List.Perm.swap first 1 tail).trans hskeletonPerm
            simp only [List.length_cons] at hh
            rw [show tail.length + 1 + 1 = (tail.length + 1) + 1 by omega, List.range'_succ] at hh
            exact hh.cons_inv
          have hshift : ((first :: tail).map Nat.succ).Perm (List.range' 3 (tail.length + 1)) := by
            have hr : (List.range' 2 (tail.length + 1)).map Nat.succ =
                List.range' 3 (tail.length + 1) := by
              simpa only [Nat.succ_eq_add_one] using (List.range'_succ_left ..).symm
            simpa only [hr] using hremove.map Nat.succ
          have hqPerm : ((first + 1) :: 1 :: 2 :: tail.map Nat.succ).Perm
              (List.range' 1 (tail.length + 3)) := by
            have hh : ((first + 1) :: 1 :: 2 :: tail.map Nat.succ).Perm
                (1 :: 2 :: (first + 1) :: tail.map Nat.succ) :=
              (List.Perm.swap 1 (first + 1) _).trans ((List.Perm.swap 2 (first + 1) _).cons 1)
            apply hh.trans; simpa only [List.map_cons, Nat.succ_eq_add_one, List.range'_succ,
              show tail.length + 3 = ((tail.length + 1) + 1) + 1 by omega] using
              (hshift.cons 2).cons 1
          rw [hshape]; apply (prepend_two_decomposition (inflate (first :: 1 :: tail) 1 [1, 2])
            (by simpa only [hinflate, List.length_cons, List.length_map,
              show tail.length + 1 + 1 + 1 = tail.length + 3 by omega] using hqPerm)
            (by simp [hinflate]) (by simp [hinflate])).1.mpr
          intro start count lower hc hp hb hi; have hh := hinside start count lower hc hp hb hi
          simp only [List.length_cons, List.length_nil] at hh; have hs : start = 1 := by omega
          have hcount : count = 2 := by omega
          have hvalues : ((inflate (first :: 1 :: tail) 1 [1, 2]).drop start).take count =
              [1, 2] := by simp [hinflate, hs, hcount]
          rw [hvalues] at hi
          have hlow := List.mem_range'_1.mp (hi.mem_iff.mp (by simp : 1 ∈ [1, 2]))
          have hbottom : lower ∈ [1, 2] := hi.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hbottom
          exact ⟨hs, hcount, by omega⟩
    · obtain ⟨_, _, heq⟩ := hterminal
      change predecessor = PopStackTerminalGap.R predecessor.length at heq
      have hh := (PopStackTerminalIntervals.terminal_family_intervals predecessor.length
        (by omega)).2.2.2.2.2
      have hmember : member = PopStackTerminalIntervals.Y (predecessor.length + 1) := by
        change member = ((PopStackTerminalGap.R predecessor.length).map Nat.succ).insertIdx 2 1
        rw [← hinverse]; exact congrArg (fun list : List ℕ => (list.map Nat.succ).insertIdx 2 1) heq
      exact hmember ▸ hh.2.2
  rintro ⟨hC, hsimple⟩; let predecessor := (member.eraseIdx 2).map Nat.pred
  have hindex : 2 < member.length := by omega
  have hentry : member[2]'hindex = 1 := by
    simpa only [List.getD_eq_getElem member 0 hindex] using hminimum
  have hremoved : (member.eraseIdx 2).Perm (List.range' 2 (member.length - 1)) := by
    have hh := (List.getElem_cons_eraseIdx_perm hindex).trans hperm
    rw [hentry, show member.length = (member.length - 1) + 1 by omega, List.range'_succ] at hh
    exact hh.cons_inv
  have hremovedPositive : ∀ value ∈ member.eraseIdx 2, 2 ≤ value := by
    intro value hvalue; have hh := List.mem_range'.mp (hremoved.mem_iff.mp hvalue); omega
  have hnormalize : (List.range' 2 (member.length - 1)).map Nat.pred =
      List.range' 1 (member.length - 1) := by
    have hshift : (List.range' 1 (member.length - 1)).map Nat.succ =
        List.range' 2 (member.length - 1) := by
      simpa only [Nat.succ_eq_add_one] using (List.range'_succ_left ..).symm
    rw [← hshift, List.map_map]; exact List.map_id _
  have hprePerm : predecessor.Perm (List.range' 1 predecessor.length) := by
    simpa only [hnormalize, predecessor, List.length_map,
      List.length_eraseIdx_of_lt hindex] using hremoved.map Nat.pred
  have hpreLength : predecessor.length = member.length - 1 := by
    simp only [predecessor, List.length_map, List.length_eraseIdx_of_lt hindex]
  have hpositive : ∀ value ∈ predecessor, 1 ≤ value := by
    intro value hvalue; exact (List.mem_range'_1.mp (hprePerm.mem_iff.mp hvalue)).1
  have hmapInverse : predecessor.map Nat.succ = member.eraseIdx 2 := by
    dsimp only [predecessor]; rw [List.map_map]
    calc
      (member.eraseIdx 2).map (Nat.succ ∘ Nat.pred) = (member.eraseIdx 2).map id := by
        apply List.map_congr_left; intro value hvalue; have hh := hremovedPositive value hvalue
        dsimp
        omega
      _ = _ := List.map_id _
  have hinverse : (predecessor.map Nat.succ).insertIdx 2 1 = member := by
    rw [hmapInverse]; simpa only [hentry] using List.insertIdx_eraseIdx_getElem hindex
  have hpreC : InC predecessor := by
    apply (PopStackMinimum.minimum_insertion_inC predecessor hpositive 2 (by omega) (by omega)).mp
    rw [hinverse]; exact hC
  refine ⟨hprePerm, hpreC, ?_, hinverse, ?_⟩
  · change predecessor.length + 1 = member.length; omega
  change (IsSimple predecessor ∧ 3 ≤ predecessor.idxOf 1) ∨
    (∃! skeleton : List ℕ, skeleton.Perm (List.range' 1 skeleton.length) ∧
      IsSimple skeleton ∧ InC skeleton ∧ 4 ≤ skeleton.length ∧
      skeleton.getD 1 0 ≠ 1 ∧ skeleton.length + 1 = predecessor.length ∧
      predecessor = inflate skeleton 1 [2, 1]) ∨
    (∃! parent : List ℕ, parent.Perm (List.range' 1 parent.length) ∧ InC parent ∧
      IsSimple parent ∧ parent.getD 1 0 = 1 ∧ parent.length + 1 = member.length ∧
      member = 2 :: parent.map (fun entry => if entry = 1 then 1 else entry + 1)) ∨
    (∃! skeleton : List ℕ, skeleton.Perm (List.range' 1 skeleton.length) ∧
      InC skeleton ∧ IsSimple skeleton ∧ skeleton.getD 1 0 = 1 ∧
      4 ≤ skeleton.length ∧ skeleton.length + 2 = member.length ∧
      member = 2 :: (inflate skeleton 1 [1, 2]).map
        (fun entry => if entry = 1 then 1 else entry + 1)) ∨
    (InD predecessor ∧ predecessor.getD (predecessor.length - 1) 0 = 1 ∧
      predecessor = PopStackTerminalGap.R predecessor.length)
  have hcriterion := (minimum_insertion_simple predecessor hpositive 2
    (by omega)).mp (hinverse ▸ hsimple)
  have hcross := hcriterion.1; have hleft : member.getD 0 0 = 2 →
      (∃! parent : List ℕ, parent.Perm (List.range' 1 parent.length) ∧ InC parent ∧
        IsSimple parent ∧ parent.getD 1 0 = 1 ∧ parent.length + 1 = member.length ∧
        member = 2 :: parent.map (fun entry => if entry = 1 then 1 else entry + 1)) ∨
      (∃! skeleton : List ℕ, skeleton.Perm (List.range' 1 skeleton.length) ∧
        InC skeleton ∧ IsSimple skeleton ∧ skeleton.getD 1 0 = 1 ∧
        4 ≤ skeleton.length ∧ skeleton.length + 2 = member.length ∧
        member = 2 :: (inflate skeleton 1 [1, 2]).map
          (fun entry => if entry = 1 then 1 else entry + 1)) := by
    intro hfirst
    cases member with
    | nil => simp at hlength
    | cons first tail =>
      simp only [List.getD_cons_zero] at hfirst; subst first
      have htailLength : 4 ≤ tail.length := by simp only [List.length_cons] at hlength; omega
      have htailMinimum : tail.getD 1 0 = 1 := by simpa using hminimum
      have htailPerm : tail.Perm (1 :: List.range' 3 (tail.length - 1)) := by
        have hrange : (List.range' 1 (tail.length + 1)).Perm
            (2 :: 1 :: List.range' 3 (tail.length - 1)) := by
          rw [show tail.length + 1 = (tail.length - 1) + 2 by omega]
          rw [List.range'_succ, List.range'_succ]; exact List.Perm.swap 2 1 _
        exact (hperm.trans hrange).cons_inv
      let down := fun entry : ℕ => if entry = 1 then 1 else entry - 1
      let shift := fun entry : ℕ => if entry = 1 then 1 else entry + 1; let parent := tail.map down
      have hleftRecovery : ∀ original : List ℕ, (∀ entry ∈ original, 1 ≤ entry) →
          ((2 :: original.map shift).drop 1).map down = original := by
        intro original hpositive; simp only [List.drop_succ_cons, List.drop_zero, List.map_map]
        calc
          original.map (down ∘ shift) = original.map id := by
            apply List.map_congr_left; intro entry hentry; have hb := hpositive entry hentry
            dsimp only [down, shift, Function.comp_def, id_eq]
            split_ifs <;> omega
          _ = original := List.map_id _
      have hparentLength : parent.length = tail.length := List.length_map ..
      have hparentPerm : parent.Perm (List.range' 1 parent.length) := by
        have hh := htailPerm.map down; have hmap : (List.range' 3 (tail.length - 1)).map down =
            List.range' 2 (tail.length - 1) := by
          have hpred : (List.range' 3 (tail.length - 1)).map down =
              (List.range' 3 (tail.length - 1)).map Nat.pred := by
            apply List.map_congr_left; intro entry hentry; have hb := List.mem_range'.mp hentry
            dsimp [down]; rw [if_neg (by omega)]
          rw [hpred]; have hup : (List.range' 2 (tail.length - 1)).map Nat.succ =
              List.range' 3 (tail.length - 1) := by
            simpa only [Nat.succ_eq_add_one] using (List.range'_succ_left ..).symm
          rw [← hup, List.map_map]; exact List.map_id _
        rw [List.map_cons, hmap] at hh; have hrange : 1 :: List.range' 2 (tail.length - 1) =
            List.range' 1 parent.length := by
          rw [hparentLength, show tail.length = (tail.length - 1) + 1 by omega, List.range'_succ]
          simp
        simpa only [show down 1 = 1 by rfl, hrange] using hh
      have hparentMinimum : parent.getD 1 0 = 1 := by
        rw [List.getD_eq_getElem tail 0 (by omega)] at htailMinimum; dsimp only [parent]
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]
        simp only [htailMinimum, down, ite_true]
      have hparentInverse : 2 :: parent.map shift = 2 :: tail := by
        have hmap : parent.map shift = tail := by
          dsimp only [parent]; rw [List.map_map]
          calc
            tail.map (shift ∘ down) = tail.map id := by
              apply List.map_congr_left; intro entry hentry; have hb := htailPerm.mem_iff.mp hentry
              rcases List.mem_cons.mp hb with rfl | hb
              · rfl
              · have hb := List.mem_range'.mp hb; have hentryNe : entry ≠ 1 := by omega
                have hpredNe : entry - 1 ≠ 1 := by omega
                simp only [shift, down, Function.comp_apply, if_neg hentryNe, if_neg hpredNe, id_eq]
                omega
            _ = tail := List.map_id _
        rw [hmap]
      have hdecomp := prepend_two_decomposition parent hparentPerm (by omega) hparentMinimum
      have hcases := hdecomp.2.mp
        (show InC (2 :: parent.map shift) ∧ IsSimple (2 :: parent.map shift) from by
          rw [hparentInverse]; exact ⟨hC, hsimple⟩)
      rcases hcases with ⟨hgood, _⟩ | ⟨hblock, _⟩
      · left
        refine ⟨parent, ⟨hparentPerm, hgood.1, hgood.2, hparentMinimum,
          by simp only [List.length_cons]; omega, hparentInverse.symm⟩, ?_⟩
        intro alternative halt; obtain ⟨haltPerm, _, _, _, _, haltImage⟩ := halt
        have ha := hleftRecovery alternative (by
          intro entry hentry; exact (List.mem_range'_1.mp (haltPerm.mem_iff.mp hentry)).1)
        rw [← haltImage] at ha; exact ha.symm
      · obtain ⟨skeleton, hsperm, hsC, hssimple, hsminimum, hslarge, hslen, hsimage⟩ :=
          hblock.exists
        right
        have hslarge' : 4 ≤ skeleton.length := by rcases hslarge with htwo | hh <;> omega
        refine ⟨skeleton, ⟨hsperm, hsC, hssimple, hsminimum, hslarge', by
          simp only [List.length_cons]
          omega, by simpa only [hsimage] using hparentInverse.symm⟩, ?_⟩
        intro alternative halt
        obtain ⟨haltPerm, haltC, haltSimple, haltMinimum, haltLarge, haltLength, haltImage⟩ := halt
        have hpositive : ∀ entry ∈ inflate alternative 1 [1, 2], 1 ≤ entry := by
          intro entry hentry; simp only [inflate, List.mem_append, List.mem_map] at hentry
          rcases hentry with (⟨old, hold, rfl⟩ | ⟨old, hold, rfl⟩) | ⟨old, hold, rfl⟩
          · have hb := List.mem_range'_1.mp (haltPerm.mem_iff.mp
              ((List.take_sublist 1 alternative).subset hold))
            split_ifs <;> omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hold; rw [haltMinimum]
            rcases hold with rfl | rfl <;> omega
          · have hb := List.mem_range'_1.mp (haltPerm.mem_iff.mp
              ((List.drop_sublist 2 alternative).subset hold))
            split_ifs <;> omega
        have ha := hleftRecovery (inflate alternative 1 [1, 2]) hpositive; rw [← haltImage] at ha
        change parent = inflate alternative 1 [1, 2] at ha
        exact hblock.unique ⟨haltPerm, haltC, haltSimple, haltMinimum,
          Or.inr haltLarge, by simp only [List.length_cons] at haltLength; omega, ha⟩
          ⟨hsperm, hsC, hssimple, hsminimum, hslarge, hslen, hsimage⟩
  by_cases hpreSimple : IsSimple predecessor
  · left
    refine ⟨hpreSimple, ?_⟩
    have hfirst : predecessor.getD 0 0 ≠ 1 := by
      intro hfirst
      cases hshape : predecessor with
      | nil => rw [hshape] at hpreLength; simp at hpreLength; omega
      | cons first tail =>
        rw [hshape] at hfirst hprePerm hpreSimple hpreLength
        simp only [List.getD_cons_zero] at hfirst; subst first
        have htail : tail.Perm (List.range' 2 tail.length) := by
          simpa only [List.length_cons, List.range'_succ] using hprePerm.cons_inv
        exact hpreSimple 1 tail.length 2 (by simp at hpreLength; omega)
          (by simp) (by simp; omega) (by simpa using htail)
    have hone : 1 ∈ predecessor := hprePerm.mem_iff.mpr
      (List.mem_range'_1.mpr (by clear hleft; omega))
    have hminBound := List.idxOf_lt_length_iff.mpr hone
    have hmin : predecessor.getD (predecessor.idxOf 1) 0 = 1 := by
      rw [List.getD_eq_getElem _ _ hminBound, List.getElem_idxOf]
    by_contra hh
    have hcases : predecessor.idxOf 1 = 0 ∨ predecessor.idxOf 1 = 1 ∨
        predecessor.idxOf 1 = 2 := by omega
    rcases hcases with hzero | hone | htwo
    · exact hfirst (by simpa only [hzero] using hmin)
    · exact hcriterion.2.1 (by simpa only [hone, Nat.reduceSub] using hmin)
    · exact hcriterion.2.2 (by simpa only [htwo] using hmin)
  right
  obtain ⟨start, count, lower, skeleton, block, hcount, hproper, hbound,
    hstartGap, hgapEnd, hlower, hmaxInterval, hskeletonPerm, hblockPerm, hblockLength,
    hskeletonLength, hrestore, _, hskeletonSimple, hskeletonC, _⟩ :=
      crossing_decomposition predecessor 2 hprePerm hpreC hpreSimple (by
        intro index size bottom hsize hsizeProper hsizeBound hinterval
        have hh := hcross index size bottom hsize hsizeProper hsizeBound hinterval
        exact ⟨hh.1, hh.2.1, by omega⟩)
  have hstart : start = 0 ∨ start = 1 := by omega
  have hskeletonLower : 2 ≤ skeleton.length := by omega
  have hnotThree : skeleton.length ≠ 3 := by
    intro hthree; obtain ⟨first, second, third, hshape⟩ := List.length_eq_three.mp hthree
    have hp : [first, second, third].Perm (List.range' 1 3) := by
      simpa [hshape] using hskeletonPerm
    have hb : ∀ entry ∈ [first, second, third], entry = 1 ∨ entry = 2 ∨ entry = 3 := by
      intro entry hentry; simpa [List.range'_succ] using hp.mem_iff.mp hentry
    have hn := hp.nodup_iff.mpr (List.nodup_range' 1); rw [hshape] at hskeletonSimple
    rcases hb first (by simp) with rfl | rfl | rfl <;>
      rcases hb second (by simp) with rfl | rfl | rfl <;>
      rcases hb third (by simp) with rfl | rfl | rfl
    all_goals try simp at hn
    all_goals first
      | exact hskeletonSimple 0 2 1 (by decide) (by decide) (by decide) (by decide)
      | exact hskeletonSimple 0 2 2 (by decide) (by decide) (by decide) (by decide)
      | exact hskeletonSimple 1 2 1 (by decide) (by decide) (by decide) (by decide)
      | exact hskeletonSimple 1 2 2 (by decide) (by decide) (by decide) (by decide)
  have hblockNormalized : block.Perm (List.range' 1 block.length) := by
    simpa only [hblockLength] using hblockPerm
  have hblockNodup := hblockNormalized.nodup_iff.mpr (List.nodup_range' 1)
  have hblockBounds : ∀ entry ∈ block, 1 ≤ entry ∧ entry ≤ count := by
    intro entry hentry; have hh := List.mem_range'_1.mp (hblockPerm.mem_iff.mp hentry); omega
  by_cases hlarge : 4 ≤ skeleton.length
  · have hindex : start < skeleton.length := by omega
    have hintervals := inflation_intervals skeleton block start hskeletonPerm
      hskeletonSimple hlarge hindex hblockNormalized (by omega)
    let pivot := skeleton.getD start 0; have hpivot : 2 ≤ pivot := by
      have hh := hintervals.2 0 count 1 (by omega) (by omega)
        (by simpa only [List.drop_zero, List.take_of_length_le (by omega :
          block.length ≤ count)] using hblockPerm)
      have hp : pivot ∈ ((predecessor.drop start).take count) := by
        rw [hrestore] at hh; apply hh.mem_iff.mpr; apply List.mem_range'_1.mpr; dsimp [pivot]; omega
      have hb := List.mem_range'_1.mp (hmaxInterval.mem_iff.mp hp); omega
    have hnoAscent : ¬ Occurs [1, 2] block := by
      intro hascent; have hocc : Occurs [2, 3, 4, 1] (inflate skeleton start block) := by
        rcases hstart with hzero | hone
        · subst start
          cases skeleton with
          | nil => simp at hlarge
          | cons first tail =>
            exact ascending_first_inflation first tail block
              (by simpa using hskeletonPerm) hskeletonSimple
              (by simp only [List.length_cons] at hlarge; omega)
              hblockNormalized hascent
        · subst start
          cases skeleton with
          | nil => simp at hlarge
          | cons first tail =>
            cases tail with
            | nil => simp at hlarge
            | cons second tail =>
              have hsecond : second ≠ 1 := by simpa [pivot] using (show pivot ≠ 1 by omega)
              exact ascending_second_inflation first second tail block
                (by simpa using hskeletonPerm) hskeletonSimple (by simpa using hlarge)
                hsecond hblockNormalized hascent
      rw [hrestore] at hocc; exact hpreC [2, 3, 4, 1] (by decide) hocc
    have hdescending : block.Pairwise (· > ·) := by
      rw [List.pairwise_iff_forall_sublist]; intro first second hpair
      have hne : first ≠ second := by
        have hh := hblockNodup.sublist hpair; intro heq
        exact (List.nodup_cons.mp hh).1 (by simp [heq])
      by_contra hnot
      apply hnoAscent; let values := fun rank => if rank = 1 then first else second
      refine ⟨values, ?_, ?_, ?_, by simp⟩
      · intro rank hfirst hlast
        have hrank : rank = 1 := (by simp only [List.length_cons, List.length_nil] at hlast; omega)
        subst rank; dsimp [values]; omega
      · intro rank hfirst hlast; have hrank : rank = 1 ∨ rank = 2 := by
          simp only [List.length_cons, List.length_nil] at hlast; omega
        rcases hrank with rfl | rfl
        · change first ∈ block; exact hpair.subset (by simp)
        · change second ∈ block; exact hpair.subset (by simp)
      · simpa only [List.map_cons, List.map_nil, values, ite_true,
          Nat.reduceEqDiff, ite_false] using hpair
    have hreverse : block = (List.range' 1 count).reverse := by
      apply List.Perm.eq_of_pairwise (le := (· > ·))
        (fun first second _ _ hfirst hsecond => by omega) hdescending
        (List.pairwise_lt_range' 1).reverse
      exact hblockPerm.trans (List.reverse_perm _).symm
    have hpairs : ∀ index, index + 2 ≤ count →
        ((block.drop index).take 2).Perm (List.range' (count - index - 1) 2) := by
      intro index hindex
      have hpair : (block.drop index).take 2 = [count - index, count - index - 1] := by
        rw [hreverse]; apply List.ext_getElem
        · simp only [List.length_take, List.length_drop, List.length_reverse,
            List.length_range', List.length_cons, List.length_nil]
          omega
        · intro offset hleft hright
          have hoffset : offset = 0 ∨ offset = 1 := by simp at hright; omega
          rcases hoffset with rfl | rfl <;>
            simp only [List.getElem_take, List.getElem_drop, List.getElem_reverse,
              List.length_range', List.getElem_range'_1, List.getElem_cons_zero,
              List.getElem_cons_succ] <;> omega
      rw [hpair]; have heq : count - index = count - index - 1 + 1 := by omega
      rw [heq]; simpa only [List.range'_succ, List.range'_zero, Nat.add_sub_cancel] using
        List.Perm.swap (count - index - 1) (count - index - 1 + 1) []
    have hstartOne : start = 1 := by
      rcases hstart with hzero | hone
      · have hh := hintervals.2 0 2 (count - 1) (by omega) (by omega) (hpairs 0 (by omega))
        rw [hrestore] at hh; have hc := hcross (start + 0) 2 (pivot + (count - 1) - 1)
          (by omega) (by omega) (by omega) hh
        omega
      · exact hone
    have hsmall : count = 2 := by
      by_contra hnot
      have hh := hintervals.2 (count - 2) 2 1 (by omega) (by omega)
        (by simpa only [show count - (count - 2) - 1 = 1 by omega]
          using hpairs (count - 2) (by omega))
      rw [hrestore] at hh; have hc := hcross (start + (count - 2)) 2 (pivot + 1 - 1)
        (by omega) (by omega) (by omega) hh
      omega
    have hblock : block = [2, 1] := by rw [hreverse, hsmall]; rfl
    left
    have himage : predecessor = inflate skeleton 1 [2, 1] := by
      simpa only [hstartOne, hblock] using hrestore.symm
    refine ⟨skeleton, ⟨hskeletonPerm, hskeletonSimple, hskeletonC, hlarge,
      by simpa only [pivot, hstartOne] using (show pivot ≠ 1 by omega),
      by omega, himage⟩, ?_⟩
    intro alternative halt; obtain ⟨_, _, _, haltLength, _, _, haltImage⟩ := halt
    let recover := fun list : List ℕ =>
      let pivot := list.getD 2 0
      let down := fun entry => if pivot < entry then entry - 1 else entry
      (list.take 1).map down ++ pivot :: (list.drop 3).map down
    have hrecovery : ∀ original : List ℕ, 2 ≤ original.length →
        recover (inflate original 1 [2, 1]) = original := by
      intro original horiginal
      cases original with
      | nil => simp at horiginal
      | cons first rest =>
        cases rest with
        | nil => simp at horiginal
        | cons pivot tail =>
          let shift := fun entry : ℕ => if pivot < entry then entry + 1 else entry
          let down := fun entry : ℕ => if pivot < entry then entry - 1 else entry
          have hshape : inflate (first :: pivot :: tail) 1 [2, 1] =
              shift first :: (pivot + 1) :: pivot :: tail.map shift := by
            simp [inflate, shift]
          rw [hshape]; have hfirst : down (shift first) = first := by
            dsimp only [down, shift]
            split_ifs <;> omega
          change down (shift first) :: pivot :: (tail.map shift).map down = first :: pivot :: tail
          rw [hfirst, List.map_map]; congr 2
          calc
            tail.map (down ∘ shift) = tail.map id := by
              apply List.map_congr_left; intro entry _
              dsimp only [down, shift, Function.comp_def, id_eq]
              split_ifs <;> omega
            _ = tail := List.map_id _
    have hsame : inflate skeleton 1 [2, 1] = inflate alternative 1 [2, 1] :=
      himage.symm.trans haltImage
    have hskeletonRecovery := hrecovery skeleton (by omega)
    have halternativeRecovery := hrecovery alternative (by omega); rw [hsame] at hskeletonRecovery
    exact halternativeRecovery.symm.trans hskeletonRecovery
  · have htwoLength : skeleton.length = 2 := by omega
    have htwo : skeleton = [1, 2] ∨ skeleton = [2, 1] := by
      obtain ⟨first, second, heq⟩ := List.length_eq_two.mp htwoLength
      have hp : [first, second].Perm (List.range' 1 2) := by simpa [heq] using hskeletonPerm
      have hf := hp.mem_iff.mp (show first ∈ [first, second] by simp)
      have hs := hp.mem_iff.mp (show second ∈ [first, second] by simp)
      have hn := hp.nodup_iff.mpr (List.nodup_range' 1)
      simp only [List.range'_succ, List.range'_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hf hs
      rcases hf with rfl | rfl <;> rcases hs with rfl | rfl
      · simp at hn
      · exact Or.inl heq
      · exact Or.inr heq
      · simp at hn
    have hsmallPivot : skeleton.getD start 0 ≠ 1 := by
      intro hpivot; have hone : 1 ∈ block := hblockPerm.mem_iff.mpr
        (List.mem_range'_1.mpr (by omega))
      have hbeforeLength : (skeleton.take start).length = start := by simp; omega
      have hinside : ((predecessor.drop start).take count) =
          block.map (fun entry => skeleton.getD start 0 + entry - 1) := by
        rw [← hrestore]; simp only [inflate, List.append_assoc]
        rw [List.drop_append_of_le_length (by
          simp only [List.length_map, hbeforeLength]; omega)]
        rw [List.drop_eq_nil_iff.mpr (by simp), List.nil_append]
        rw [List.take_append_of_le_length (by
          simp only [List.length_map, hblockLength]; omega)]
        exact List.take_of_length_le (by simp only [List.length_map, hblockLength]; omega)
      have hmem : 1 ∈ (predecessor.drop start).take count := by
        rw [hinside]
        exact List.mem_map.mpr ⟨1, hone, by simpa only [Nat.add_sub_cancel] using hpivot⟩
      have hh := List.mem_range'_1.mp (hmaxInterval.mem_iff.mp hmem); omega
    rcases htwo with hskeleton | hskeleton
    · have hstartOne : start = 1 := by
        rcases hstart with hzero | hone
        · exact False.elim (hsmallPivot (by simp [hskeleton, hzero]))
        · exact hone
      right
      have hshape : predecessor = 1 :: block.map Nat.succ := by
        rw [← hrestore, hskeleton, hstartOne]; simp [inflate, Nat.add_comm]
      have hfirst : member.getD 0 0 = 2 := (by rw [← hinverse, hshape]; simp)
      rcases hleft hfirst with hparent | hinflation
      · exact Or.inl hparent
      · exact Or.inr (Or.inl hinflation)
    · have hstartZero : start = 0 := by
        rcases hstart with hzero | hone
        · exact hzero
        · exact False.elim (hsmallPivot (by simp [hskeleton, hone]))
      right
      right
      right
      have hshape : predecessor = block.map Nat.succ ++ [1] := by
        rw [← hrestore, hskeleton, hstartZero]
        simp only [inflate, List.getD_cons_zero, List.take_zero, List.map_nil,
          List.nil_append, List.drop_succ_cons, List.drop_zero, List.map_cons]
        have hmap : block.map (fun entry => 2 + entry - 1) = block.map Nat.succ := by
          apply List.map_congr_left; intro entry _; omega
        rw [hmap]; simp
      have hD : InD block := (skew_minimum_class block
        (fun entry hentry => (hblockBounds entry hentry).1)) (hshape ▸ hpreC)
      obtain ⟨cut, hchain⟩ := (two_decreasing_chains block hblockNodup).1.mp hD
      have hnewChain : predecessor.Pairwise (fun first second =>
          (first ≤ cut + 1 ↔ second ≤ cut + 1) → second < first) := by
        rw [hshape]; apply List.pairwise_append.mpr; refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
        · apply hchain.map; intro first second hrel hsame
          have hh := hrel (show first ≤ cut ↔ second ≤ cut by omega); omega
        · intro first hfirst second hsecond _; obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hfirst
          have hh := hblockBounds old hold; simp only [List.mem_singleton] at hsecond; omega
      have hpreD : InD predecessor := (two_decreasing_chains predecessor
        (hprePerm.nodup_iff.mpr (List.nodup_range' _))).1.mpr ⟨cut + 1, hnewChain⟩
      have hlen : predecessor.length = block.length + 1 := by simp [hshape]
      have hterminal : predecessor.getD (predecessor.length - 1) 0 = 1 := by
        rw [hlen]; simp [hshape]
      exact ⟨hpreD, hterminal, PopStackTerminalGap.terminal_gap_classification predecessor
        (by omega) hprePerm hpreD hterminal hcross⟩
end D5.S3.Combinatorics.PopStack.PopStackThirdDecomposition
