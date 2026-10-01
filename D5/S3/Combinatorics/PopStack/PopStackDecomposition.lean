/- GID: D5/S3/Combinatorics/PopStack/PopStackDecomposition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackDecomposition
   mirror-E: none(waiver:minimum-deletion-prefix-decomposition)
   anchors: [mathlib/module/Mathlib.Data.List.Sort]
   utility: none
   digest: Deleting a second-position minimum yields three unique predecessor branches. -/
import D5.S3.Combinatorics.PopStack.PopStackCrossing
import D5.S3.Combinatorics.PopStack.PopStackFamilies
import D5.S3.Combinatorics.PopStack.PopStackMinimum
import Mathlib.Data.List.Sort
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.PopStack.PopStackDecomposition
open PopStackDefs PopStackInflation PopStackCrossing PopStackFamilies
open PopStackChains
theorem minimum_two_decomposition (member : List ℕ) (hlength : 4 ≤ member.length)
    (hperm : member.Perm (List.range' 1 member.length)) (hC : InC member)
    (hminimum : member.getD 1 0 = 1) :
    let permutation := (member.eraseIdx 1).map Nat.pred
    permutation.Perm (List.range' 1 permutation.length) ∧ InC permutation ∧
      permutation.length + 1 = member.length ∧
      (permutation.map Nat.succ).insertIdx 1 1 = member ∧
      (IsSimple member ↔
      (IsSimple permutation ∧ permutation.getD 1 0 ≠ 1) ∨
        (∃ skeleton : List ℕ, skeleton.Perm (List.range' 1 skeleton.length) ∧
          IsSimple skeleton ∧ InC skeleton ∧ 4 ≤ skeleton.length ∧
          skeleton.length + 1 = permutation.length ∧
          permutation = inflate skeleton 0 [2, 1]) ∨ permutation = B permutation.length) := by
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
      intro index size hbound
      rw [hlength] at hbound
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
      intro index
      simp only [List.take_one, List.head?_eq_getElem?, List.getElem?_drop,
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
  have hskewPrefix (permutation : List ℕ) (hlength : 2 ≤ permutation.length)
      (hperm : permutation.Perm (List.range' 1 permutation.length))
      (hD : InD permutation)
      (hprefix : ∀ start size lower, 2 ≤ size → size < permutation.length →
        start + size ≤ permutation.length →
        ((permutation.drop start).take size).Perm (List.range' lower size) → start = 0) :
      let extended := permutation.map Nat.succ ++ [1]
      extended.Perm (List.range' 1 (permutation.length + 1)) ∧ InD extended ∧
        ((∀ start size lower, 2 ≤ size → size < extended.length → start + size ≤ extended.length →
          ((extended.drop start).take size).Perm (List.range' lower size) → start = 0) ↔
          permutation.getD (permutation.length - 1) 0 ≠ 1) := by
    let extended := permutation.map Nat.succ ++ [1]; change extended.Perm _ ∧ InD extended ∧
      ((∀ start size lower, 2 ≤ size → size < extended.length → start + size ≤ extended.length →
        ((extended.drop start).take size).Perm (List.range' lower size) → start = 0) ↔
        permutation.getD (permutation.length - 1) 0 ≠ 1)
    have hsize : extended.length = permutation.length + 1 := by
      simp only [extended, List.length_append, List.length_map, List.length_singleton]
    have hbounds : ∀ entry ∈ permutation, 1 ≤ entry ∧ entry ≤ permutation.length := by
      intro entry hentry; have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hentry); omega
    have hshiftRange : ∀ lower size,
        (List.range' lower size).map Nat.succ = List.range' (lower + 1) size := by
      intro lower size; simpa only [Nat.succ_eq_add_one] using
        (List.range'_succ_left (s := lower) (n := size)).symm
    have hpredRange : ∀ lower size, 1 ≤ lower →
        (List.range' lower size).map Nat.pred = List.range' (lower - 1) size := by
      intro lower size hpositive
      induction size generalizing lower with
      | zero => simp
      | succ size ih =>
        simp only [List.range'_succ, List.map_cons, Nat.pred_eq_sub_one, ih (lower + 1) (by omega)]
        congr 2; omega
    have hshiftPerm : (permutation.map Nat.succ).Perm (List.range' 2 permutation.length) := by
      simpa only [hshiftRange] using hperm.map Nat.succ
    have hpermExtended : extended.Perm (List.range' 1 (permutation.length + 1)) := by
      have hh := (hshiftPerm.append (List.Perm.refl [1])).trans List.perm_append_comm
      change (permutation.map Nat.succ ++ [1]).Perm _; rw [List.range'_succ]
      simpa only [List.singleton_append] using hh
    have hnodup : permutation.Nodup := hperm.nodup_iff.mpr (List.nodup_range' _)
    have hnodupExtended : extended.Nodup := hpermExtended.nodup_iff.mpr (List.nodup_range' _)
    obtain ⟨cut, hchain⟩ := (two_decreasing_chains permutation hnodup).1.mp hD
    have hchainExtended : extended.Pairwise (fun first second =>
        (first ≤ cut + 1 ↔ second ≤ cut + 1) → second < first) := by
      apply List.pairwise_append.mpr; refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
      · apply hchain.map; intro first second hrel hside; have hh := hrel (by omega); omega
      · intro first hfirst second hsecond _; obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hfirst
        have hh := hbounds old hold; simp only [List.mem_singleton] at hsecond; omega
    have hDExtended : InD extended :=
      (two_decreasing_chains extended hnodupExtended).1.mpr ⟨cut + 1, hchainExtended⟩
    have hinside : ∀ start size, start + size ≤ permutation.length →
        ((extended.drop start).take size) = ((permutation.drop start).take size).map Nat.succ := by
      intro start size hbound
      change ((((permutation.map Nat.succ ++ [1]).drop start).take size)) = _
      rw [List.drop_append_of_le_length (by simp only [List.length_map]; omega),
        List.take_append_of_le_length (by
          simp only [List.length_drop, List.length_map]; omega),
        ← List.map_drop, ← List.map_take]
    have hterminal : ∀ start size, start < permutation.length →
        start + size = permutation.length + 1 →
        ((extended.drop start).take size) = (permutation.drop start).map Nat.succ ++ [1] := by
      intro start size hstart hend
      change ((((permutation.map Nat.succ ++ [1]).drop start).take size)) = _
      rw [List.drop_append_of_le_length (by simp only [List.length_map]; omega), ← List.map_drop]
      apply List.take_of_length_le
      simp only [List.length_append, List.length_map, List.length_drop, List.length_singleton]
      omega
    have hlast : permutation.drop (permutation.length - 1) =
        [permutation.getD (permutation.length - 1) 0] := by
      apply List.ext_getElem
      · simp only [List.length_drop, List.length_cons, List.length_nil]
        omega
      · intro index hleft hright; have hzero : index = 0 := by
          simp only [List.length_cons, List.length_nil] at hright; omega
        subst index; simp only [List.getElem_drop, Nat.add_zero]
        rw [List.getD_eq_getElem _ _ (by omega)]; rfl
    refine ⟨hpermExtended, hDExtended, ?_⟩
    constructor
    · intro hnewPrefix heq
      have hsegment := hterminal (permutation.length - 1) 2 (by omega) (by omega)
      rw [hlast, heq] at hsegment
      have hinterval : ((extended.drop (permutation.length - 1)).take 2).Perm
          (List.range' 1 2) := by
        rw [hsegment]; exact List.Perm.swap 1 2 []
      have hh := hnewPrefix (permutation.length - 1) 2 1 (by omega) (by omega) (by omega) hinterval
      omega
    · intro hnotLast start size lower hnontrivial hproper hbound hinterval
      by_cases hcontained : start + size ≤ permutation.length
      · have hsegment := hinside start size hcontained
        have hlowerMem : lower ∈ ((extended.drop start).take size) :=
          hinterval.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
        rw [hsegment] at hlowerMem; obtain ⟨old, hold, heq⟩ := List.mem_map.mp hlowerMem
        have holdMem : old ∈ permutation :=
          ((List.take_sublist size _).trans (List.drop_sublist start _)).subset hold
        have hpositive := (hbounds old holdMem).1; have hlower : 2 ≤ lower := by omega
        have holdInterval : ((permutation.drop start).take size).Perm
            (List.range' (lower - 1) size) := by
          have hh := hinterval.map Nat.pred
          rw [hsegment, List.map_map, hpredRange lower size (by omega)] at hh
          simpa only [Function.comp_def, Nat.pred_succ, List.map_id_fun', id_eq] using hh
        by_cases hfull : size = permutation.length
        · omega
        · exact hprefix start size (lower - 1) hnontrivial (by omega) hcontained holdInterval
      · have hend : start + size = permutation.length + 1 := by omega
        have hstart : start < permutation.length := by omega
        have hsegment := hterminal start size hstart hend
        have hone : 1 ∈ (extended.drop start).take size := by rw [hsegment]; simp
        have hmin := List.mem_range'_1.mp (hinterval.mem_iff.mp hone)
        have hpositive : 1 ≤ lower := by
          have hlowerMem : lower ∈ ((extended.drop start).take size) :=
            hinterval.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
          rw [hsegment] at hlowerMem
          rcases List.mem_append.mp hlowerMem with hshift | hlast
          · obtain ⟨old, hold, heq⟩ := List.mem_map.mp hshift; omega
          · simp only [List.mem_singleton] at hlast; omega
        have hlower : lower = 1 := by omega
        have hshiftedSuffix : ((permutation.drop start).map Nat.succ).Perm
            (List.range' 2 (size - 1)) := by
          have hrange : List.range' lower size = 1 :: List.range' 2 (size - 1) := by
            have hsizeEq : size = (size - 1) + 1 := by omega
            conv_lhs => rw [hlower, hsizeEq, List.range'_succ]
          rw [hsegment, hrange] at hinterval
          exact ((List.perm_append_singleton 1 _).symm.trans hinterval).cons_inv
        have holdSuffix : (permutation.drop start).Perm (List.range' 1 (size - 1)) := by
          have hh := hshiftedSuffix.map Nat.pred
          rw [List.map_map, hpredRange 2 (size - 1) (by omega)] at hh
          simpa only [Function.comp_def, Nat.pred_succ, List.map_id_fun', id_eq,
            Nat.reduceSub] using hh
        have hstartPositive : 1 ≤ start := by omega
        by_cases hpair : size = 2
        · have hstartLast : start = permutation.length - 1 := by omega
          rw [hstartLast, hlast] at holdSuffix; have hentry := holdSuffix.mem_iff.mp
            (show permutation.getD (permutation.length - 1) 0 ∈
              [permutation.getD (permutation.length - 1) 0] by simp)
          simp only [hpair, List.range'_succ, List.range'_zero, List.mem_cons,
            List.not_mem_nil, or_false] at hentry
          exact False.elim (hnotLast hentry)
        · have holdInterval : ((permutation.drop start).take (size - 1)).Perm
              (List.range' 1 (size - 1)) := by
            have hfull : (permutation.drop start).length = size - 1 := by
              simp only [List.length_drop]; omega
            rw [List.take_of_length_le (by omega)]; exact holdSuffix
          have hh := hprefix start (size - 1) 1 (by omega) (by omega) (by omega) holdInterval; omega
  classical
  let permutation := (member.eraseIdx 1).map Nat.pred; have hindex : 1 < member.length := by omega
  have hentry : member[1]'hindex = 1 := by
    simpa only [List.getD_eq_getElem member 0 hindex] using hminimum
  have hremoved : (member.eraseIdx 1).Perm (List.range' 2 (member.length - 1)) := by
    have hh := (List.getElem_cons_eraseIdx_perm hindex).trans hperm; rw [hentry] at hh
    have hlengthEq : member.length = (member.length - 1) + 1 := by omega
    rw [hlengthEq, List.range'_succ] at hh; exact hh.cons_inv
  have hremovedPositive : ∀ value ∈ member.eraseIdx 1, 2 ≤ value := by
    intro value hvalue; have hh := List.mem_range'.mp (hremoved.mem_iff.mp hvalue); omega
  have hnormalizeRange : (List.range' 2 (member.length - 1)).map Nat.pred =
      List.range' 1 (member.length - 1) := by
    have hrange : (List.range' 1 (member.length - 1)).map Nat.succ =
        List.range' 2 (member.length - 1) := by
      simpa only [Nat.succ_eq_add_one] using
        (List.range'_succ_left (s := 1) (n := member.length - 1)).symm
    rw [← hrange, List.map_map]; exact List.map_id _
  have hpermutation : permutation.Perm (List.range' 1 permutation.length) := by
    have hh := hremoved.map Nat.pred; simpa only [hnormalizeRange, permutation, List.length_map,
      List.length_eraseIdx_of_lt hindex] using hh
  have hpermutationLength : permutation.length = member.length - 1 := by
    simp only [permutation, List.length_map, List.length_eraseIdx_of_lt hindex]
  have hpositive : ∀ value ∈ permutation, 1 ≤ value := by
    intro value hvalue; exact (List.mem_range'_1.mp (hpermutation.mem_iff.mp hvalue)).1
  have hmapInverse : permutation.map Nat.succ = member.eraseIdx 1 := by
    dsimp only [permutation]; rw [List.map_map]
    calc
      (member.eraseIdx 1).map (Nat.succ ∘ Nat.pred) = (member.eraseIdx 1).map id := by
        apply List.map_congr_left; intro value hvalue; have hh := hremovedPositive value hvalue
        dsimp
        omega
      _ = _ := List.map_id _
  have hinverse : (permutation.map Nat.succ).insertIdx 1 1 = member := by
    rw [hmapInverse]; simpa only [hentry] using List.insertIdx_eraseIdx_getElem hindex
  have hpermutationC : InC permutation := by
    apply (PopStackMinimum.minimum_insertion_inC permutation hpositive 1 (by omega)
      (by rw [hpermutationLength]; omega)).mp
    rw [hinverse]; exact hC
  refine ⟨hpermutation, hpermutationC, ?_, hinverse, ?_⟩
  · change permutation.length + 1 = member.length; omega
  have hpredecessorDecomposition : ∀ (permutation : List ℕ), 4 ≤ permutation.length →
      permutation.Perm (List.range' 1 permutation.length) → InC permutation →
      (IsSimple ((permutation.map Nat.succ).insertIdx 1 1) ↔
        (IsSimple permutation ∧ permutation.getD 1 0 ≠ 1) ∨
          (∃ skeleton : List ℕ, skeleton.Perm (List.range' 1 skeleton.length) ∧
            IsSimple skeleton ∧ InC skeleton ∧ 4 ≤ skeleton.length ∧
            skeleton.length + 1 = permutation.length ∧
            permutation = inflate skeleton 0 [2, 1]) ∨ permutation = B permutation.length) := by
    intro permutation hlength hperm hC
    classical
    have hpositive : ∀ entry ∈ permutation, 1 ≤ entry := by
      intro entry hentry; exact (List.mem_range'_1.mp (hperm.mem_iff.mp hentry)).1
    have hfirstNotMinimum : ∀ list : List ℕ, 3 ≤ list.length →
        list.Perm (List.range' 1 list.length) → IsSimple list → list.getD 0 0 ≠ 1 := by
      intro list hlength hperm hsimple hfirst
      cases list with
      | nil => simp at hlength
      | cons first tail =>
        simp only [List.getD_cons_zero] at hfirst; subst first
        have htail : tail.Perm (List.range' 2 tail.length) := by
          simpa only [List.length_cons, List.range'_succ] using hperm.cons_inv
        exact hsimple 1 tail.length 2 (by simp only [List.length_cons] at hlength; omega)
          (by simp) (by simp; omega) (by
            simpa only [List.drop_succ_cons, List.drop_zero, List.take_length] using htail)
    refine ⟨fun hinsertSimple => ?_, ?_⟩
    · have hcriterion := (minimum_insertion_simple permutation hpositive 1
        (by omega)).mp hinsertSimple
      have hintervals : ∀ start count lower, 2 ≤ count → count < permutation.length →
          start + count ≤ permutation.length →
          ((permutation.drop start).take count).Perm (List.range' lower count) →
          start = 0 ∧ 2 ≤ lower := by
        intro start count lower hcount hproper hbound hinterval
        have hh := hcriterion.1 start count lower hcount hproper hbound hinterval
        exact ⟨by omega, hh.2.2⟩
      by_cases hsimple : IsSimple permutation
      · exact Or.inl ⟨hsimple, hcriterion.2.2⟩
      right
      obtain ⟨start, count, lower, skeleton, block, hcount, hproper, hbound,
        hstartGap, _, hlower, hmaxInterval, hskeletonPerm, hblockPerm, hblockLength,
        hskeletonLength, hinverse, _, hskeletonSimple, hskeletonC, _⟩ :=
          crossing_decomposition permutation 1 hperm hC hsimple (by
            intro index size bottom hsize hsizeProper hsizeBound hinterval
            obtain ⟨hzero, hbottom⟩ :=
              hintervals index size bottom hsize hsizeProper hsizeBound hinterval
            exact ⟨by omega, by omega, by omega⟩)
      have hstart : start = 0 := by omega
      subst start; have hskeletonLower : 2 ≤ skeleton.length := by omega
      have hskeletonNotThree : skeleton.length ≠ 3 := by
        intro hthree; obtain ⟨first, second, third, hshape⟩ := List.length_eq_three.mp hthree
        have hpermThree : [first, second, third].Perm (List.range' 1 3) := by
          simpa only [hshape, List.length_cons, List.length_nil, Nat.reduceAdd] using hskeletonPerm
        have hentries : ∀ entry ∈ [first, second, third], entry = 1 ∨ entry = 2 ∨ entry = 3 := by
          intro entry hentry; have hh := hpermThree.mem_iff.mp hentry
          simpa only [List.range'_succ, List.range'_zero, List.mem_cons, List.not_mem_nil,
            or_false, Nat.reduceAdd] using hh
        have hfirst := hentries first (by simp); have hsecond := hentries second (by simp)
        have hthird := hentries third (by simp)
        have hnodup := hpermThree.nodup_iff.mpr (List.nodup_range' _)
        rw [hshape] at hskeletonSimple
        rcases hfirst with rfl | rfl | rfl <;> rcases hsecond with rfl | rfl | rfl <;>
          rcases hthird with rfl | rfl | rfl
        all_goals try simp at hnodup
        all_goals first
          | exact hskeletonSimple 0 2 1 (by decide) (by decide) (by decide) (by decide)
          | exact hskeletonSimple 0 2 2 (by decide) (by decide) (by decide) (by decide)
          | exact hskeletonSimple 1 2 1 (by decide) (by decide) (by decide) (by decide)
          | exact hskeletonSimple 1 2 2 (by decide) (by decide) (by decide) (by decide)
      have hblockNormalized : block.Perm (List.range' 1 block.length) := by
        simpa only [hblockLength] using hblockPerm
      have hblockNodup := hblockNormalized.nodup_iff.mpr (List.nodup_range' _)
      have hblockBounds : ∀ entry ∈ block, 1 ≤ entry ∧ entry ≤ count := by
        intro entry hentry; have hh := List.mem_range'_1.mp (hblockPerm.mem_iff.mp hentry); omega
      let pivot := skeleton.getD 0 0; have hinside : ∀ index size, index + size ≤ count →
          ((permutation.drop index).take size) =
            ((block.drop index).take size).map (fun entry => pivot + entry - 1) := by
        intro index size hsize; rw [← hinverse]
        simp only [inflate, List.take_zero, List.map_nil, List.nil_append]
        rw [List.drop_append_of_le_length (by simp only [List.length_map, hblockLength]; omega),
          List.take_append_of_le_length (by
            simp only [List.length_drop, List.length_map, hblockLength]; omega),
          ← List.map_drop, ← List.map_take]
      by_cases hlarge : 3 ≤ skeleton.length
      · have hnoAscent : ¬ Occurs [1, 2] block := by
          intro hascent
          cases skeleton with
          | nil => simp at hskeletonLower
          | cons first tail =>
            have hocc := ascending_first_inflation first tail block
              (by simpa using hskeletonPerm) hskeletonSimple (by simpa using hlarge)
              hblockNormalized hascent
            rw [hinverse] at hocc; exact hC [2, 3, 4, 1] (by decide) hocc
        have hdescending : block.Pairwise (· > ·) := by
          rw [List.pairwise_iff_forall_sublist]; intro first second hpair
          have hne : first ≠ second := by
            have hh := hblockNodup.sublist hpair; intro heq
            exact (List.nodup_cons.mp hh).1 (by simp [heq])
          by_contra hnot
          have hascent : Occurs [1, 2] block := by
            let values := fun rank => if rank = 1 then first else second
            refine ⟨values, ?_, ?_, ?_, by simp⟩
            · intro rank hfirst hlast; have hrank : rank = 1 := by
                simp only [List.length_cons, List.length_nil] at hlast; omega
              subst rank; dsimp [values]; omega
            · intro rank hfirst hlast; have hrank : rank = 1 ∨ rank = 2 := by
                simp only [List.length_cons, List.length_nil] at hlast; omega
              rcases hrank with rfl | rfl
              · change first ∈ block; exact hpair.subset (by simp)
              · change second ∈ block; exact hpair.subset (by simp)
            · simpa only [List.map_cons, List.map_nil, values, ite_true,
                Nat.reduceEqDiff, ite_false] using hpair
          exact hnoAscent hascent
        have hreverse : block = (List.range' 1 count).reverse := by
          apply List.Perm.eq_of_pairwise (le := (· > ·))
            (fun first second _ _ hfirst hsecond => by omega) hdescending
            (List.pairwise_lt_range' 1).reverse
          exact hblockPerm.trans (List.reverse_perm _).symm
        have hsmall : count = 2 := by
          by_contra hnot
          have hlastPair : (block.drop (count - 2)).take 2 = [2, 1] := by
            rw [hreverse]; apply List.ext_getElem
            · simp only [List.length_take, List.length_drop, List.length_reverse,
                List.length_range', List.length_cons, List.length_nil]
              omega
            · intro index hindex hright; have hindexCases : index = 0 ∨ index = 1 := by
                simp only [List.length_cons, List.length_nil] at hright; omega
              rcases hindexCases with rfl | rfl <;>
                simp only [List.getElem_take, List.getElem_drop, List.getElem_reverse,
                  List.length_range', List.getElem_range'_1, List.getElem_cons_zero,
                  List.getElem_cons_succ] <;> omega
          have hpair : ((permutation.drop (count - 2)).take 2).Perm (List.range' pivot 2) := by
            rw [hinside (count - 2) 2 (by omega), hlastPair]
            have hmap : [2, 1].map (fun entry => pivot + entry - 1) = [pivot + 1, pivot] := by
              simp only [List.map_cons, List.map_nil]; congr 1
            rw [hmap]; simpa only [List.range'_succ, List.range'_zero] using
              List.Perm.swap pivot (pivot + 1) []
          have hh := hintervals (count - 2) 2 pivot (by omega) (by omega) (by omega) hpair; omega
        have hblock : block = [2, 1] := (by rw [hreverse, hsmall]; rfl)
        left
        exact ⟨skeleton, hskeletonPerm, hskeletonSimple, hskeletonC, by omega, by omega,
          by simpa only [hblock] using hinverse.symm⟩
      · have hskeletonTwo : skeleton.length = 2 := by omega
        have htwo : skeleton = [1, 2] ∨ skeleton = [2, 1] := by
          obtain ⟨first, second, heq⟩ := List.length_eq_two.mp hskeletonTwo
          have hpermTwo : [first, second].Perm (List.range' 1 2) := by
            simpa only [heq, List.length_cons, List.length_nil, Nat.reduceAdd] using hskeletonPerm
          have hfirst := hpermTwo.mem_iff.mp (by simp : first ∈ [first, second])
          have hsecond := hpermTwo.mem_iff.mp (by simp : second ∈ [first, second])
          have hnodup := (hpermTwo.nodup_iff.mpr (List.nodup_range' _))
          simp only [List.range'_succ, List.range'_zero, List.mem_cons, List.not_mem_nil,
            or_false] at hfirst hsecond
          simp only [List.nodup_cons, List.mem_singleton] at hnodup
          rcases hfirst with rfl | rfl <;> rcases hsecond with rfl | rfl
          · exact False.elim (hnodup.1 rfl)
          · exact Or.inl heq
          · exact Or.inr heq
          · exact False.elim (hnodup.1 rfl)
        rcases htwo with hskeleton | hskeleton
        · have honeMem : 1 ∈ block := hblockPerm.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
          have hfirstBlock : 1 ∈ permutation.take count := by
            have hh : 1 ∈ block.map (fun entry => pivot + entry - 1) :=
              List.mem_map.mpr ⟨1, honeMem,
              show pivot + 1 - 1 = 1 by simp [pivot, hskeleton]⟩
            have hfull : block.take count = block := List.take_of_length_le (by omega)
            have hsegment := hinside 0 count (by omega)
            simp only [List.drop_zero, hfull] at hsegment; rw [hsegment]; exact hh
          have hh := List.mem_range'_1.mp (hmaxInterval.mem_iff.mp hfirstBlock); omega
        · right
          have hskew : permutation = block.map Nat.succ ++ [1] := by
            rw [← hinverse, hskeleton]
            simp only [inflate, List.getD_cons_zero, List.take_zero, List.map_nil,
              List.nil_append, List.drop_succ_cons, List.drop_zero, List.map_cons, List.map_nil]
            have hmap : block.map (fun entry => 2 + entry - 1) = block.map Nat.succ := by
              apply List.map_congr_left; intro entry _; omega
            rw [hmap]; simp
          have hD : InD block := (skew_minimum_class block
            (fun entry hentry => (hblockBounds entry hentry).1)) (hskew ▸ hC)
          have hsuccRange : ∀ bottom size,
              (List.range' bottom size).map Nat.succ = List.range' (bottom + 1) size := by
            intro bottom size; simpa only [Nat.succ_eq_add_one] using
              (List.range'_succ_left (s := bottom) (n := size)).symm
          have hblockPrefix : ∀ index size bottom, 2 ≤ size → size < count → index + size ≤ count →
              ((block.drop index).take size).Perm (List.range' bottom size) → index = 0 := by
            intro index size bottom hsize hsizeProper hsizeBound hinterval
            have hh := hinterval.map Nat.succ; rw [hsuccRange] at hh
            have hsegment : ((permutation.drop index).take size) =
                ((block.drop index).take size).map Nat.succ := by
              rw [hskew, List.drop_append_of_le_length (by simp only [List.length_map]; omega),
                List.take_append_of_le_length (by
                  simp only [List.length_drop, List.length_map]; omega),
                ← List.map_drop, ← List.map_take]
            rw [← hsegment] at hh
            exact (hintervals index size (bottom + 1) hsize (by omega) (by omega) hh).1
          have hlastNotMinimum : block.getD (count - 1) 0 ≠ 1 := by
            have hh := hskewPrefix block (by omega) hblockNormalized hD
              (by simpa only [hblockLength] using hblockPrefix)
            have hcriterion : ((∀ index size bottom, 2 ≤ size →
                  size < (block.map Nat.succ ++ [1]).length →
                  index + size ≤ (block.map Nat.succ ++ [1]).length →
                  (((block.map Nat.succ ++ [1]).drop index).take size).Perm
                    (List.range' bottom size) → index = 0) ↔
                  block.getD (count - 1) 0 ≠ 1) := by
              simpa only [hblockLength] using hh.2.2
            apply hcriterion.mp; intro index size bottom hsize hsizeProper hsizeBound hinterval
            rw [← hskew] at hsizeProper hsizeBound hinterval
            exact (hintervals index size bottom hsize hsizeProper hsizeBound hinterval).1
          have hblockA : block = A count := by
            have hh := (prefix_families count hcount).2.2 block |>.mp ⟨hblockPerm, hD, hblockPrefix⟩
            rcases hh with heq | heq
            · exact heq
            · have hlast := (prefix_families count hcount).2.1; rw [← heq] at hlast
              exact False.elim (hlastNotMinimum hlast)
          have hcountEq : count = permutation.length - 1 := by omega
          rw [B, if_neg (by omega), ← hcountEq, ← hblockA, ← hskew]
    · intro hcases; apply (minimum_insertion_simple permutation hpositive 1 (by omega)).mpr
      rcases hcases with ⟨hsimple, hsecond⟩ | hbond | hskewFamily
      · refine ⟨?_, hfirstNotMinimum permutation (by omega) hperm hsimple, hsecond⟩
        intro index size bottom hsize hproper hbound hinterval
        exact False.elim (hsimple index size bottom hsize hproper hbound hinterval)
      · obtain ⟨skeleton, hskeletonPerm, hskeletonSimple, _, hskeletonLarge,
          hskeletonLength, hshape⟩ := hbond
        let pivot := skeleton.getD 0 0
        let shift := fun entry => if pivot < entry then entry + 1 else entry
        have hpivot : 2 ≤ pivot := by
          have hnot := hfirstNotMinimum skeleton (by omega) hskeletonPerm hskeletonSimple
          have hmem : pivot ∈ skeleton := by
            dsimp only [pivot]; rw [List.getD_eq_getElem _ 0 (by omega)]
            exact List.getElem_mem (by omega)
          have hh := List.mem_range'_1.mp (hskeletonPerm.mem_iff.mp hmem); omega
        have hinflate : permutation = (pivot + 1) :: pivot :: (skeleton.drop 1).map shift := by
          rw [hshape]; simp [inflate, pivot, shift]
        refine ⟨?_, ?_, ?_⟩
        · intro index size bottom hsize hproper hbound hinterval
          have hh := (PopStackPrime.inflation_intervals skeleton [2, 1] 0 hskeletonPerm
            hskeletonSimple hskeletonLarge (by omega) (by decide) (by simp)).1
              index size bottom hsize (by rw [← hshape]; exact hproper)
              (by rw [← hshape]; exact hbound) (by rw [← hshape]; exact hinterval)
          simp only [List.length_cons, List.length_nil] at hh; have hindex : index = 0 := by omega
          have hsizeTwo : size = 2 := by omega
          rw [hinflate, hindex, hsizeTwo] at hinterval
          have hbottomMem : bottom ∈ [pivot + 1, pivot] := hinterval.mem_iff.mpr
            (List.mem_range'_1.mpr (by omega))
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hbottomMem
          exact ⟨by omega, by omega, by omega⟩
        · rw [hinflate]; change pivot + 1 ≠ 1; omega
        · rw [hinflate]; simp only [List.getD_cons_succ, List.getD_cons_zero]; omega
      · let length := permutation.length
        obtain ⟨_, _, hprefix⟩ := (prefix_families length (by omega)).2.2 permutation |>.mpr
          (Or.inr hskewFamily)
        have hshape : permutation = (A (length - 1)).map Nat.succ ++ [1] := by
          calc
            permutation = B length := hskewFamily
            _ = _ := by rw [B, if_neg (by dsimp [length]; omega)]
        have hAperm := ((prefix_families (length - 1) (by dsimp [length]; omega)).2.2
          (A (length - 1))).mpr (Or.inl rfl) |>.1
        have hAlength : (A (length - 1)).length = length - 1 := by
          simpa only [List.length_range'] using hAperm.length_eq
        have hApositive : ∀ entry ∈ A (length - 1), 1 ≤ entry := by
          intro entry hentry; exact (List.mem_range'_1.mp (hAperm.mem_iff.mp hentry)).1
        have hneighbors : ∀ index, index ≤ 1 → permutation.getD index 0 ≠ 1 := by
          intro index hindex; have hposition : index < (A (length - 1)).length := by
            rw [hAlength]; dsimp [length]; omega
          rw [hshape, List.getD_eq_getElem _ 0 (by
            simp only [List.length_append, List.length_map, hAlength, List.length_singleton]
            dsimp [length] at hAlength; omega), List.getElem_append_left (by
            simp only [List.length_map, hAlength]; dsimp [length]; omega), List.getElem_map]
          have hh := hApositive ((A (length - 1))[index]'hposition) (List.getElem_mem hposition)
          omega
        refine ⟨?_, hneighbors 0 (by omega), hneighbors 1 le_rfl⟩
        intro index size bottom hsize hproper hbound hinterval
        have hindex := hprefix index size bottom hsize hproper hbound hinterval; subst index
        have hsegment : permutation.take size = ((A (length - 1)).take size).map Nat.succ := by
          rw [hshape, List.take_append_of_le_length (by
            simp only [List.length_map, hAlength]; dsimp [length] at hAlength; omega),
            ← List.map_take]
        have hbottomMem : bottom ∈ permutation.take size := hinterval.mem_iff.mpr
          (List.mem_range'_1.mpr (by omega))
        rw [hsegment] at hbottomMem; obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hbottomMem
        have hh := hApositive entry (List.mem_of_mem_take hentry)
        exact ⟨by omega, by omega, by omega⟩
  by_cases hlarge : 4 ≤ permutation.length
  · simpa only [hinverse] using
      hpredecessorDecomposition permutation hlarge hpermutation hpermutationC
  have hthree : permutation.length = 3 := by rw [hpermutationLength] at *; omega
  obtain ⟨first, second, third, hshape⟩ := List.length_eq_three.mp hthree
  have hpermThree : [first, second, third].Perm (List.range' 1 3) := by
    simpa only [hshape, List.length_cons, List.length_nil, Nat.reduceAdd] using hpermutation
  have hentries : ∀ value ∈ [first, second, third], value = 1 ∨ value = 2 ∨ value = 3 := by
    intro value hvalue
    simpa only [List.range'_succ, List.range'_zero, List.mem_cons, List.not_mem_nil,
      or_false, Nat.reduceAdd] using hpermThree.mem_iff.mp hvalue
  have hfirst := hentries first (by simp); have hsecond := hentries second (by simp)
  have hthird := hentries third (by simp)
  have hnodup := hpermThree.nodup_iff.mpr (List.nodup_range' _)
  have hfinite : ∀ index : Fin 4, ∀ size : Fin 4, ∀ lower : Fin 5,
      2 ≤ size.val → size.val < 4 → index.val + size.val ≤ 4 →
      ¬ (([3, 1, 4, 2].drop index.val).take size.val).Perm
        (List.range' lower.val size.val) := by decide
  have hseedSimple : IsSimple [3, 1, 4, 2] := by
    intro index size lower hsize hproper hbound hinterval
    have hsizeBound : size < 4 := by simpa using hproper
    have hindexBound : index < 4 := by simp at hbound; omega
    have hlowerMem : lower ∈ ([3, 1, 4, 2].drop index).take size :=
      hinterval.mem_iff.mpr (List.mem_range'.mpr ⟨0, by omega, by omega⟩)
    have hlowerOriginal := List.mem_of_mem_drop (List.mem_of_mem_take hlowerMem)
    have hlowerBound : lower < 5 := by simp at hlowerOriginal; omega
    exact hfinite ⟨index, hindexBound⟩ ⟨size, hsizeBound⟩ ⟨lower, hlowerBound⟩
      hsize hsizeBound (by simpa using hbound) hinterval
  have hnoSkeleton : ¬ ∃ skeleton : List ℕ,
      skeleton.Perm (List.range' 1 skeleton.length) ∧ IsSimple skeleton ∧
        InC skeleton ∧ 4 ≤ skeleton.length ∧ skeleton.length + 1 = permutation.length ∧
          permutation = inflate skeleton 0 [2, 1] := by
    rintro ⟨skeleton, _, _, _, hlarge, hsize, _⟩; omega
  change IsSimple member ↔ (IsSimple permutation ∧ permutation.getD 1 0 ≠ 1) ∨
      (∃ skeleton : List ℕ, skeleton.Perm (List.range' 1 skeleton.length) ∧
        IsSimple skeleton ∧ InC skeleton ∧ 4 ≤ skeleton.length ∧
        skeleton.length + 1 = permutation.length ∧
        permutation = inflate skeleton 0 [2, 1]) ∨ permutation = B permutation.length
  simp only [hnoSkeleton, false_or]; rw [← hinverse, hshape]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
  rcases hfirst with rfl | rfl | rfl <;> rcases hsecond with rfl | rfl | rfl <;>
    rcases hthird with rfl | rfl | rfl
  all_goals try simp at hnodup
  all_goals simp only [List.map_cons, List.map_nil, Nat.succ_eq_add_one, Nat.reduceAdd,
    List.insertIdx_succ_cons, List.insertIdx_zero]
  all_goals constructor
  all_goals intro hh
  all_goals first
    | exact Or.inr (by decide)
    | exact hseedSimple
    | exact False.elim (hh 0 2 1 (by decide) (by decide) (by decide) (by decide))
    | exact False.elim (hh 0 2 2 (by decide) (by decide) (by decide) (by decide))
    | exact False.elim (hh 0 2 3 (by decide) (by decide) (by decide) (by decide))
    | exact False.elim (hh 1 2 1 (by decide) (by decide) (by decide) (by decide))
    | exact False.elim (hh 1 2 2 (by decide) (by decide) (by decide) (by decide))
    | exact False.elim (hh 1 2 3 (by decide) (by decide) (by decide) (by decide))
    | exact False.elim (hh 2 2 1 (by decide) (by decide) (by decide) (by decide))
    | exact False.elim (hh 2 2 2 (by decide) (by decide) (by decide) (by decide))
    | rcases hh with ⟨hsimple, _⟩ | hskew
      · first
        | exact False.elim (hsimple 0 2 1 (by decide) (by decide) (by decide) (by decide))
        | exact False.elim (hsimple 0 2 2 (by decide) (by decide) (by decide) (by decide))
        | exact False.elim (hsimple 1 2 1 (by decide) (by decide) (by decide) (by decide))
        | exact False.elim (hsimple 1 2 2 (by decide) (by decide) (by decide) (by decide))
      · simp [B, A, PopStackParallel.P] at hskew
end D5.S3.Combinatorics.PopStack.PopStackDecomposition
