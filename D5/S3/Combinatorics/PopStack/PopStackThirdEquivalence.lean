/- GID: D5/S3/Combinatorics/PopStack/PopStackThirdEquivalence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackThirdEquivalence
   mirror-E: none(waiver:recursive-five-branch-bijection)
   anchors: [mathlib/module/Mathlib.Data.List.Permutation]
   utility: none
   digest: The five recursive branches give inverse minimum-position replacement maps. -/
import D5.S3.Combinatorics.PopStack.PopStackThirdBijection
import Mathlib.Data.List.Permutation
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.PopStack.PopStackThirdEquivalence
open PopStackDefs PopStackInflation PopStackFamilies PopStackM3Disjoint
open PopStackTerminalGap PopStackTerminalIntervals PopStackThirdBijection
open PopStackDecomposition PopStackThirdDecomposition PopStackLeftDecomposition
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem third_minimum_bijection (size : ℕ) (hsize : 4 ≤ size) :
    let source := {member : List ℕ | member ∈ simples size ∧ member.getD 1 0 = 1}
    let target := {member : List ℕ | member ∈ simples size ∧ member.getD 2 0 = 1}
    Set.BijOn (Phi size) source target ∧
      (∀ member ∈ source, undoPhi size (Phi size member) = member) ∧
      (∀ member ∈ target, Phi size (undoPhi size member) = member) := by
  have minimum_insertion_simple (permutation : List ℕ)
      (hpositive : ∀ value ∈ permutation, 1 ≤ value)
      (gap : ℕ) (hinterior : 0 < gap ∧ gap < permutation.length) :
      (∀ index size lower, 2 ≤ size → size < permutation.length →
        index + size ≤ permutation.length →
        ((permutation.drop index).take size).Perm (List.range' lower size) →
        index < gap ∧ gap < index + size ∧ 2 ≤ lower) ∧
      permutation.getD (gap - 1) 0 ≠ 1 ∧ permutation.getD gap 0 ≠ 1 →
      IsSimple ((permutation.map Nat.succ).insertIdx gap 1) := by
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
    have hpredRange : ∀ lower size, 1 ≤ lower →
        (List.range' lower size).map Nat.pred = List.range' (lower - 1) size := by
      intro lower size hlower
      simpa only [← Nat.pred_eq_sub_one] using (List.map_sub_range' hlower size)
    have hpredSucc : ∀ segment : List ℕ, (segment.map Nat.succ).map Nat.pred = segment := by
      intro segment; simp [List.map_map, Function.comp_def]
    have hget : ∀ index, permutation.getD index 0 = 1 ↔
        ((permutation.drop index).take 1) = [1] := by
      intro index
      simp only [List.take_one, List.head?_eq_getElem?, List.getElem?_drop,
        List.getD_eq_getElem?_getD]
      cases permutation[index]? <;> simp
    rintro ⟨hintervals, hleft, hright⟩ index size lower hsize hproper hbound hperm
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
  classical
  let up := fun entry : ℕ => if entry = 1 then 1 else entry + 1
  let down := fun entry : ℕ => if entry = 1 then 1 else entry - 1
  let insert := fun index : ℕ => fun member : List ℕ =>
    (member.map Nat.succ).insertIdx index 1
  have hnormalize : ∀ member : List ℕ, member.Perm (List.range' 1 member.length) →
      ((member.map up).map down = member) := by
    intro member hp; rw [List.map_map]
    calc
      member.map (down ∘ up) = member.map id := by
        apply List.map_congr_left
        intro entry he; have hb := (List.mem_range'_1.mp (hp.mem_iff.mp he)).1
        dsimp [up, down]; split_ifs <;> omega
      _ = member := List.map_id _
  have hraise : ∀ member : List ℕ, member.Perm (List.range' 1 member.length) → ∀ pivot : ℕ,
      1 ≤ pivot → pivot ≤ member.length + 1 →
      (pivot :: member.map (fun entry => if pivot ≤ entry then entry + 1 else entry)).Perm
        (List.range' 1 (member.length + 1)) := by
    intro member hp pivot hlo hhi
    let shift := fun entry : ℕ => if pivot ≤ entry then entry + 1 else entry
    have hinj : Function.Injective shift := by
      intro first second he; dsimp [shift] at he
      split_ifs at he <;> omega
    have hmissing : pivot ∉ member.map shift := by
      intro hm; obtain ⟨entry, _, he⟩ := List.mem_map.mp hm
      dsimp [shift] at he; split_ifs at he <;> omega
    apply (List.perm_ext_iff_of_nodup
      (List.nodup_cons.mpr ⟨hmissing, (hp.nodup_iff.mpr (List.nodup_range' _)).map hinj⟩)
      (List.nodup_range' _)).mpr
    intro entry; constructor
    · intro hm; rcases List.mem_cons.mp hm with rfl | hm
      · exact List.mem_range'_1.mpr ⟨hlo, by omega⟩
      · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
        have hb := List.mem_range'_1.mp (hp.mem_iff.mp hold); apply List.mem_range'_1.mpr
        dsimp [shift]; split_ifs <;> omega
    · intro hm; have hb := List.mem_range'_1.mp hm
      by_cases he : entry = pivot
      · exact List.mem_cons.mpr (Or.inl he)
      · apply List.mem_cons.mpr ∘ Or.inr
        by_cases hl : entry < pivot
        · exact List.mem_map.mpr ⟨entry,
            hp.mem_iff.mpr (List.mem_range'_1.mpr (by omega)), by simp [shift, hl]⟩
        · exact List.mem_map.mpr ⟨entry - 1, hp.mem_iff.mpr (List.mem_range'_1.mpr (by omega)), by
              dsimp [shift]; rw [if_pos (by omega)]; omega⟩
  have hinsert : ∀ member : List ℕ, member.Perm (List.range' 1 member.length) → InC member →
      ∀ index : ℕ, index ≤ 2 → index ≤ member.length →
      (insert index member).Perm (List.range' 1 (member.length + 1)) ∧
        InC (insert index member) ∧ (insert index member).length = member.length + 1 ∧
        (insert index member).getD index 0 = 1 ∧
        ((insert index member).eraseIdx index).map Nat.pred = member := by
    intro member hp hc index hi hb; have hpos : ∀ entry ∈ member, 1 ≤ entry := by
      intro entry he; exact (List.mem_range'_1.mp (hp.mem_iff.mp he)).1
    have hr := hp.map Nat.succ
    have hmap : (List.range' 1 member.length).map Nat.succ = List.range' 2 member.length := by
      simpa only [Nat.succ_eq_add_one] using (List.range'_succ_left ..).symm
    rw [hmap] at hr; refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (List.perm_insertIdx _ _ (by simp; omega)).trans
        (by simpa only [List.range'_succ] using hr.cons 1)
    · exact (PopStackMinimum.minimum_insertion_inC member hpos index hi hb).mpr hc
    · simp [insert, List.length_insertIdx, hb]
    · rw [List.getD_eq_getElem _ 0 (by simp [insert, List.length_insertIdx, hb])]
      exact List.getElem_insertIdx_self (by simp [List.length_insertIdx, hb])
    · simp [insert, List.eraseIdx_insertIdx_self, List.map_map, Function.comp_def]
  have hfirstExclusion : ∀ member : List ℕ,
      member.Perm (List.range' 1 member.length) → IsSimple member →
      4 ≤ member.length → member.getD 0 0 ≠ 1 := by
    intro member hp hs hl he; cases member with
    | nil => simp at hl
    | cons first tail =>
      have hh : first = 1 := by simpa using he
      subst first; have ht : tail.Perm (List.range' 2 tail.length) := by
        rw [List.length_cons, List.range'_succ] at hp; exact hp.cons_inv
      exact hs 1 tail.length 2 (by simp only [List.length_cons] at hl; omega)
        (by simp) (by simp; omega) (by simpa using ht)
  have hdouble : ∀ member : List ℕ,
      member.Perm (List.range' 1 member.length) → InC member → 4 ≤ member.length →
      ∀ index : ℕ, index ≤ 1 →
      (inflate member index [2, 1]).Perm (List.range' 1 (member.length + 1)) ∧
        InC (inflate member index [2, 1]) ∧
        (inflate member index [2, 1]).length = member.length + 1 ∧
        ¬ IsSimple (inflate member index [2, 1]) := by
    intro member hp hc hl index hi; have hn := hp.nodup_iff.mpr (List.nodup_range' _)
    have hb : index < member.length := by omega
    let pivot := member.getD index 0; have hpivot := List.mem_range'_1.mp (hp.mem_iff.mp
      (show pivot ∈ member by
        dsimp [pivot]; rw [List.getD_eq_getElem _ 0 hb]; exact List.getElem_mem hb))
    let shift := fun entry : ℕ => if pivot < entry then entry + 1 else entry
    have hraised : ((pivot + 1) :: member.map shift).Perm (List.range' 1 (member.length + 1)) := by
      simpa only [show (fun entry => if pivot + 1 ≤ entry then entry + 1 else entry) =
          shift by funext entry; simp [shift]] using
        hraise member hp (pivot + 1) (by omega) (by omega)
    have hget : member = member.take index ++ member[index]'hb :: member.drop (index + 1) := by
      conv_lhs => rw [← List.take_append_drop index member]
      rw [List.drop_eq_getElem?_toList_append (l := member) (i := index),
        List.getElem?_eq_getElem hb]
      simp
    have hpv : member[index]'hb = pivot := by dsimp [pivot]; rw [List.getD_eq_getElem _ 0 hb]
    have hshape : inflate member index [2, 1] =
        (member.take index).map shift ++ (pivot + 1) :: pivot ::
          (member.drop (index + 1)).map shift := by
      simp [inflate, pivot, shift]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hshape]; have hm : member.map shift = (member.take index).map shift ++
          pivot :: (member.drop (index + 1)).map shift := by
        conv_lhs => rw [hget]
        simp [hpv, shift]
      rw [hm] at hraised; exact List.perm_middle.trans hraised
    · rw [hpv] at hget; have hh := PopStackDecreasing.decreasing_early_inflation (member.take index)
        (member.drop (index + 1)) pivot (by simp [List.length_take]; omega)
        (hget ▸ hn) (hget ▸ hc)
      rw [← hget, List.length_take, Nat.min_eq_left (by omega)] at hh; exact hh
    · simp [inflate, List.length_take, List.length_drop]; omega
    · intro hs; have hinterval : (((inflate member index [2, 1]).drop index).take 2).Perm
          (List.range' pivot 2) := by
        rw [hshape]; have ht : ((member.take index).map shift).length = index := by simp; omega
        nth_rw 1 [← ht]
        rw [List.drop_left]; simpa [List.range'_succ] using List.Perm.swap pivot (pivot + 1) []
      exact hs index 2 pivot (by omega) (by rw [hshape]; simp; omega)
        (by rw [hshape]; simp [List.length_take]; omega) hinterval
  have hI : ∀ member : List ℕ, member.Perm (List.range' 1 member.length) → InC member →
      IsSimple member → 4 ≤ member.length → member.getD 1 0 = 1 →
      let expanded := inflate member 1 [1, 2]
      expanded.Perm (List.range' 1 (member.length + 1)) ∧ InC expanded ∧
        expanded.length = member.length + 1 ∧ expanded.getD 1 0 = 1 ∧
        ¬ IsSimple expanded ∧ (expanded.eraseIdx 2).map down = member ∧
        (∀ start count lower, 2 ≤ count → count < expanded.length →
          start + count ≤ expanded.length →
          ((expanded.drop start).take count).Perm (List.range' lower count) →
          start = 1 ∧ count = 2 ∧ lower = 1) := by
    intro member hp hc hs hl hm
    have hinside := (PopStackPrime.inflation_intervals member [1, 2] 1 hp hs hl
      (by omega) (by decide) (by decide)).1
    cases member with
    | nil => simp at hl
    | cons first rest =>
      cases rest with
      | nil => simp at hl
      | cons second tail =>
        have hsecond : second = 1 := by simpa using hm
        subst second; have hpos : ∀ entry ∈ first :: 1 :: tail, 1 ≤ entry := by
          intro entry he; exact (List.mem_range'_1.mp (hp.mem_iff.mp he)).1
        have hfirst := hpos first (by simp); have htail : ∀ entry ∈ tail, 2 ≤ entry := by
          intro entry he; have hb := hpos entry (by simp [he])
          have hn := hp.nodup_iff.mpr (List.nodup_range' _); simp only [List.nodup_cons] at hn
          have hne : entry ≠ 1 := fun hh => hn.2.1 (hh ▸ he); omega
        have hfirstNot : first ≠ 1 := hfirstExclusion _ hp hs hl
        have hshape : inflate (first :: 1 :: tail) 1 [1, 2] =
            (first + 1) :: 1 :: 2 :: tail.map Nat.succ := by
          simp [inflate, show 1 < first by omega]; intro entry he; have hh := htail entry he; omega
        have hraised := hraise (first :: 1 :: tail) hp 2 (by omega) (by simp)
        have hmap : (first :: 1 :: tail).map (fun entry => if 2 ≤ entry then entry + 1 else entry) =
            (first + 1) :: 1 :: tail.map Nat.succ := by
          simp [show 2 ≤ first by omega]; intro entry he; have hh := htail entry he; omega
        rw [hmap] at hraised; have hperm : (inflate (first :: 1 :: tail) 1 [1, 2]).Perm
            (List.range' 1 ((first :: 1 :: tail).length + 1)) := by
          rw [hshape]; exact ((List.Perm.swap 2 1 (tail.map Nat.succ)).cons (first + 1)).trans
            ((List.Perm.swap 2 (first + 1) (1 :: tail.map Nat.succ)).trans hraised)
        refine ⟨hperm, ?_, by simp [hshape], by simp [hshape], ?_, ?_, ?_⟩
        · rw [hshape]; simpa using PopStackIncreasing.increasing_minimum_inflation [first] tail
              (by intro entry he; simp at he; subst entry; omega) htail hc
        · intro hsimple; exact hsimple 1 2 1 (by decide) (by simp [hshape])
            (by simp [hshape]) (by simp [hshape, List.range'_succ])
        · rw [hshape]; simp only [List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, List.map_cons]
          have he : down (first + 1) = first := by simp [down, show first ≠ 0 by omega]
          rw [he, show down 1 = 1 by simp [down], List.map_map]; congr 2
          calc
            tail.map (down ∘ Nat.succ) = tail.map id := by
              apply List.map_congr_left; intro entry he; have hh := htail entry he; dsimp [down]
              simp [show entry ≠ 0 by omega]
            _ = tail := List.map_id _
        · intro start count lower hcount hproper hbound hi
          have hh := hinside start count lower hcount hproper hbound hi
          simp only [List.length_cons, List.length_nil] at hh; have hstart : start = 1 := by omega
          have hcount' : count = 2 := by omega
          subst start count
          have hsegment : [1, 2].Perm (List.range' lower 2) := by simpa [hshape] using hi
          have hone := List.mem_range'.mp (hsegment.mem_iff.mp (by simp : 1 ∈ [1, 2]))
          have htwo := List.mem_range'.mp (hsegment.mem_iff.mp (by simp : 2 ∈ [1, 2]))
          exact ⟨rfl, rfl, by omega⟩
  have hleft : ∀ member : List ℕ, member.Perm (List.range' 1 member.length) → InC member →
      3 ≤ member.length → member.getD 1 0 = 1 →
      (∀ start count lower, 2 ≤ count → count < member.length → start + count ≤ member.length →
        ((member.drop start).take count).Perm (List.range' lower count) →
        start = 1 ∧ count = 2 ∧ lower = 1) →
      (2 :: member.map up) ∈ simples (member.length + 1) ∧ (2 :: member.map up).getD 2 0 = 1 ∧
        ((2 :: member.map up).drop 1).map down = member := by
    intro member hp hc hl hm hi; have hpos : ∀ entry ∈ member, 1 ≤ entry := by
      intro entry he; exact (List.mem_range'_1.mp (hp.mem_iff.mp he)).1
    have hshift : member.map (fun entry => if 2 ≤ entry then entry + 1 else entry) =
        member.map up := by
      apply List.map_congr_left; intro entry he; have hh := hpos entry he
      dsimp [up]; split_ifs <;> omega
    have hperm : (2 :: member.map up).Perm (List.range' 1 (member.length + 1)) := by
      simpa only [hshift] using hraise member hp 2 (by omega) (by omega)
    refine ⟨⟨hperm, ?_, ?_⟩, ?_, ?_⟩
    · exact (PopStackLeft.prepend_two_inC member
        (hp.nodup_iff.mpr (List.nodup_range' _)) hpos hm).mpr hc
    · exact (prepend_two_decomposition member hp hl hm).1.mpr hi
    · cases member with
      | nil => simp at hl
      | cons first rest =>
        cases rest with
        | nil => simp at hl
        | cons second tail =>
          have hh : second = 1 := by simpa using hm
          simp [hh, up]
    · simpa only [List.drop_succ_cons, List.drop_zero] using hnormalize member hp
  have hB : ∀ length, 3 ≤ length →
      (B length).Perm (List.range' 1 length) ∧ InC (B length) ∧ ¬ IsSimple (B length) ∧
      ((B length).take (length - 1)).Perm (List.range' 2 (length - 1)) := by
    intro length hl; obtain ⟨hp, hd, _⟩ := ((prefix_families length (by omega)).2.2 (B length)).mpr
      (Or.inr rfl)
    have hc := (PopStackChains.two_decreasing_chains (B length)
      (hp.nodup_iff.mpr (List.nodup_range' _))).2 hd
    have ha := (((prefix_families (length - 1) (by omega)).2.2 (A (length - 1))).mpr (Or.inl rfl)).1
    have halen : (A (length - 1)).length = length - 1 := by simpa using ha.length_eq
    have hprefix : ((B length).take (length - 1)).Perm (List.range' 2 (length - 1)) := by
      have hh := ha.map Nat.succ; rw [show (List.range' 1 (length - 1)).map Nat.succ =
          List.range' 2 (length - 1) from by
            simpa only [Nat.succ_eq_add_one] using (List.range'_succ_left ..).symm] at hh
      simpa [B, show length ≠ 2 by omega, List.take_append, halen] using hh
    exact ⟨hp, hc, fun hs => hs 0 (length - 1) 2 (by omega)
      (by have hh := hp.length_eq; simp at hh; omega)
      (by have hh := hp.length_eq; simp at hh; omega) (by simpa using hprefix), hprefix⟩
  have hfirstInverse : ∀ skeleton : List ℕ,
      skeleton.Perm (List.range' 1 skeleton.length) → IsSimple skeleton →
      4 ≤ skeleton.length → inflate skeleton 0 [2, 1] ≠ B (skeleton.length + 1) ∧
        deflateFirst (inflate skeleton 0 [2, 1]) = skeleton := by
    intro skeleton hp hs hl; constructor
    · intro he
      obtain ⟨_, _, _, hprefix⟩ := hB (skeleton.length + 1) (by omega); rw [← he] at hprefix
      have hi := (PopStackPrime.inflation_intervals skeleton [2, 1] 0 hp hs hl
        (by omega) (by decide) (by decide)).1
      have hlen : (inflate skeleton 0 [2, 1]).length = skeleton.length + 1 := by
        simp [inflate]; omega
      have hh := hi 0 skeleton.length 2 (by omega) (by omega) (by omega)
        (by simpa only [Nat.add_sub_cancel, List.drop_zero] using hprefix)
      simp only [List.length_cons, List.length_nil] at hh; omega
    · cases skeleton with
      | nil => simp at hl
      | cons pivot tail =>
        let shift := fun entry : ℕ => if pivot < entry then entry + 1 else entry
        let contract := fun entry : ℕ => if pivot < entry then entry - 1 else entry
        have hshape : inflate (pivot :: tail) 0 [2, 1] =
            (pivot + 1) :: pivot :: tail.map shift := by
          simp [inflate, shift]
        rw [hshape]; change pivot :: (tail.map shift).map contract = pivot :: tail
        have hinverse : contract ∘ shift = id := by
          funext entry; dsimp [contract, shift]; split_ifs <;> omega
        rw [List.map_map, hinverse, List.map_id]
  have hsecond : ∀ predecessor : List ℕ,
      predecessor.Perm (List.range' 1 predecessor.length) → InC predecessor →
      3 ≤ predecessor.length →
      ((IsSimple predecessor ∧ predecessor.getD 1 0 ≠ 1) ∨
        (∃ skeleton : List ℕ, skeleton.Perm (List.range' 1 skeleton.length) ∧
          IsSimple skeleton ∧ InC skeleton ∧ 4 ≤ skeleton.length ∧
          skeleton.length + 1 = predecessor.length ∧
          predecessor = inflate skeleton 0 [2, 1]) ∨ predecessor = B predecessor.length) →
      insert 1 predecessor ∈ simples (predecessor.length + 1) ∧
        (insert 1 predecessor).getD 1 0 = 1 := by
    intro predecessor hp hc hl hcase
    obtain ⟨hip, hic, hil, him, hid⟩ := hinsert predecessor hp hc 1 (by omega) (by omega)
    have hd := minimum_two_decomposition (insert 1 predecessor) (by omega)
      (by simpa only [hil] using hip) hic him
    rw [hid] at hd; exact ⟨⟨hip, hic, hd.2.2.2.2.mpr hcase⟩, him⟩
  have hindex : ∀ member : List ℕ,
      member.Perm (List.range' 1 member.length) → ∀ index, index < member.length →
      (member.getD index 0 = 1 ↔ member.idxOf 1 = index) := by
    intro member hp index hi; have hn := hp.nodup_iff.mpr (List.nodup_range' _)
    constructor
    · intro he; have hh := hn.idxOf_getElem index hi
      rw [← List.getD_eq_getElem _ 0 hi, he] at hh; exact hh
    · intro he; have hmem : 1 ∈ member := hp.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
      rw [← he, List.getD_eq_getElem _ 0 (List.idxOf_lt_length_of_mem hmem), List.getElem_idxOf]
  let valid := fun member : List ℕ =>
    ∀ start ∈ List.range member.length, ∀ count ∈ List.range (member.length + 1),
      ∀ lower ∈ List.range (member.length + 1), 2 ≤ count → count < member.length →
        start + count ≤ member.length →
        ¬ ((member.drop start).take count).Perm (List.range' lower count)
  have hbounded : ∀ member : List ℕ, IsSimple member → valid member := by
    intro member hs start _ count _ lower _ hc ht hb; exact hs start count lower hc ht hb
  have hnoThree : ∀ member : List ℕ, member.Perm (List.range' 1 3) → ¬ IsSimple member := by
    intro member hp hs
    have hm : member ∈ ((List.range' 1 3).permutations'.toFinset).filter valid := by
      simp only [Finset.mem_filter, List.mem_toFinset, List.mem_permutations']
      exact ⟨hp, hbounded member hs⟩
    have hh : ((List.range' 1 3).permutations'.toFinset).filter valid = ∅ := by
      dsimp [valid]; decide
    simp [hh] at hm
  have hfour : ∀ member ∈ simples 4, member = [2, 4, 1, 3] ∨ member = [3, 1, 4, 2] := by
    intro member hm; have hp := hm.1
    have hmem : member ∈ ((List.range' 1 4).permutations'.toFinset).filter valid := by
      simp only [Finset.mem_filter, List.mem_toFinset, List.mem_permutations']
      exact ⟨hp, hbounded member hm.2.2⟩
    have hh : ((List.range' 1 4).permutations'.toFinset).filter valid =
        {[2, 4, 1, 3], [3, 1, 4, 2]} := by dsimp [valid]; decide
    simpa only [hh, Finset.mem_insert, Finset.mem_singleton] using hmem
  have hseedThird : [2, 4, 1, 3] ∈ simples 4 := by
    obtain ⟨hp, _, hc, hs⟩ := PopStackParallel.parallel_simple 2 (by omega)
    have hh : PopStackParallel.P 2 = [2, 4, 1, 3] := by decide
    exact hh ▸ ⟨hp, hc, hs⟩
  have hseedSecond : [3, 1, 4, 2] ∈ simples 4 := by
    obtain ⟨hp, hc, _⟩ := hB 3 (by omega); have hh : B 3 = [2, 3, 1] := by decide
    have hl : (B 3).length = 3 := by simpa using hp.length_eq
    have hm := hsecond (B 3) (by simpa [hl] using hp) hc (by omega) (Or.inr (Or.inr rfl))
    simpa [hh, insert] using hm.1
  have hAll : ∀ length : ℕ, 4 ≤ length →
      (∀ member : List ℕ, member ∈ simples length → member.getD 1 0 = 1 →
        (Phi length member ∈ simples length ∧ (Phi length member).getD 2 0 = 1) ∧
          undoPhi length (Phi length member) = member) ∧
      (∀ member : List ℕ, member ∈ simples length → member.getD 2 0 = 1 →
        (undoPhi length member ∈ simples length ∧ (undoPhi length member).getD 1 0 = 1) ∧
          Phi length (undoPhi length member) = member) := by
    intro length; induction length using Nat.strong_induction_on with
    | h length ih =>
      intro hl; cases length with
      | zero => omega
      | succ previous =>
        by_cases hbase : previous + 1 = 4
        · have hf : Phi (previous + 1) = fun _ => [2, 4, 1, 3] := by
            funext member; simp only [Phi, if_pos hbase]
          have hu : undoPhi (previous + 1) = fun _ => [3, 1, 4, 2] := by
            funext member; simp only [undoPhi, if_pos hbase]
          rw [hf, hu, hbase]
          constructor
          · intro member hm hmin
            rcases hfour member hm with hh | hh
            · simp [hh] at hmin
            · exact ⟨⟨hseedThird, rfl⟩, hh.symm⟩
          · intro member hm hmin
            rcases hfour member hm with hh | hh
            · exact ⟨⟨hseedSecond, rfl⟩, hh.symm⟩
            · simp [hh] at hmin
        · have hprevious : 4 ≤ previous := by omega
          have hnormal : ∀ parent : List ℕ, parent ∈ simples previous →
              parent.getD 1 0 ≠ 1 → parent.getD 2 0 ≠ 1 →
              (insert 2 parent ∈ simples (previous + 1) ∧ (insert 2 parent).getD 2 0 = 1) ∧
              Phi (previous + 1) (insert 1 parent) = insert 2 parent ∧
              undoPhi (previous + 1) (insert 2 parent) = insert 1 parent := by
            intro parent hp hm hn; obtain ⟨hperm, hC, hs⟩ := hp
            have hlen : parent.length = previous := by simpa using hperm.length_eq
            have hp' : parent.Perm (List.range' 1 parent.length) := by simpa [hlen] using hperm
            obtain ⟨htperm, htC, htlen, htmin, htdelete⟩ :=
              hinsert parent hp' hC 2 (by omega) (by omega)
            have hsdelete := (hinsert parent hp' hC 1 (by omega) (by omega)).2.2.2.2
            have hsimple : IsSimple (insert 2 parent) := by
              apply (minimum_insertion_simple parent
                (fun entry he => (List.mem_range'_1.mp (hp'.mem_iff.mp he)).1) 2
                ⟨by omega, by omega⟩)
              exact ⟨fun start count lower hc ht hb hi =>
                False.elim (hs start count lower hc ht hb hi), hm, hn⟩
            have hhead : (insert 2 parent).getD 0 0 ≠ 2 := by
              have hh := hfirstExclusion parent hp' hs (by omega)
              cases parent with
              | nil => simp at hlen; omega
              | cons first tail =>
                change first + 1 ≠ 2; have he : first ≠ 1 := by simpa using hh
                omega
            refine ⟨⟨⟨by simpa [hlen] using htperm, htC, hsimple⟩, htmin⟩, ?_, ?_⟩
            · simp only [Phi, if_neg hbase, insert, hsdelete, if_pos hs, if_neg hn]
            · simp only [undoPhi, if_neg hbase, if_neg hhead, htdelete, if_pos hs]; rfl
          have hrecursion : ∀ parent : List ℕ, parent ∈ simples previous → parent.getD 1 0 = 1 →
              (2 :: parent.map up) ∈ simples (previous + 1) ∧ (2 :: parent.map up).getD 2 0 = 1 ∧
                Phi (previous + 1) (insert 1 (Phi previous parent)) = 2 :: parent.map up ∧
                undoPhi (previous + 1) (2 :: parent.map up) = insert 1 (Phi previous parent) := by
            intro parent hp hm
            have hlen : parent.length = previous := by simpa using hp.1.length_eq
            have hp' : parent.Perm (List.range' 1 parent.length) := by simpa [hlen] using hp.1
            obtain ⟨hf, hb⟩ := ih previous (by omega) hprevious
            obtain ⟨⟨hchild, hchildMin⟩, hchildUndo⟩ := hf parent hp hm
            have hchildLen : (Phi previous parent).length = previous := by
              simpa using hchild.1.length_eq
            have hchildPerm : (Phi previous parent).Perm
                (List.range' 1 (Phi previous parent).length) := by
              simpa [hchildLen] using hchild.1
            have hdelete := (hinsert (Phi previous parent) hchildPerm hchild.2.1
              1 (by omega) (by omega)).2.2.2.2
            obtain ⟨hleftMem, hleftMin, hleftUndo⟩ := hleft parent hp' hp.2.1
              (by omega) hm (fun start count lower hc ht hbound hi =>
                False.elim (hp.2.2 start count lower hc ht hbound hi))
            dsimp only [down] at hleftUndo
            refine ⟨by simpa [hlen] using hleftMem, hleftMin, ?_, ?_⟩
            · simp only [Phi, if_neg hbase, hdelete, if_pos hchild.2.2,
                if_pos hchildMin, hchildUndo]; rfl
            · have hhead : (2 :: parent.map up).getD 0 0 = 2 := rfl
              simp only [undoPhi, if_neg hbase, if_pos hhead, hleftUndo, if_pos hp.2.2]; rfl
          have hincreased : ∀ skeleton : List ℕ, skeleton ∈ simples (previous - 1) →
              skeleton.getD 1 0 = 1 →
              (insert 1 (inflate skeleton 0 [2, 1]) ∈ simples (previous + 1) ∧
                (insert 1 (inflate skeleton 0 [2, 1])).getD 1 0 = 1) ∧
              ((2 :: (inflate skeleton 1 [1, 2]).map up) ∈ simples (previous + 1) ∧
                (2 :: (inflate skeleton 1 [1, 2]).map up).getD 2 0 = 1) ∧
              Phi (previous + 1) (insert 1 (inflate skeleton 0 [2, 1])) =
                2 :: (inflate skeleton 1 [1, 2]).map up ∧
              undoPhi (previous + 1) (2 :: (inflate skeleton 1 [1, 2]).map up) =
                insert 1 (inflate skeleton 0 [2, 1]) := by
            intro skeleton hm hmin; obtain ⟨hp, hc, hs⟩ := hm
            have hlen : skeleton.length = previous - 1 := by simpa using hp.length_eq
            have hlarge : 4 ≤ skeleton.length := by
              by_contra hh
              have he : previous - 1 = 3 := by omega
              exact hnoThree skeleton (by simpa [he] using hp) hs
            have hp' : skeleton.Perm (List.range' 1 skeleton.length) := by simpa [hlen] using hp
            obtain ⟨hfperm, hfC, hflen, hfnot⟩ := hdouble skeleton hp' hc hlarge 0 (by omega)
            have hfperm' : (inflate skeleton 0 [2, 1]).Perm
                (List.range' 1 (inflate skeleton 0 [2, 1]).length) := by
              simpa [hflen] using hfperm
            have hsource := hsecond (inflate skeleton 0 [2, 1]) hfperm' hfC
              (by omega) (Or.inr (Or.inl ⟨skeleton, hp', hs, hc, hlarge, hflen.symm, rfl⟩))
            have hdelete := (hinsert (inflate skeleton 0 [2, 1]) hfperm' hfC
              1 (by omega) (by omega)).2.2.2.2
            obtain ⟨hfnotB, hdeflate⟩ := hfirstInverse skeleton hp' hs hlarge
            have hnotB : inflate skeleton 0 [2, 1] ≠ B previous := by
              simpa only [show skeleton.length + 1 = previous by omega] using hfnotB
            obtain ⟨hip, hiC, hilen, himin, hinot, hirecover, hiintervals⟩ :=
              hI skeleton hp' hc hs hlarge hmin
            have hip' : (inflate skeleton 1 [1, 2]).Perm
                (List.range' 1 (inflate skeleton 1 [1, 2]).length) := by
              simpa [hilen] using hip
            obtain ⟨hlt, hlmin, hlrecover⟩ := hleft (inflate skeleton 1 [1, 2]) hip'
              hiC (by omega) himin hiintervals
            dsimp only [down] at hirecover hlrecover
            refine ⟨by simpa only [show (inflate skeleton 0 [2, 1]).length + 1 =
                previous + 1 by omega] using hsource,
              ⟨by simpa only [show (inflate skeleton 1 [1, 2]).length + 1 =
                previous + 1 by omega] using hlt, hlmin⟩, ?_, ?_⟩
            · simp only [Phi, if_neg hbase, hdelete, if_neg hfnot, if_neg hnotB,
                hdeflate, if_pos hmin]; rfl
            · have hhead : (2 :: (inflate skeleton 1 [1, 2]).map up).getD 0 0 = 2 := rfl
              simp only [undoPhi, if_neg hbase, if_pos hhead, hlrecover, if_neg hinot,
                hirecover]; rfl
          have hdecreased : ∀ skeleton : List ℕ, skeleton ∈ simples (previous - 1) →
              skeleton.getD 1 0 ≠ 1 →
              (insert 1 (inflate skeleton 0 [2, 1]) ∈ simples (previous + 1) ∧
                (insert 1 (inflate skeleton 0 [2, 1])).getD 1 0 = 1) ∧
              (insert 2 (inflate skeleton 1 [2, 1]) ∈ simples (previous + 1) ∧
                (insert 2 (inflate skeleton 1 [2, 1])).getD 2 0 = 1) ∧
              Phi (previous + 1) (insert 1 (inflate skeleton 0 [2, 1])) =
                insert 2 (inflate skeleton 1 [2, 1]) ∧
              undoPhi (previous + 1) (insert 2 (inflate skeleton 1 [2, 1])) =
                insert 1 (inflate skeleton 0 [2, 1]) := by
            intro skeleton hm hmin; obtain ⟨hp, hc, hs⟩ := hm
            have hlen : skeleton.length = previous - 1 := by simpa using hp.length_eq
            have hlarge : 4 ≤ skeleton.length := by
              by_contra hh
              have he : previous - 1 = 3 := by omega
              exact hnoThree skeleton (by simpa [he] using hp) hs
            have hp' : skeleton.Perm (List.range' 1 skeleton.length) := by simpa [hlen] using hp
            obtain ⟨hfperm, hfC, hflen, hfnot⟩ := hdouble skeleton hp' hc hlarge 0 (by omega)
            have hfperm' : (inflate skeleton 0 [2, 1]).Perm
                (List.range' 1 (inflate skeleton 0 [2, 1]).length) := by
              simpa [hflen] using hfperm
            have hsource := hsecond (inflate skeleton 0 [2, 1]) hfperm' hfC (by omega)
              (Or.inr (Or.inl ⟨skeleton, hp', hs, hc, hlarge, hflen.symm, rfl⟩))
            have hdelete := (hinsert (inflate skeleton 0 [2, 1]) hfperm' hfC
              1 (by omega) (by omega)).2.2.2.2
            obtain ⟨hfnotB, hdeflate⟩ := hfirstInverse skeleton hp' hs hlarge
            have hnotB : inflate skeleton 0 [2, 1] ≠ B previous := by
              simpa only [show skeleton.length + 1 = previous by omega] using hfnotB
            obtain ⟨htperm, htC, htlen, htnot⟩ := hdouble skeleton hp' hc hlarge 1 (by omega)
            have htperm' : (inflate skeleton 1 [2, 1]).Perm
                (List.range' 1 (inflate skeleton 1 [2, 1]).length) := by
              simpa [htlen] using htperm
            obtain ⟨htip, htiC, htilen, htimin, htidelete⟩ :=
              hinsert (inflate skeleton 1 [2, 1]) htperm' htC 2 (by omega) (by omega)
            have hinside := (PopStackPrime.inflation_intervals skeleton [2, 1] 1 hp'
              hs hlarge (by omega) (by decide) (by decide)).1
            have hnotR : inflate skeleton 1 [2, 1] ≠ R previous := by
              intro he; obtain ⟨hrp, hrC, hrlen, hrmin, hrintervals, _⟩ :=
                terminal_family_intervals previous hprevious
              have hi := (hrintervals 0 (previous - 1) 2 (by omega) (by omega)
                (by omega)).mpr (Or.inl ⟨rfl, rfl, rfl⟩)
              rw [← he] at hi
              have hh := hinside 0 (previous - 1) 2 (by omega) (by omega) (by omega) hi; omega
            have hfirstNot := hfirstExclusion skeleton hp' hs hlarge
            cases skeleton with
            | nil => simp at hlarge
            | cons first rest =>
              cases rest with
              | nil => simp at hlarge
              | cons pivot tail =>
                have hb := List.mem_range'_1.mp (hp'.mem_iff.mp
                  (by simp : pivot ∈ first :: pivot :: tail))
                have hpivot : 2 ≤ pivot := by
                  have hh : pivot ≠ 1 := by simpa using hmin
                  omega
                let shift := fun entry : ℕ => if pivot < entry then entry + 1 else entry
                let contract := fun entry : ℕ => if pivot < entry then entry - 1 else entry
                have hshape : inflate (first :: pivot :: tail) 1 [2, 1] =
                    shift first :: (pivot + 1) :: pivot :: tail.map shift := by
                  simp [inflate, shift]
                have hsimple : IsSimple (insert 2 (inflate (first :: pivot :: tail) 1 [2, 1])) := by
                  apply (minimum_insertion_simple _
                    (fun entry he => (List.mem_range'_1.mp (htperm'.mem_iff.mp he)).1)
                    2 ⟨by omega, by omega⟩)
                  refine ⟨?_, by simp [hshape]; omega, by simp [hshape]; omega⟩
                  intro start count lower hcount hproper hbound hi
                  have hh := hinside start count lower hcount hproper hbound hi
                  simp only [List.length_cons, List.length_nil] at hh
                  have hstart : start = 1 := by omega
                  have hcount' : count = 2 := by omega
                  subst start count; have hseg : [pivot + 1, pivot].Perm (List.range' lower 2) := by
                    simpa [hshape] using hi
                  have hlower : lower ∈ [pivot + 1, pivot] :=
                    hseg.mem_iff.mpr (List.mem_range'_1.mpr ⟨le_rfl, by omega⟩)
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlower
                  exact ⟨by omega, by omega, by rcases hlower with he | he <;> omega⟩
                have hhead : (insert 2 (inflate (first :: pivot :: tail) 1 [2, 1])).getD
                    0 0 ≠ 2 := by
                  have hh : first ≠ 1 := by simpa using hfirstNot
                  have hpos := (List.mem_range'_1.mp (hp'.mem_iff.mp
                    (by simp : first ∈ first :: pivot :: tail))).1
                  simp only [insert, hshape, List.map_cons]; change shift first + 1 ≠ 2
                  dsimp [shift]; split_ifs <;> omega
                have hrecover : ((inflate (first :: pivot :: tail) 1 [2, 1]).eraseIdx 1).map
                    (fun entry => if (inflate (first :: pivot :: tail) 1 [2, 1]).getD 2 0 <
                      entry then entry - 1 else entry) = first :: pivot :: tail := by
                  rw [hshape]; change contract (shift first) :: contract pivot ::
                    (tail.map shift).map contract = first :: pivot :: tail
                  have hinverse : ∀ entry, contract (shift entry) = entry := by
                    intro entry; dsimp [contract, shift]
                    split_ifs <;> omega
                  rw [hinverse, show contract pivot = pivot by simp [contract], List.map_map]
                  congr 2
                  calc
                    tail.map (contract ∘ shift) = tail.map id := by
                      apply List.map_congr_left; intro entry _; exact hinverse entry
                    _ = tail := List.map_id _
                refine ⟨by simpa only [show (inflate (first :: pivot :: tail) 0 [2, 1]).length
                    + 1 = previous + 1 by omega] using hsource,
                  ⟨⟨by simpa only [show (inflate (first :: pivot :: tail) 1 [2, 1]).length
                    + 1 = previous + 1 by omega] using htip, htiC, hsimple⟩, htimin⟩, ?_, ?_⟩
                · simp only [Phi, if_neg hbase, hdelete, if_neg hfnot, if_neg hnotB,
                    hdeflate, if_neg hmin]; rfl
                · simp only [undoPhi, if_neg hbase, if_neg hhead, htidelete,
                    if_neg htnot, if_neg hnotR, hrecover]; rfl
          have hterminal : (insert 1 (B previous) ∈ simples (previous + 1) ∧
                (insert 1 (B previous)).getD 1 0 = 1) ∧
              (Y (previous + 1) ∈ simples (previous + 1) ∧ (Y (previous + 1)).getD 2 0 = 1) ∧
              Phi (previous + 1) (insert 1 (B previous)) = Y (previous + 1) ∧
              undoPhi (previous + 1) (Y (previous + 1)) = insert 1 (B previous) := by
            obtain ⟨hbp, hbC, hbnot, _⟩ := hB previous (by omega)
            have hblen : (B previous).length = previous := by simpa using hbp.length_eq
            have hbp' : (B previous).Perm (List.range' 1 (B previous).length) := by
              simpa [hblen] using hbp
            have hbsource := hsecond (B previous) hbp' hbC (by omega)
              (Or.inr (Or.inr (by simp only [hblen])))
            have hbdelete := (hinsert (B previous) hbp' hbC 1 (by omega) (by omega)).2.2.2.2
            obtain ⟨hrp, hrC, hrlen, hrmin, hrintervals, hy⟩ :=
              terminal_family_intervals previous hprevious
            have hrp' : (R previous).Perm (List.range' 1 (R previous).length) := by
              simpa [hrlen] using hrp
            have hrprefix := (hrintervals 0 (previous - 1) 2 (by omega) (by omega)
              (by omega)).mpr (Or.inl ⟨rfl, rfl, rfl⟩)
            have hrnot : ¬ IsSimple (R previous) := fun hs =>
              hs 0 (previous - 1) 2 (by omega) (by omega) (by omega) (by simpa using hrprefix)
            have hYeq : Y (previous + 1) = insert 2 (R previous) := by
              simp only [Y, Nat.add_sub_cancel, insert]
            obtain ⟨_, _, _, hymin, hydelete⟩ :=
              hinsert (R previous) hrp' hrC 2 (by omega) (by omega)
            have hrhead : (R previous).getD 0 0 ≠ 1 := by
              intro he; have hh := (List.getD_inj (by omega : 0 < (R previous).length)
                (by omega : previous - 1 < (R previous).length)
                (hrp.nodup_iff.mpr (List.nodup_range' _))).mp (he.trans hrmin.symm)
              omega
            have hyhead : (Y (previous + 1)).getD 0 0 ≠ 2 := by
              cases hshape : R previous with
              | nil => simp [hshape] at hrlen; omega
              | cons first tail =>
                have hh : first ≠ 1 := by simpa [hshape] using hrhead
                rw [hYeq]; dsimp only [insert]; rw [hshape]; change first + 1 ≠ 2; omega
            refine ⟨by simpa only [hblen] using hbsource,
              ⟨hy, by simpa only [← hYeq] using hymin⟩, ?_, ?_⟩
            · simp only [Phi, if_neg hbase, hbdelete, if_neg hbnot, if_true]
            · rw [hYeq]; simp only [undoPhi, if_neg hbase, if_neg (hYeq ▸ hyhead), hydelete,
                if_neg hrnot, if_true]; rfl
          have hforward : ∀ member ∈ simples (previous + 1), member.getD 1 0 = 1 →
              (Phi (previous + 1) member ∈ simples (previous + 1) ∧
                (Phi (previous + 1) member).getD 2 0 = 1) ∧
              undoPhi (previous + 1) (Phi (previous + 1) member) = member := by
            intro member hm hmin
            have hlen : member.length = previous + 1 := by simpa using hm.1.length_eq
            obtain ⟨hp, hc, hlpre, hrestore, hcases⟩ := minimum_two_decomposition member
              (by omega) (by simpa [hlen] using hm.1) hm.2.1 hmin
            let predecessor := (member.eraseIdx 1).map Nat.pred
            change predecessor.Perm (List.range' 1 predecessor.length) at hp
            change InC predecessor at hc; change predecessor.length + 1 = member.length at hlpre
            change insert 1 predecessor = member at hrestore
            have hprelen : predecessor.length = previous := by omega
            rcases hcases.mp hm.2.2 with hsimple | hinflation | hskew
            · obtain ⟨hs, hn⟩ := hsimple; change IsSimple predecessor at hs
              change predecessor.getD 1 0 ≠ 1 at hn; have hpre : predecessor ∈ simples previous :=
                ⟨by simpa [hprelen] using hp, hc, hs⟩
              by_cases ht : predecessor.getD 2 0 = 1
              · obtain ⟨_, hb⟩ := ih previous (by omega) hprevious
                obtain ⟨⟨hparent, hparentMin⟩, hrecovery⟩ := hb predecessor hpre ht
                obtain ⟨himage, hminimum, hf, hu⟩ :=
                  hrecursion (undoPhi previous predecessor) hparent hparentMin
                have hinput : insert 1 (Phi previous (undoPhi previous predecessor)) = member := by
                  rw [hrecovery]; exact hrestore
                rw [← hinput, hf]; exact ⟨⟨himage, hminimum⟩, hu⟩
              · obtain ⟨htarget, hf, hu⟩ := hnormal predecessor hpre hn ht
                rw [← hrestore, hf]; exact ⟨htarget, hu⟩
            · obtain ⟨skeleton, hsp, hss, hsc, hslarge, hslen, hshape⟩ := hinflation
              change skeleton.length + 1 = predecessor.length at hslen
              change predecessor = inflate skeleton 0 [2, 1] at hshape
              have hslen' : skeleton.length = previous - 1 := by omega
              have hsMember : skeleton ∈ simples (previous - 1) :=
                ⟨by simpa [hslen'] using hsp, hsc, hss⟩
              by_cases hsmin : skeleton.getD 1 0 = 1
              · obtain ⟨_, htarget, hf, hu⟩ := hincreased skeleton hsMember hsmin
                rw [← hrestore, hshape, hf]; exact ⟨htarget, hu⟩
              · obtain ⟨_, htarget, hf, hu⟩ := hdecreased skeleton hsMember hsmin
                rw [← hrestore, hshape, hf]; exact ⟨htarget, hu⟩
            · change predecessor = B predecessor.length at hskew
              have hshape : predecessor = B previous := by simpa [hprelen] using hskew
              rw [← hrestore, hshape, hterminal.2.2.1]; exact ⟨hterminal.2.1, hterminal.2.2.2⟩
          have hbackward : ∀ member ∈ simples (previous + 1), member.getD 2 0 = 1 →
              (undoPhi (previous + 1) member ∈ simples (previous + 1) ∧
                (undoPhi (previous + 1) member).getD 1 0 = 1) ∧
              Phi (previous + 1) (undoPhi (previous + 1) member) = member := by
            intro member hm hmin
            have hlen : member.length = previous + 1 := by simpa using hm.1.length_eq
            obtain ⟨hp, hc, hlpre, hrestore, hcases⟩ :=
              (minimum_three_decomposition member (by omega)
                (by simpa [hlen] using hm.1) hmin).mp ⟨hm.2.1, hm.2.2⟩
            let predecessor := (member.eraseIdx 2).map Nat.pred
            change predecessor.Perm (List.range' 1 predecessor.length) at hp
            change InC predecessor at hc; change predecessor.length + 1 = member.length at hlpre
            change insert 2 predecessor = member at hrestore
            have hprelen : predecessor.length = previous := by omega
            rcases hcases with hsimple | hinflation | hleftParent | hleftInflation | hskew
            · obtain ⟨hs, hposition⟩ := hsimple; change IsSimple predecessor at hs
              change 3 ≤ predecessor.idxOf 1 at hposition; have hn : predecessor.getD 1 0 ≠ 1 := by
                intro he; have hh := (hindex predecessor hp 1 (by omega)).mp he; omega
              have ht : predecessor.getD 2 0 ≠ 1 := by
                intro he; have hh := (hindex predecessor hp 2 (by omega)).mp he; omega
              obtain ⟨_, hf, hu⟩ := hnormal predecessor ⟨by simpa [hprelen] using hp, hc, hs⟩ hn ht
              have hsource := hsecond predecessor hp hc (by omega) (Or.inl ⟨hs, hn⟩)
              rw [← hrestore, hu, hf]; exact ⟨by simpa [hprelen] using hsource, rfl⟩
            · obtain ⟨skeleton, hsp, hss, hsc, hslarge, hsmin, hslen, hshape⟩ := hinflation.exists
              change skeleton.length + 1 = predecessor.length at hslen
              change predecessor = inflate skeleton 1 [2, 1] at hshape
              have hslen' : skeleton.length = previous - 1 := by omega
              obtain ⟨hsource, _, hf, hu⟩ := hdecreased skeleton
                ⟨by simpa [hslen'] using hsp, hsc, hss⟩ hsmin
              rw [← hrestore, hshape, hu, hf]; exact ⟨hsource, rfl⟩
            · obtain ⟨parent, hpp, hpc, hps, hpmin, hplen, hshape⟩ := hleftParent.exists
              have hplen' : parent.length = previous := by omega
              have hparent : parent ∈ simples previous := ⟨by simpa [hplen'] using hpp, hpc, hps⟩
              obtain ⟨_, _, hf, hu⟩ := hrecursion parent hparent hpmin
              obtain ⟨hprevForward, _⟩ := ih previous (by omega) hprevious
              obtain ⟨⟨hchild, hchildMin⟩, _⟩ := hprevForward parent hparent hpmin
              have hchildLen : (Phi previous parent).length = previous := by
                simpa using hchild.1.length_eq
              have hchildPerm : (Phi previous parent).Perm
                  (List.range' 1 (Phi previous parent).length) := by
                simpa [hchildLen] using hchild.1
              have hchildNot : (Phi previous parent).getD 1 0 ≠ 1 := by
                intro he; have hs := (hindex _ hchildPerm 1 (by omega)).mp he
                have ht := (hindex _ hchildPerm 2 (by omega)).mp hchildMin; omega
              have hsource := hsecond (Phi previous parent) hchildPerm hchild.2.1
                (by omega) (Or.inl ⟨hchild.2.2, hchildNot⟩)
              rw [hshape, hu, hf]; exact ⟨by simpa [hchildLen] using hsource, rfl⟩
            · obtain ⟨skeleton, hsp, hsc, hss, hsmin, hslarge, hslen, hshape⟩ :=
                hleftInflation.exists
              have hslen' : skeleton.length = previous - 1 := by omega
              obtain ⟨hsource, _, hf, hu⟩ := hincreased skeleton
                ⟨by simpa [hslen'] using hsp, hsc, hss⟩ hsmin
              rw [hshape, hu, hf]; exact ⟨hsource, rfl⟩
            · obtain ⟨_, _, hshape⟩ := hskew; change predecessor = R predecessor.length at hshape
              have hY : member = Y (previous + 1) := by
                rw [← hrestore, hshape]; simp only [Y, Nat.add_sub_cancel, hprelen, insert]
              rw [hY, hterminal.2.2.2, hterminal.2.2.1]; exact ⟨hterminal.1, rfl⟩
          exact ⟨hforward, hbackward⟩
  obtain ⟨hforward, hbackward⟩ := hAll size hsize
  refine ⟨⟨fun member hm => (hforward member hm.1 hm.2).1, ?_, ?_⟩,
    fun member hm => (hforward member hm.1 hm.2).2,
    fun member hm => (hbackward member hm.1 hm.2).2⟩
  · intro first hf second hs he; have hh := congrArg (undoPhi size) he
    simpa only [(hforward first hf.1 hf.2).2, (hforward second hs.1 hs.2).2] using hh
  · intro member hm; exact ⟨undoPhi size member, (hbackward member hm.1 hm.2).1,
      (hbackward member hm.1 hm.2).2⟩
end D5.S3.Combinatorics.PopStack.PopStackThirdEquivalence
