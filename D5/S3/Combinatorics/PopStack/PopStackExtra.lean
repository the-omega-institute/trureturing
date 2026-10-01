/- GID: D5/S3/Combinatorics/PopStack/PopStackExtra
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackExtra
   mirror-E: none(waiver:odd-extra-permutation-intervals)
   anchors: []
   utility: none
   digest: Appending a minimum to the alternating family gives precisely one proper interval. -/

import D5.S3.Combinatorics.PopStack.PopStackParallel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackExtra

open PopStackDefs PopStackChains PopStackParallel

def E (half : ℕ) : List ℕ := (P half).map Nat.succ ++ [1]

theorem odd_extra (half : ℕ) (hhalf : 1 ≤ half) :
    (E half).Perm (List.range' 1 (2 * half + 1)) ∧ InC (E half) ∧ ¬ IsSimple (E half) ∧
      (∀ start size lower, 2 ≤ size → size < (E half).length →
        start + size ≤ (E half).length →
        ((((E half).drop start).take size).Perm (List.range' lower size) ↔
          start = 0 ∧ size = 2 * half ∧ lower = 2)) := by
  obtain ⟨hPperm, hPD, _, hPsimple⟩ := parallel_simple half hhalf
  have hPlength : (P half).length = 2 * half := List.length_ofFn
  have hlength : (E half).length = 2 * half + 1 := by
    simp only [E, List.length_append, List.length_map, List.length_singleton, hPlength]
  have hshiftRange : ∀ lower size,
      (List.range' lower size).map Nat.succ = List.range' (lower + 1) size := by
    intro lower size
    simpa only [Nat.succ_eq_add_one] using
      (List.range'_succ_left (s := lower) (n := size)).symm
  have hprefixPerm : ((P half).map Nat.succ).Perm (List.range' 2 (2 * half)) := by
    simpa only [hshiftRange] using hPperm.map Nat.succ
  have hperm : (E half).Perm (List.range' 1 (2 * half + 1)) := by
    have hh := (hprefixPerm.append (List.Perm.refl [1])).trans List.perm_append_comm
    have hrange : [1] ++ List.range' 2 (2 * half) =
        List.range' 1 (2 * half + 1) := by rw [List.range'_succ]; rfl
    simpa only [E, hrange] using hh
  have hPnodup : (P half).Nodup := hPperm.nodup_iff.mpr (List.nodup_range' _)
  have hnodup : (E half).Nodup := hperm.nodup_iff.mpr (List.nodup_range' _)
  have hPbounds : ∀ value ∈ P half, 1 ≤ value ∧ value ≤ 2 * half := by
    intro value hvalue
    have hh := List.mem_range'_1.mp (hPperm.mem_iff.mp hvalue)
    omega
  obtain ⟨cut, hPchain⟩ := (two_decreasing_chains (P half) hPnodup).1.mp hPD
  have hchain : (E half).Pairwise (fun first second =>
      (first ≤ cut + 1 ↔ second ≤ cut + 1) → second < first) := by
    apply List.pairwise_append.mpr
    refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · apply hPchain.map
      intro first second hrel hsame
      have hsame' : first ≤ cut ↔ second ≤ cut := by omega
      have hh := hrel hsame'
      omega
    · intro first hfirst second hsecond _
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hfirst
      have hh := hPbounds old hold
      simp only [List.mem_singleton] at hsecond
      omega
  have hC : InC (E half) := (two_decreasing_chains (E half) hnodup).2
    ((two_decreasing_chains (E half) hnodup).1.mpr ⟨cut + 1, hchain⟩)
  have hprefix : ((E half).drop 0).take (2 * half) = (P half).map Nat.succ := by
    rw [List.drop_zero]
    change (((P half).map Nat.succ) ++ [1]).take (2 * half) = _
    rw [List.take_append_of_le_length (by simp only [List.length_map, hPlength]; omega)]
    exact List.take_of_length_le (by simp only [List.length_map, hPlength]; omega)
  have hnotSimple : ¬ IsSimple (E half) := by
    intro hs
    apply hs 0 (2 * half) 2 (by omega) (by omega) (by omega)
    simpa only [hprefix] using hprefixPerm
  refine ⟨hperm, hC, hnotSimple, ?_⟩
  have hget : ∀ index, index < 2 * half →
      (E half).getD index 0 = (P half).getD index 0 + 1 := by
    intro index hindex
    rw [List.getD_eq_getElem?_getD]
    change ((((P half).map Nat.succ) ++ [1])[index]?).getD 0 = _
    rw [List.getElem?_append_left (by simp only [List.length_map, hPlength]; omega),
      List.getElem?_map, List.getElem?_eq_getElem (by omega),
      List.getD_eq_getElem _ _ (by omega)]
    rfl
  have hgetLast : (E half).getD (2 * half) 0 = 1 := by
    rw [List.getD_eq_getElem?_getD]
    change ((((P half).map Nat.succ) ++ [1])[2 * half]?).getD 0 = _
    rw [List.getElem?_append_right (by simp only [List.length_map, hPlength]; omega),
      List.length_map, hPlength, Nat.sub_self]
    rfl
  have hgetFirst : (E half).getD 0 0 = half + 1 := by
    rw [hget 0 (by omega), List.getD_eq_getElem _ _ (by omega)]
    simp only [P, List.getElem_ofFn, Nat.zero_mod, ite_true, Nat.zero_div, Nat.sub_zero]
  have hgetPenultimate : (E half).getD (2 * half - 1) 0 = half + 2 := by
    rw [hget _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    simp only [P, List.getElem_ofFn]
    split_ifs <;> omega
  have hgetInjective : ∀ first second, first < (E half).length →
      second < (E half).length → (E half).getD first 0 = (E half).getD second 0 →
      first = second := by
    intro first second hfirst hsecond heq
    have hh : (⟨first, hfirst⟩ : Fin (E half).length) = ⟨second, hsecond⟩ :=
      hnodup.injective_get (by
        simpa only [List.getD_eq_getElem _ _ hfirst, List.getD_eq_getElem _ _ hsecond,
          List.get_eq_getElem] using heq)
    exact congrArg Fin.val hh
  have hsliceMem : ∀ start size, start + size ≤ (E half).length →
      ∀ value, value ∈ ((E half).drop start).take size ↔
        ∃ position, start ≤ position ∧ position < start + size ∧
          (E half).getD position 0 = value := by
    intro start size hbound value
    have hsliceLength : (((E half).drop start).take size).length = size := by
      simp only [List.length_take, List.length_drop]
      omega
    constructor
    · intro hvalue
      obtain ⟨offset, hgetValue⟩ := List.mem_iff_getElem?.mp hvalue
      have hoffset : offset < size := by
        have hh := (List.getElem?_eq_some_iff.mp hgetValue).1
        omega
      rw [List.getElem?_take_of_lt hoffset, List.getElem?_drop] at hgetValue
      refine ⟨start + offset, by omega, by omega, ?_⟩
      simp only [List.getD_eq_getElem?_getD, hgetValue, Option.getD_some]
    · rintro ⟨position, hstart, hend, hgetValue⟩
      apply List.mem_iff_getElem?.mpr
      refine ⟨position - start, ?_⟩
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
        Nat.add_sub_of_le hstart]
      rw [List.getD_eq_getElem _ _ (by omega)] at hgetValue
      rw [List.getElem?_eq_getElem (by omega), hgetValue]
  intro start size lower hsize hproper hbound
  constructor
  · intro hinterval
    by_cases hinside : start + size ≤ 2 * half
    · have hsegment : ((E half).drop start).take size =
          (((P half).drop start).take size).map Nat.succ := by
        change ((((P half).map Nat.succ ++ [1]).drop start).take size) = _
        rw [List.drop_append_of_le_length (by
          simp only [List.length_map, hPlength]; omega),
          List.take_append_of_le_length (by
            simp only [List.length_drop, List.length_map, hPlength]; omega),
          ← List.map_drop, ← List.map_take]
      have hlowerMem : lower ∈ ((E half).drop start).take size :=
        hinterval.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
      rw [hsegment] at hlowerMem
      obtain ⟨old, hold, heq⟩ := List.mem_map.mp hlowerMem
      have holdMem : old ∈ P half :=
        ((List.take_sublist size _).trans (List.drop_sublist start _)).subset hold
      have hpositive := (hPbounds old holdMem).1
      have hlower : 2 ≤ lower := by omega
      have hpredRange : ∀ bottom count, 1 ≤ bottom →
          (List.range' bottom count).map Nat.pred = List.range' (bottom - 1) count := by
        intro bottom count hbottom
        induction count generalizing bottom with
        | zero => simp
        | succ count ih =>
          simp only [List.range'_succ, List.map_cons, Nat.pred_eq_sub_one,
            ih (bottom + 1) (by omega)]
          congr 2; omega
      have holdInterval : (((P half).drop start).take size).Perm
          (List.range' (lower - 1) size) := by
        have hh := hinterval.map Nat.pred
        rw [hsegment, List.map_map, hpredRange lower size (by omega)] at hh
        simpa only [Function.comp_def, Nat.pred_succ, List.map_id_fun', id_eq] using hh
      have hfull : size = 2 * half := by
        by_contra hne
        exact hPsimple start size (lower - 1) hsize (by omega) (by omega) holdInterval
      have hstart : start = 0 := by omega
      subst start
      rw [hfull, hprefix] at hinterval
      have htwoMem : 2 ∈ (P half).map Nat.succ :=
        hprefixPerm.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
      have hlow := List.mem_range'_1.mp (hinterval.mem_iff.mp htwoMem)
      have hmin : lower ∈ List.range' lower (2 * half) :=
        List.mem_range'_1.mpr (by omega)
      have hlow' := List.mem_range'_1.mp (hprefixPerm.mem_iff.mp (hinterval.mem_iff.mpr hmin))
      exact ⟨rfl, hfull, by omega⟩
    · have hend : start + size = 2 * half + 1 := by omega
      have hlastMem : 1 ∈ ((E half).drop start).take size :=
        (hsliceMem start size hbound 1).mpr
          ⟨2 * half, by omega, by omega, hgetLast⟩
      have hpenultimateMem : half + 2 ∈ ((E half).drop start).take size :=
        (hsliceMem start size hbound (half + 2)).mpr
          ⟨2 * half - 1, by omega, by omega, hgetPenultimate⟩
      have hlow := List.mem_range'_1.mp (hinterval.mem_iff.mp hlastMem)
      have hhigh := List.mem_range'_1.mp (hinterval.mem_iff.mp hpenultimateMem)
      have hfirstMem : half + 1 ∈ ((E half).drop start).take size :=
        hinterval.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
      obtain ⟨position, hposition, hpositionEnd, hvalue⟩ :=
        (hsliceMem start size hbound (half + 1)).mp hfirstMem
      have hzero : position = 0 := hgetInjective position 0 (by omega) (by omega)
        (hvalue.trans hgetFirst.symm)
      omega
  · rintro ⟨rfl, rfl, rfl⟩
    simpa only [hprefix] using hprefixPerm

end D5.S3.Combinatorics.PopStack.PopStackExtra
