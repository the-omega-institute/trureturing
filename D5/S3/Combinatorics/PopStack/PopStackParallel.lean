/- GID: D5/S3/Combinatorics/PopStack/PopStackParallel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackParallel
   mirror-E: none(waiver:alternating-two-chain-family)
   anchors: [mathlib/module/Mathlib.Data.List.OfFn]
   utility: none
   digest: The alternating two-chain permutations are simple members of the avoidance class. -/

import D5.S3.Combinatorics.PopStack.PopStackChains
import Mathlib.Data.List.OfFn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackParallel

open PopStackDefs PopStackChains

def P (half : ℕ) : List ℕ :=
  List.ofFn (fun index : Fin (2 * half) =>
    if index.val % 2 = 0 then half - index.val / 2 else 2 * half - index.val / 2)

theorem parallel_simple (half : ℕ) (hhalf : 1 ≤ half) :
    (P half).Perm (List.range' 1 (2 * half)) ∧
      InD (P half) ∧ InC (P half) ∧ IsSimple (P half) := by
  let entry := fun index => if index % 2 = 0 then half - index / 2
    else 2 * half - index / 2
  have hlength : (P half).length = 2 * half := List.length_ofFn
  have hget : ∀ index, index < 2 * half → (P half).getD index 0 = entry index := by
    intro index hindex
    rw [List.getD_eq_getElem _ _ (by omega)]
    simp only [P, List.getElem_ofFn, entry]
  have hbounds : ∀ index, index < 2 * half →
      1 ≤ entry index ∧ entry index ≤ 2 * half := by
    intro index hindex
    dsimp only [entry]
    split_ifs <;> omega
  have hinjective : ∀ first second, first < 2 * half → second < 2 * half →
      entry first = entry second → first = second := by
    intro first second hfirst hsecond heq
    dsimp only [entry] at heq
    split_ifs at heq <;> omega
  have hnodup : (P half).Nodup := by
    apply List.nodup_iff_injective_get.mpr
    intro first second heq
    apply Fin.ext
    apply hinjective first.val second.val (by omega) (by omega)
    rw [← hget first.val (by omega), ← hget second.val (by omega)]
    simpa only [List.getD_eq_getElem _ _ first.isLt,
      List.getD_eq_getElem _ _ second.isLt, List.get_eq_getElem] using heq
  have hmem : ∀ value, value ∈ P half ↔ 1 ≤ value ∧ value ≤ 2 * half := by
    intro value
    constructor
    · intro hvalue
      obtain ⟨index, hindex, heq⟩ := List.mem_iff_getElem.mp hvalue
      have hh := hbounds index (by omega)
      have hentry : entry index = value := by
        rw [← hget index (by omega), List.getD_eq_getElem _ _ hindex]
        exact heq
      omega
    · rintro ⟨hpositive, hupper⟩
      by_cases hlower : value ≤ half
      · have hindex : 2 * (half - value) < 2 * half := by omega
        have heq : entry (2 * (half - value)) = value := by
          dsimp only [entry]
          split_ifs <;> omega
        apply List.mem_iff_getElem.mpr
        refine ⟨2 * (half - value), by omega, ?_⟩
        rw [← List.getD_eq_getElem _ _ (by omega), hget _ hindex, heq]
      · have hindex : 2 * (2 * half - value) + 1 < 2 * half := by omega
        have heq : entry (2 * (2 * half - value) + 1) = value := by
          dsimp only [entry]
          split_ifs <;> omega
        apply List.mem_iff_getElem.mpr
        refine ⟨2 * (2 * half - value) + 1, by omega, ?_⟩
        rw [← List.getD_eq_getElem _ _ (by omega), hget _ hindex, heq]
  have hperm : (P half).Perm (List.range' 1 (2 * half)) := by
    apply List.perm_ext_iff_of_nodup hnodup (List.nodup_range' _) |>.mpr
    intro value
    rw [hmem, List.mem_range'_1]
    omega
  have hchain : (P half).Pairwise (fun first second =>
      (first ≤ half ↔ second ≤ half) → second < first) := by
    apply List.pairwise_iff_getElem.mpr
    intro first second hfirst hsecond hlt hsame
    have heqFirst : (P half)[first] = entry first := by
      rw [← List.getD_eq_getElem _ _ hfirst, hget first (by omega)]
    have heqSecond : (P half)[second] = entry second := by
      rw [← List.getD_eq_getElem _ _ hsecond, hget second (by omega)]
    rw [heqFirst, heqSecond] at hsame ⊢
    have hfirst' : first < 2 * half := by omega
    have hsecond' : second < 2 * half := by omega
    have hside : ∀ index, index < 2 * half → (entry index ≤ half ↔ index % 2 = 0) := by
      intro index hindex
      dsimp only [entry]
      split_ifs <;> omega
    rw [hside first hfirst', hside second hsecond'] at hsame
    dsimp only [entry]
    split_ifs <;> omega
  have hD : InD (P half) := (two_decreasing_chains (P half) hnodup).1.mpr ⟨half, hchain⟩
  refine ⟨hperm, hD, (two_decreasing_chains (P half) hnodup).2 hD, ?_⟩
  have hsliceMem : ∀ start size, start + size ≤ (P half).length →
      ∀ value, value ∈ ((P half).drop start).take size ↔
        ∃ position, start ≤ position ∧ position < start + size ∧
          (P half).getD position 0 = value := by
    intro start size hbound value
    have hsliceLength : (((P half).drop start).take size).length = size := by
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
  intro start size lower hsize hproper hbound hinterval
  have hstart : start < 2 * half := by omega
  have hnext : start + 1 < 2 * half := by omega
  have hfirstMem : entry start ∈ ((P half).drop start).take size :=
    (hsliceMem start size hbound _).mpr ⟨start, le_rfl, by omega, hget start hstart⟩
  have hsecondMem : entry (start + 1) ∈ ((P half).drop start).take size :=
    (hsliceMem start size hbound _).mpr
      ⟨start + 1, by omega, by omega, hget (start + 1) hnext⟩
  have hfirstBounds := List.mem_range'_1.mp (hinterval.mem_iff.mp hfirstMem)
  have hsecondBounds := List.mem_range'_1.mp (hinterval.mem_iff.mp hsecondMem)
  have hstraddles : lower ≤ half ∧ half + 1 < lower + size := by
    dsimp only [entry] at hfirstBounds hsecondBounds
    split_ifs at hfirstBounds hsecondBounds <;> omega
  have hlowMem : half ∈ ((P half).drop start).take size :=
    hinterval.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
  have hhighMem : half + 1 ∈ ((P half).drop start).take size :=
    hinterval.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
  obtain ⟨lowPosition, hlowStart, hlowEnd, hlowValue⟩ :=
    (hsliceMem start size hbound half).mp hlowMem
  obtain ⟨highPosition, hhighStart, hhighEnd, hhighValue⟩ :=
    (hsliceMem start size hbound (half + 1)).mp hhighMem
  have hzero : entry 0 = half := by simp only [entry, Nat.zero_mod, ite_true, Nat.zero_div,
    Nat.sub_zero]
  have hlast : entry (2 * half - 1) = half + 1 := by
    dsimp only [entry]
    split_ifs <;> omega
  have hlowPosition : lowPosition = 0 := by
    apply hinjective lowPosition 0 (by omega) (by omega)
    rw [← hget lowPosition (by omega), hlowValue, hzero]
  have hhighPosition : highPosition = 2 * half - 1 := by
    apply hinjective highPosition (2 * half - 1) (by omega) (by omega)
    rw [← hget highPosition (by omega), hhighValue, hlast]
  omega

end D5.S3.Combinatorics.PopStack.PopStackParallel
