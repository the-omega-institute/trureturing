/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenNineClassicalCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenNineClassicalCount
   mirror-E: none(waiver:classical-split-counting-bijection)
   anchors: [mathlib/module/Mathlib.Data.List.Sort, mathlib/module/Mathlib.Data.List.Permutation]
   utility: none
   digest: Maximum splitting and suffix translation give the classical convolution count. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenNineAuxiliaryCount
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Permutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenNineClassicalCount

open D5.S3.Combinatorics Nonnesting FishburnClassicalDefs
open FishburnTenNineClassicalSplit FishburnTenNineAuxiliaryCount

theorem classical_count_recurrence (n : ℕ) :
    (classicalAvoiders (n + 1) [[2, 3, 1], [4, 1, 2, 3]]).ncard =
      ∑ cut ∈ Finset.range (n + 1),
        (classicalAvoiders cut [[2, 3, 1], [4, 1, 2, 3]]).ncard *
          (1 + (n - cut).choose 2) := by
  classical
  have hshift (pattern word : List ℕ) (offset : ℕ) :
      NonnestingDefs.Occurs pattern (word.map (fun value => value + offset)) ↔
        NonnestingDefs.Occurs pattern word := by
    constructor
    · rintro ⟨values, hstep, hmem, hsub, _⟩
      refine ⟨fun rank => values rank - offset, ?_, ?_, ?_, by simp⟩
      · intro rank hlo hhi
        obtain ⟨lower, _, hlower⟩ := List.mem_map.mp (hmem rank hlo (by omega))
        obtain ⟨upper, _, hupper⟩ :=
          List.mem_map.mp (hmem (rank + 1) (by omega) (by omega))
        have hlt := hstep rank hlo hhi
        change values rank - offset < values (rank + 1) - offset
        omega
      · intro rank hlo hhi
        obtain ⟨value, hm, heq⟩ := List.mem_map.mp (hmem rank hlo hhi)
        have hv : values rank - offset = value := by omega
        simpa only [hv] using hm
      · have hs := hsub.map (fun value => value - offset)
        simpa [List.map_map, Function.comp_def] using hs
    · rintro ⟨values, hstep, hmem, hsub, _⟩
      refine ⟨fun rank => values rank + offset, ?_, ?_, ?_, by simp⟩
      · intro rank hlo hhi
        exact Nat.add_lt_add_right (hstep rank hlo hhi) offset
      · intro rank hlo hhi
        exact List.mem_map_of_mem (hmem rank hlo hhi)
      · simpa [List.map_map, Function.comp_def] using
          hsub.map (fun value => value + offset)
  let Pieces := Σ cut : Fin (n + 1),
    classicalAvoiders cut.val [[2, 3, 1], [4, 1, 2, 3]] ×
      classicalAvoiders (n - cut.val) [[2, 3, 1], [1, 2, 3]]
  let assemble : Pieces → List ℕ := fun entry => entry.2.1.val ++
    (n + 1) :: entry.2.2.val.map (fun value => value + entry.1.val)
  have hvalid (entry : Pieces) : assemble entry ∈
      classicalAvoiders (n + 1) [[2, 3, 1], [4, 1, 2, 3]] := by
    let cut := entry.1.val
    let left := entry.2.1.val
    let right := entry.2.2.val.map (fun value => value + cut)
    have hcut : cut ≤ n := by have hb := entry.1.is_lt; dsimp [cut]; omega
    have hleftPerm : left.Perm (List.range' 1 cut) := entry.2.1.property.1
    have hrightPerm : right.Perm (List.range' (cut + 1) (n - cut)) := by
      have hp := entry.2.2.property.1.map (fun value => cut + value)
      rw [List.map_add_range'] at hp
      convert hp using 1
      simp [right, cut, Nat.add_comm]
    have hpartPerm : (left ++ right).Perm (List.range' 1 n) := by
      have hrange : List.range' 1 n =
          List.range' 1 cut ++ List.range' (cut + 1) (n - cut) := by
        apply List.range'_eq_append_iff.mpr
        exact ⟨cut, hcut, rfl, by simp [Nat.add_comm]⟩
      rw [hrange]
      exact hleftPerm.append hrightPerm
    have hperm : (left ++ (n + 1) :: right).Perm (List.range' 1 (n + 1)) := by
      apply List.Perm.trans List.perm_middle
      apply List.Perm.trans (hpartPerm.cons (n + 1))
      rw [List.range'_1_concat]
      simpa only [List.append_nil, Nat.add_comm] using
        (List.perm_middle : (List.range' 1 n ++ (n + 1) :: []).Perm
          ((n + 1) :: (List.range' 1 n ++ []))).symm
    have hmax (value : ℕ) (hm : value ∈ left ++ right) : value < n + 1 := by
      have hr := hpartPerm.mem_iff.mp hm
      simp only [List.mem_range'_1] at hr
      omega
    have hsep (lower : ℕ) (hlower : lower ∈ left) (upper : ℕ)
        (hupper : upper ∈ right) : lower < upper := by
      have hl := hleftPerm.mem_iff.mp hlower
      have hu := hrightPerm.mem_iff.mp hupper
      simp only [List.mem_range'_1] at hl hu
      omega
    have hright231 : ¬ NonnestingDefs.Occurs [2, 3, 1] right := by
      intro hocc
      exact entry.2.2.property.2 [2, 3, 1] (by simp)
        ((hshift [2, 3, 1] entry.2.2.val cut).mp hocc)
    have hright123 : ¬ NonnestingDefs.Occurs [1, 2, 3] right := by
      intro hocc
      exact entry.2.2.property.2 [1, 2, 3] (by simp)
        ((hshift [1, 2, 3] entry.2.2.val cut).mp hocc)
    refine ⟨hperm, ?_⟩
    intro pattern hpattern
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
    rcases hpattern with rfl | rfl
    · exact (avoids231_maxSplit_iff left right (n + 1) hmax
        (hperm.nodup_iff.mpr (List.nodup_range' 1))).mpr
        ⟨entry.2.1.property.2 [2, 3, 1] (by simp), hright231, hsep⟩
    · exact (avoids4123_maxSplit_iff left right (n + 1) hmax hsep).mpr
        ⟨entry.2.1.property.2 [4, 1, 2, 3] (by simp), hright123⟩
  have hposition (entry : Pieces) : (assemble entry).idxOf (n + 1) = entry.1.val := by
    have hnot : n + 1 ∉ entry.2.1.val := by
      intro hm
      have hr := entry.2.1.property.1.mem_iff.mp hm
      simp only [List.mem_range'_1] at hr
      have hb := entry.1.is_lt
      omega
    have hlen : entry.2.1.val.length = entry.1.val := by
      simpa using entry.2.1.property.1.length_eq
    simp [assemble, List.idxOf_append_of_notMem hnot, hlen]
  have hinjective : Function.Injective assemble := by
    intro first second heq
    have hindex := congrArg (fun word : List ℕ => word.idxOf (n + 1)) heq
    rw [hposition first, hposition second] at hindex
    rcases first with ⟨firstCut, firstLeft, firstRight⟩
    rcases second with ⟨secondCut, secondLeft, secondRight⟩
    have hcut : firstCut = secondCut := Fin.ext hindex
    subst secondCut
    have hfirstLen : firstLeft.val.length = firstCut.val := by
      simpa using firstLeft.property.1.length_eq
    have hsecondLen : secondLeft.val.length = firstCut.val := by
      simpa using secondLeft.property.1.length_eq
    have hl := congrArg (fun word : List ℕ => word.take firstCut.val) heq
    have hr := congrArg (fun word : List ℕ => word.drop (firstCut.val + 1)) heq
    dsimp [assemble] at hl hr
    simp only [List.take_append, hfirstLen, hsecondLen, Nat.sub_self,
      List.take_zero, List.append_nil] at hl
    have htakeFirst : firstLeft.val.take firstCut.val = firstLeft.val := by
      simpa only [hfirstLen] using (List.take_length (l := firstLeft.val))
    have htakeSecond : secondLeft.val.take firstCut.val = secondLeft.val := by
      simpa only [hsecondLen] using (List.take_length (l := secondLeft.val))
    rw [htakeFirst, htakeSecond] at hl
    simp only [List.drop_append, hfirstLen, hsecondLen, Nat.add_sub_cancel_left,
      List.drop_eq_nil_of_le (by omega : firstLeft.val.length ≤ firstCut.val + 1),
      List.drop_eq_nil_of_le (by omega : secondLeft.val.length ≤ firstCut.val + 1),
      List.drop_succ_cons, List.drop_zero, List.nil_append] at hr
    have hleft : firstLeft = secondLeft := Subtype.ext hl
    have hright : firstRight = secondRight := by
      apply Subtype.ext
      exact (List.map_injective_iff.mpr (fun _ _ h => Nat.add_right_cancel h)) hr
    subst secondLeft
    subst secondRight
    rfl
  have hsurjective : ∀ p ∈ classicalAvoiders (n + 1) [[2, 3, 1], [4, 1, 2, 3]],
      ∃ entry : Pieces, assemble entry = p := by
    intro p hp
    have hmaximum : n + 1 ∈ p := hp.1.mem_iff.mpr (by simp)
    obtain ⟨left, right, heq, _⟩ := List.eq_append_cons_of_mem hmaximum
    subst p
    have hnodup : (left ++ (n + 1) :: right).Nodup :=
      hp.1.nodup_iff.mpr (List.nodup_range' 1)
    have hmax (value : ℕ) (hm : value ∈ left ++ right) : value < n + 1 := by
      have hv : value ∈ left ++ (n + 1) :: right := by
        rcases List.mem_append.mp hm with hl | hr
        · exact List.mem_append_left _ hl
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
      have hb := hp.1.mem_iff.mp hv
      simp only [List.mem_range'_1] at hb
      have hne : value ≠ n + 1 := by
        intro heq
        subst value
        rcases List.mem_append.mp hm with hl | hr
        · exact (List.nodup_append.mp hnodup).2.2 (n + 1) hl (n + 1) (by simp) rfl
        · exact (List.nodup_cons.mp (List.nodup_append.mp hnodup).2.1).1 hr
      omega
    obtain ⟨hleft231, hright231, hsep⟩ :=
      (avoids231_maxSplit_iff left right (n + 1) hmax hnodup).mp
        (hp.2 [2, 3, 1] (by simp))
    obtain ⟨hleft4123, hright123⟩ :=
      (avoids4123_maxSplit_iff left right (n + 1) hmax hsep).mp
        (hp.2 [4, 1, 2, 3] (by simp))
    have hparentPerm : (left ++ right).Perm (List.range' 1 n) := by
      have hcons := List.perm_middle.symm.trans hp.1
      rw [List.range'_1_concat] at hcons
      have hm : (List.range' 1 n ++ [1 + n]).Perm ((n + 1) :: List.range' 1 n) := by
        simpa only [List.append_nil, Nat.add_comm] using
          (List.perm_middle : (List.range' 1 n ++ (n + 1) :: []).Perm
            ((n + 1) :: (List.range' 1 n ++ [])))
      exact (hcons.trans hm).cons_inv
    have hsort : (left.mergeSort (· ≤ ·) ++ right.mergeSort (· ≤ ·)).Pairwise
        (· ≤ ·) := by
      apply List.pairwise_append.mpr
      refine ⟨List.pairwise_mergeSort' (· ≤ ·) left,
        List.pairwise_mergeSort' (· ≤ ·) right, ?_⟩
      intro lower hlower upper hupper
      exact le_of_lt (hsep lower ((List.mergeSort_perm left (· ≤ ·)).mem_iff.mp hlower)
        upper ((List.mergeSort_perm right (· ≤ ·)).mem_iff.mp hupper))
    have hsorted : left.mergeSort (· ≤ ·) ++ right.mergeSort (· ≤ ·) =
        List.range' 1 n := by
      apply List.Perm.eq_of_pairwise' hsort List.pairwise_le_range'
      exact ((List.mergeSort_perm left (· ≤ ·)).append
        (List.mergeSort_perm right (· ≤ ·))).trans hparentPerm
    obtain ⟨cut, hcut, hleftSort, hrightSort⟩ :=
      List.range'_eq_append_iff.mp hsorted.symm
    have hleftPerm : left.Perm (List.range' 1 cut) := by
      rw [← hleftSort]
      exact (List.mergeSort_perm left (· ≤ ·)).symm
    have hrightPerm : right.Perm (List.range' (cut + 1) (n - cut)) := by
      simpa only [hleftSort, hrightSort, Nat.mul_one, Nat.add_comm] using
        (List.mergeSort_perm right (· ≤ ·)).symm
    let unshifted := right.map (fun value => value - cut)
    have hunshiftPerm : unshifted.Perm (List.range' 1 (n - cut)) := by
      have hmap := hrightPerm.map (fun value => value - cut)
      simpa only [List.map_sub_range' (by omega : cut ≤ cut + 1),
        Nat.add_sub_cancel_left] using hmap
    have hrightEq : unshifted.map (fun value => value + cut) = right := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id right]
      apply List.map_congr_left
      intro value hm
      have hr := hrightPerm.mem_iff.mp hm
      simp only [List.mem_range'_1] at hr
      dsimp [Function.comp_def]
      omega
    have hleftMember : left ∈ classicalAvoiders cut [[2, 3, 1], [4, 1, 2, 3]] := by
      refine ⟨hleftPerm, ?_⟩
      intro pattern hpattern
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl
      · exact hleft231
      · exact hleft4123
    have hrightMember : unshifted ∈ classicalAvoiders (n - cut)
        [[2, 3, 1], [1, 2, 3]] := by
      refine ⟨hunshiftPerm, ?_⟩
      intro pattern hpattern hocc
      have hs := (hshift pattern unshifted cut).mpr hocc
      rw [hrightEq] at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl
      · exact hright231 hs
      · exact hright123 hs
    refine ⟨⟨⟨cut, by omega⟩,
      ⟨left, hleftMember⟩, ⟨unshifted, hrightMember⟩⟩, ?_⟩
    dsimp [assemble]
    rw [hrightEq]
  let correspondence : Pieces → classicalAvoiders (n + 1)
      [[2, 3, 1], [4, 1, 2, 3]] := fun entry => ⟨assemble entry, hvalid entry⟩
  have hbijective : Function.Bijective correspondence := by
    constructor
    · intro first second heq
      exact hinjective (congrArg Subtype.val heq)
    · intro p
      obtain ⟨entry, heq⟩ := hsurjective p.val p.property
      exact ⟨entry, Subtype.ext heq⟩
  have hfinite (size : ℕ) (patterns : List (List ℕ)) :
      (classicalAvoiders size patterns).Finite := by
    apply (List.finite_toSet (List.range' 1 size).permutations).subset
    intro p hp
    exact List.mem_permutations.mpr hp.1
  let (cut : Fin (n + 1)) : Finite
      (classicalAvoiders cut.val [[2, 3, 1], [4, 1, 2, 3]]) := (hfinite _ _).to_subtype
  let (cut : Fin (n + 1)) : Finite
      (classicalAvoiders (n - cut.val) [[2, 3, 1], [1, 2, 3]]) :=
    (hfinite _ _).to_subtype
  have hcard := Nat.card_congr (Equiv.ofBijective correspondence hbijective)
  dsimp [Pieces] at hcard
  rw [Nat.card_sigma] at hcard
  rw [← hcard]
  simp only [Nat.card_prod, Nat.card_coe_set_eq, auxiliary_count]
  exact Fin.sum_univ_eq_sum_range (fun cut =>
    (classicalAvoiders cut [[2, 3, 1], [4, 1, 2, 3]]).ncard *
      (1 + (n - cut).choose 2)) (n + 1)

end D5.S3.Combinatorics.Fishburn.FishburnTenNineClassicalCount
