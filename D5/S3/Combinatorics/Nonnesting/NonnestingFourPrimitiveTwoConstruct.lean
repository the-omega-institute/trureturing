/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveTwoConstruct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveTwoConstruct
   mirror-E: none(waiver:row-four-two-first-primitivity)
   anchors: []
   utility: none
   digest: Preserves primitivity under the two-first prefix insertion. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwoInsert

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwoConstruct

open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicCuts
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwoInsert

theorem two_insert_primitive (r : List ℕ) (m : ℕ)
    (hv : (1 :: r) ∈ NonnestingDefs.avoiders m
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
    (hprimitive : primitive (1 :: r) m) :
    primitive (2 :: 1 :: 3 :: 2 :: 1 :: shift 2 r) (m + 2) := by
  have valueCut_separates_positions (w : List ℕ) (k x y : ℕ)
      (hcut : valueCut w k) (hcount : w.count x = 2)
      (hx : x ≤ k) (hy : k < y) :
      secondPos x w < (w).idxOf y := by
    obtain ⟨u, v, heq, _, hu, hv⟩ := hcut
    have hxNot : x ∉ v := by
      intro h
      have := hv x h
      omega
    have hyNot : y ∉ u := by
      intro h
      have := (hu y h).2
      omega
    have hcountU : u.count x = 2 := by
      rw [heq, List.count_append] at hcount
      have hvzero : v.count x = 0 := List.count_eq_zero_of_not_mem hxNot
      omega
    obtain ⟨a, b, c, ha, hb, _, hueq⟩ :=
      count_two_decomposition x u hcountU
    have hs : secondPos x w = a.length + 1 + b.length := by
      rw [heq, hueq]
      have hdrop : a.drop (a.length + 1) = [] := by
        apply List.drop_eq_nil_iff.mpr
        omega
      simp [secondPos, List.idxOf_append, ha, hb,
        List.drop_append, hdrop, List.append_assoc]
    have hf : (w).idxOf y = u.length + v.idxOf y := by
      rw [heq]
      exact List.idxOf_append_of_notMem hyNot
    rw [hs, hf, hueq]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  let v := 1 :: r
  let w := 2 :: 1 :: 3 :: 2 :: 1 :: shift 2 r
  have hw := two_insert r m hv
  have hpositive : ∀ x ∈ r, 1 ≤ x := by
    intro x hx
    have hxbase := hv.1.mem_iff.mp (by simp [v, hx] : x ∈ v)
    obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hxbase
    have heq : x = i := by simpa using hxi
    subst x
    rw [List.mem_range'_1] at hi
    omega
  have hshiftPos : ∀ x ∈ shift 2 r, 3 ≤ x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have := hpositive y hy
    omega
  have hcount1 : w.count 1 = 2 := by
    apply doubled_count (m + 2) 1 w hw.1
    rw [List.mem_range'_1]
    omega
  have hcount2 : w.count 2 = 2 := by
    apply doubled_count (m + 2) 2 w hw.1
    rw [List.mem_range'_1]
    omega
  have hfirst2 : (w).idxOf 2 = 0 := by simp [w]
  have hfirst3 : (w).idxOf 3 = 2 := by simp [w]
  have hsecond1 : secondPos 1 w = 4 := by simp [w, secondPos]
  have hsecond2 : secondPos 2 w = 3 := by simp [w, secondPos]
  intro k hk hkn hcut
  by_cases hk1 : k = 1
  · subst k
    have hsep := valueCut_separates_positions w 1 1 2 hcut
      hcount1 (by omega) (by omega)
    rw [hsecond1, hfirst2] at hsep
    omega
  by_cases hk2 : k = 2
  · subst k
    have hsep := valueCut_separates_positions w 2 2 3 hcut
      hcount2 (by omega) (by omega)
    rw [hsecond2, hfirst3] at hsep
    omega
  have hk3 : 3 ≤ k := by omega
  obtain ⟨u, t, heq, hulength, hu, ht⟩ := hcut
  change w = u ++ t at heq
  have hu5 : 5 ≤ u.length := by omega
  have htake : u.take 5 = [2, 1, 3, 2, 1] := by
    have htakeW : w.take 5 = [2, 1, 3, 2, 1] := by simp [w]
    rw [heq] at htakeW
    simpa [List.take_append, hu5] using htakeW
  have huprefix : u = [2, 1, 3, 2, 1] ++ u.drop 5 := by
    calc
      u = u.take 5 ++ u.drop 5 := (List.take_append_drop 5 u).symm
      _ = [2, 1, 3, 2, 1] ++ u.drop 5 := by rw [htake]
  have hrEq : shift 2 r = u.drop 5 ++ t := by
    have hwEq : [2, 1, 3, 2, 1] ++ shift 2 r =
        [2, 1, 3, 2, 1] ++ (u.drop 5 ++ t) := by
      calc
        [2, 1, 3, 2, 1] ++ shift 2 r = w := rfl
        _ = u ++ t := heq
        _ = ([2, 1, 3, 2, 1] ++ u.drop 5) ++ t :=
          congrArg (fun x : List ℕ => x ++ t) huprefix
        _ = [2, 1, 3, 2, 1] ++ (u.drop 5 ++ t) := by rw [List.append_assoc]
    exact (List.append_right_inj [2, 1, 3, 2, 1]).mp hwEq
  have hrestHigh : ∀ x ∈ u.drop 5, 3 ≤ x := by
    intro x hx
    have hmem : x ∈ shift 2 r := by rw [hrEq]; simp [hx]
    exact hshiftPos x hmem
  have hrRestore : (shift 2 r).map (fun x => x - 2) = r := by
    simp only [shift, List.map_map]
    calc
      r.map ((fun x => x - 2) ∘ (fun x => x + 2)) = r.map id := by
        apply List.map_congr_left
        intro x hx
        simp only [Function.comp_apply, id_eq]
        omega
      _ = r := List.map_id r
  have hrMap : r = (u.drop 5).map (fun x => x - 2) ++
      t.map (fun x => x - 2) := by
    rw [← hrRestore, hrEq]
    simp
  have hcutV : valueCut v (k - 2) := by
    refine ⟨1 :: (u.drop 5).map (fun x => x - 2),
      t.map (fun x => x - 2), ?_, ?_, ?_, ?_⟩
    · simp [v, hrMap]
    · have hdroplen : (u.drop 5).length = u.length - 5 := by simp
      simp at hulength ⊢
      omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        have hyu : y ∈ u := by rw [huprefix]; simp [hy]
        have hyb := hu y hyu
        have hyh := hrestHigh y hy
        omega
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have hyt := ht y hy
      omega
  exact hprimitive (k - 2) (by omega) (by omega) hcutV

#print axioms two_insert_primitive

end D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwoConstruct
