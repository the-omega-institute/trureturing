/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycle
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateCycle
   mirror-E: none(waiver:explicit-cycle-family-for-iterate-counting)
   anchors: []
   utility: none
   digest: The distinguished long cycle has computable first and final one-line entries. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateScan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycle

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse

local notation "B" =>
  (fun p : List ℕ => List.map (hat p) (List.range' 1 (List.length p)))

/-- The permutation whose unique standard cycle reads `h+2,r+1,1`. -/
def P (r : List ℕ) : List ℕ :=
  B (((r.length + 2) :: r.map (· + 1)) ++ [1])

/-- Successors of the parameter entries in the defining long cycle. -/
def b (r : List ℕ) : List ℕ :=
  (List.range' 1 r.length).map (fun x =>
    if r.idxOf x + 1 < r.length then r.getD (r.idxOf x + 1) 0 + 1 else 1)

/-- When the first parameter letter is maximal, following the long cycle
permutes the remaining parameter labels rather than introducing a new one. -/
theorem b_perm_of_first_max (r : List ℕ)
    (hr : r.Perm (List.range' 1 r.length))
    (hfirst : r.getD 0 0 = r.length) :
    (b r).Perm (List.range' 1 r.length) := by
  let h := r.length
  by_cases hzero : h = 0
  · have rempty : r = [] := List.length_eq_zero_iff.mp hzero
    simp [rempty, b]
  have hpos : 0 < h := by omega
  have hrnd : r.Nodup := hr.nodup_iff.mpr List.nodup_range'
  have hrange (x : ℕ) (hx : x ∈ r) : 1 ≤ x ∧ x ≤ h := by
    obtain ⟨i, hi, heq⟩ := List.mem_range'.mp (hr.mem_iff.mp hx)
    omega
  have hmem (i : ℕ) (hi : i < h) : i + 1 ∈ r := by
    apply hr.mem_iff.mpr
    exact List.mem_range'.mpr ⟨i, hi, by omega⟩
  have hidx (x : ℕ) (hx : x ∈ r) : r.idxOf x < h :=
    List.idxOf_lt_length_of_mem hx
  have hidx_inj (x y : ℕ) (hx : x ∈ r) (hy : y ∈ r)
      (heq : r.idxOf x = r.idxOf y) : x = y := by
    have hxval : r[r.idxOf x]'(by simpa [h] using hidx x hx) = x :=
      List.getElem_idxOf (by simpa [h] using hidx x hx)
    have hyval : r[r.idxOf y]'(by simpa [h] using hidx y hy) = y :=
      List.getElem_idxOf (by simpa [h] using hidx y hy)
    have hxval' : r.getD (r.idxOf x) 0 = x := by
      simpa only [List.getD_eq_getElem _ 0 (by simpa [h] using hidx x hx)] using hxval
    have hyval' : r.getD (r.idxOf y) 0 = y := by
      simpa only [List.getD_eq_getElem _ 0 (by simpa [h] using hidx y hy)] using hyval
    rw [heq] at hxval'
    exact hxval'.symm.trans hyval'
  have hsuccessor (x : ℕ) (hx : x ∈ r)
      (hn : r.idxOf x + 1 < h) :
      1 ≤ r.getD (r.idxOf x + 1) 0 ∧
        r.getD (r.idxOf x + 1) 0 < h := by
    have hvalue : r.getD (r.idxOf x + 1) 0 ∈ r := by
      rw [List.getD_eq_getElem _ 0 hn]
      exact List.getElem_mem hn
    have hbounds := hrange _ hvalue
    have hnotmax : r.getD (r.idxOf x + 1) 0 ≠ h := by
      intro heq
      have hval : r[r.idxOf x + 1] = r[0] := by
        have heq' : r.getD (r.idxOf x + 1) 0 = r.getD 0 0 := by
          rw [heq, hfirst]
        simpa only [List.getD_eq_getElem _ 0 hn,
          List.getD_eq_getElem _ 0 (by omega : 0 < r.length)] using heq'
      have hindex := (hrnd.getElem_inj_iff).mp hval
      omega
    omega
  have hbget (i : ℕ) (hi : i < h) :
      (b r).getD i 0 =
        if r.idxOf (i + 1) + 1 < h then
          r.getD (r.idxOf (i + 1) + 1) 0 + 1 else 1 := by
    rw [List.getD_eq_getElem _ 0 (by simpa [b, h] using hi)]
    simp [b, h, Nat.add_comm]
  have hbnd : (b r).Nodup := by
    apply List.nodup_iff_injective_getElem.mpr
    intro i j hij
    have hi : i.val < h := by simpa [b, h] using i.isLt
    have hj : j.val < h := by simpa [b, h] using j.isLt
    have hxi := hmem i.val hi
    have hxj := hmem j.val hj
    have heq : (b r).getD i.val 0 = (b r).getD j.val 0 := by
      simpa only [List.getD_eq_getElem _ 0 i.isLt,
        List.getD_eq_getElem _ 0 j.isLt] using hij
    rw [hbget i.val hi, hbget j.val hj] at heq
    by_cases hni : r.idxOf (i.val + 1) + 1 < h
    · by_cases hnj : r.idxOf (j.val + 1) + 1 < h
      · rw [if_pos hni, if_pos hnj] at heq
        have hvalues : r[r.idxOf (i.val + 1) + 1] =
            r[r.idxOf (j.val + 1) + 1] := by
          have heq' : r.getD (r.idxOf (i.val + 1) + 1) 0 =
              r.getD (r.idxOf (j.val + 1) + 1) 0 := by omega
          simpa only [List.getD_eq_getElem _ 0 hni,
            List.getD_eq_getElem _ 0 hnj] using heq'
        have hindices := (hrnd.getElem_inj_iff).mp hvalues
        have hidxeq : r.idxOf (i.val + 1) = r.idxOf (j.val + 1) := by omega
        have hxy := hidx_inj _ _ hxi hxj hidxeq
        exact Fin.ext (by omega)
      · rw [if_pos hni, if_neg hnj] at heq
        have hpositive := (hsuccessor _ hxi hni).1
        omega
    · by_cases hnj : r.idxOf (j.val + 1) + 1 < h
      · rw [if_neg hni, if_pos hnj] at heq
        have hpositive := (hsuccessor _ hxj hnj).1
        omega
      · have hii := hidx _ hxi
        have hjj := hidx _ hxj
        have hidxeq : r.idxOf (i.val + 1) = r.idxOf (j.val + 1) := by omega
        have hxy := hidx_inj _ _ hxi hxj hidxeq
        exact Fin.ext (by omega)
  have hbsubset : (b r).toFinset ⊆ (List.range' 1 h).toFinset := by
    intro y hy
    obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hy)
    have hi' : i < h := by simpa [b, h] using hi
    have hyval : y = (b r).getD i 0 := by
      simpa only [List.getD_eq_getElem _ 0 hi] using hiy.symm
    rw [hyval, hbget i hi']
    by_cases hn : r.idxOf (i + 1) + 1 < h
    · rw [if_pos hn]
      have hbounds := hsuccessor _ (hmem i hi') hn
      apply List.mem_toFinset.mpr
      exact List.mem_range'.mpr
        ⟨r.getD (r.idxOf (i + 1) + 1) 0, by omega, by omega⟩
    · rw [if_neg hn]
      apply List.mem_toFinset.mpr
      exact List.mem_range'.mpr ⟨0, hpos, by simp⟩
  have hbcard : (b r).toFinset.card = (List.range' 1 h).toFinset.card := by
    have hblen : (b r).length = h := by simp [b, h]
    simp only [List.card_toFinset, List.dedup_eq_self.mpr hbnd,
      List.dedup_eq_self.mpr List.nodup_range']
    simpa using hblen
  have hbset : (b r).toFinset = (List.range' 1 h).toFinset :=
    Finset.eq_of_subset_of_card_le hbsubset (by omega)
  exact List.perm_of_nodup_nodup_toFinset_eq hbnd List.nodup_range' hbset

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycle
