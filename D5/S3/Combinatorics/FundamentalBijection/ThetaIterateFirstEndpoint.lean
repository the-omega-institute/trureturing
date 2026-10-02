/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateFirstEndpoint
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateFirstEndpoint
   mirror-E: none(waiver:first-endpoint-cycle-reconstruction)
   anchors: []
   utility: none
   digest: A final one and an avoiding successor word force descending cycle order. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycle

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateFirstEndpoint

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycle
open D5.S3.Combinatorics.FundamentalBijection.ThetaIteratePosition

/-- The only first-maximum parameter ending in `1` whose successor word
avoids 132 is the descending word. -/
theorem descending_of_last_one_and_b_avoids (r : List ℕ)
    (hr : r.Perm (List.range' 1 r.length)) (hsize : 2 ≤ r.length)
    (hfirst : r.getD 0 0 = r.length)
    (hlast : r.getD (r.length - 1) 0 = 1)
    (hbavoid : ¬ Contains [1, 3, 2] [] 3 (b r)) :
    r = (List.range' 1 r.length).reverse := by
  have first_one_identity (p : List ℕ)
      (hp : p.Perm (List.range' 1 p.length))
      (havoid : ¬ Contains [1, 3, 2] [] 3 p)
      (hpos : 0 < p.length) (hfirst : p.getD 0 0 = 1) :
      p = List.range' 1 p.length := by
    have hpair : p.Pairwise (· < ·) := by
      apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij
      have hzero : i = 0 ∨ 0 < i := by omega
      rcases hzero with rfl | hzero
      · have hone : p[0] = 1 := by
          simpa only [List.getD_eq_getElem _ 0 hpos] using hfirst
        have hpositive : 1 < p[j] := by
          have hmem : p[j] ∈ p := List.getElem_mem hj
          obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hp.mem_iff.mp hmem)
          have hne : p[j] ≠ p[0] := by
            intro heq
            have hnd : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
            have := (hnd.getElem_inj_iff).mp heq
            omega
          omega
        simpa only [hone] using hpositive
      · have h := ThetaIteratePosition.suffix_after_one_increasing p hp havoid
          0 i j hzero hij hj hfirst
        simpa only [List.getD_eq_getElem _ 0 hi,
          List.getD_eq_getElem _ 0 hj] using h
    have hrange : (List.range' 1 p.length).Pairwise (· < ·) :=
      List.pairwise_lt_range' 1 (by omega)
    apply List.Pairwise.eq_of_mem_iff hpair hrange
    intro x
    exact hp.mem_iff
  let h := r.length
  have hrnd : r.Nodup := hr.nodup_iff.mpr List.nodup_range'
  have hbone : (b r).getD 0 0 = 1 := by
    have hidx1 : r.idxOf 1 = h - 1 := by
      have hval : r[h - 1] = 1 := by
        simpa only [← List.getD_eq_getElem _ 0 (by omega : h - 1 < r.length)]
          using hlast
      have hidx := (List.get_idxOf hrnd ⟨h - 1, by omega⟩)
      change r.idxOf r[h - 1] = h - 1 at hidx
      rw [hval] at hidx
      exact hidx
    have hbget : (b r).getD 0 0 =
        if r.idxOf 1 + 1 < h then r.getD (r.idxOf 1 + 1) 0 + 1 else 1 := by
      rw [List.getD_eq_getElem _ 0 (by simp [b]; omega)]
      simp [b, h]
    rw [hbget, hidx1, if_neg (by omega : ¬ h - 1 + 1 < h)]
  have hbperm := b_perm_of_first_max r hr hfirst
  have hbident : b r = List.range' 1 h := by
    have hblen : (b r).length = h := by simp [b, h]
    have hvalid : (b r).Perm (List.range' 1 (b r).length) := by
      simpa only [hblen] using hbperm
    have heq := first_one_identity (b r) hvalid hbavoid
      (by simp [b]; omega) hbone
    simpa only [hblen] using heq
  have hrange (i : ℕ) (hi : i < h) : 1 ≤ r.getD i 0 ∧ r.getD i 0 ≤ h := by
    have hm : r.getD i 0 ∈ r := by
      rw [List.getD_eq_getElem _ 0 (by simpa [h] using hi)]
      exact List.getElem_mem (by simpa [h] using hi)
    obtain ⟨j, hj, heq⟩ := List.mem_range'.mp (hr.mem_iff.mp hm)
    omega
  have hstep (i : ℕ) (hi : i + 1 < h) :
      r.getD (i + 1) 0 + 1 = r.getD i 0 := by
    let x := r.getD i 0
    have hxi : i < h := by omega
    have hxmem : x ∈ r := by
      change r.getD i 0 ∈ r
      rw [List.getD_eq_getElem _ 0 (by simpa [h] using hxi)]
      exact List.getElem_mem (by simpa [h] using hxi)
    have hidx : r.idxOf x = i := by
      change r.idxOf (r.getD i 0) = i
      rw [List.getD_eq_getElem _ 0 (by simpa [h] using hxi)]
      simpa using (List.get_idxOf hrnd ⟨i, by simpa [h] using hxi⟩)
    have hxpos : 1 ≤ x := (hrange i hxi).1
    have hxle : x ≤ h := (hrange i hxi).2
    have hbentry : (b r).getD (x - 1) 0 = x := by
      rw [hbident, List.getD_eq_getElem _ 0 (by simp; omega)]
      simp only [List.getElem_range'_1]
      omega
    have hbformula : (b r).getD (x - 1) 0 =
        r.getD (i + 1) 0 + 1 := by
      rw [List.getD_eq_getElem _ 0 (by simp [b]; omega)]
      simp only [b, List.getElem_map, List.getElem_range'_1]
      rw [show 1 + (x - 1) = x by omega, hidx,
        if_pos (by simpa [h] using hi)]
    exact hbformula.symm.trans hbentry
  have hvalue (i : ℕ) (hi : i < h) : r.getD i 0 = h - i := by
    induction i with
    | zero => simpa [h] using hfirst
    | succ i ih =>
        have hprev : i < h := by omega
        have hs := hstep i hi
        have hv := ih hprev
        omega
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    have hi : i < h := by simpa [h] using hi₁
    have hv := hvalue i hi
    rw [List.getD_eq_getElem _ 0 hi₁] at hv
    rw [List.getElem_reverse]
    simp only [List.length_range', List.getElem_range'_1]
    omega

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateFirstEndpoint
