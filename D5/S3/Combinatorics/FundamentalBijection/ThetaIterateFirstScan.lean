/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateFirstScan
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateFirstScan
   mirror-E: none(waiver:first-endpoint-successor-scan)
   anchors: []
   utility: none
   digest: Simultaneous avoidance forces the final pair when the second entry is small. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateFirstEndpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateFirstScan

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycle
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords
open D5.S3.Combinatorics.FundamentalBijection.ThetaIteratePosition

theorem small_second_forces_final_pair (r : List ℕ)
    (hr : r.Perm (List.range' 1 r.length)) (hsize : 4 ≤ r.length)
    (hfirst : r.getD 0 0 = r.length)
    (hsecond : 2 ≤ r.getD 1 0) (hsmall : r.getD 1 0 ≤ r.length - 2)
    (hravoid : ¬ Contains [1, 3, 2] [] 3 r)
    (hbavoid : ¬ Contains [1, 3, 2] [] 3 (b r)) :
    r.getD (r.length - 1) 0 = r.length - 1 ∧
      r.getD (r.length - 2) 0 = 1 := by
  have contains132_iff_indices (p : List ℕ) :
      Contains [1, 3, 2] [] 3 p ↔
        ∃ i j k : Fin p.length, i < j ∧ j < k ∧ p[i.val] < p[k.val] ∧
          p[k.val] < p[j.val] := by
    constructor
    · rintro ⟨x, hlt, _, hsub, _⟩
      change List.Sublist [x 1, x 3, x 2] p at hsub
      obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      have h0 : p[(f ⟨0, by simp⟩).val] = x 1 := by
        simpa using (hf ⟨0, by simp⟩).symm
      have h1 : p[(f ⟨1, by simp⟩).val] = x 3 := by
        simpa using (hf ⟨1, by simp⟩).symm
      have h2 : p[(f ⟨2, by simp⟩).val] = x 2 := by
        simpa using (hf ⟨2, by simp⟩).symm
      refine ⟨f ⟨0, by simp⟩, f ⟨1, by simp⟩, f ⟨2, by simp⟩,
        f.strictMono (by simp), f.strictMono (by simp), ?_, ?_⟩
      · simpa only [h0, h2] using hlt 1 (by omega) (by omega)
      · simpa only [h2, h1] using hlt 2 (by omega) (by omega)
    · rintro ⟨i, j, k, hij, hjk, hik, hkj⟩
      let x : ℕ → ℕ := fun t => if t = 1 then p[i.val] else if t = 2 then p[k.val]
        else p[j.val]
      have hx1 : x 1 = p[i.val] := by simp [x]
      have hx2 : x 2 = p[k.val] := by simp [x]
      have hx3 : x 3 = p[j.val] := by simp [x]
      have hsub : List.Sublist [p[i.val], p[j.val], p[k.val]] p := by
        let f : Fin 3 → Fin p.length := fun t =>
          if t.val = 0 then i else if t.val = 1 then j else k
        have hf : StrictMono f := by
          intro a b hab
          fin_cases a <;> fin_cases b <;> simp_all [f]; omega
        apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
        refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩
        intro t
        fin_cases t <;> simp [f]
      refine ⟨x, ?_, ?_, ?_, by simp⟩
      · intro t ht ht3
        have h : t = 1 ∨ t = 2 := by omega
        rcases h with rfl | rfl <;> simp [hx1, hx2, hx3, hik, hkj]
      · intro t ht ht3
        have h : t = 1 ∨ t = 2 ∨ t = 3 := by omega
        rcases h with rfl | rfl | rfl <;> simp [hx1, hx2, hx3]
      · simpa [hx1, hx2, hx3] using hsub

  let h := r.length
  let a := r.getD 1 0
  have hnd : r.Nodup := hr.nodup_iff.mpr List.nodup_range'
  have hval (i : ℕ) (hi : i < h) : 1 ≤ r.getD i 0 ∧ r.getD i 0 ≤ h := by
    have hm : r.getD i 0 ∈ r := by
      rw [List.getD_eq_getElem _ 0 hi]
      exact List.getElem_mem hi
    obtain ⟨j, hj, heq⟩ := List.mem_range'.mp (hr.mem_iff.mp hm)
    omega
  have hinj (i j : ℕ) (hi : i < h) (hj : j < h)
      (heq : r.getD i 0 = r.getD j 0) : i = j := by
    rw [List.getD_eq_getElem _ 0 hi, List.getD_eq_getElem _ 0 hj] at heq
    exact hnd.getElem_inj_iff.mp heq
  have hidx (x : ℕ) (hx : 1 ≤ x) (hxh : x ≤ h) :
      r.idxOf x < h ∧ r.getD (r.idxOf x) 0 = x := by
    have hm : x ∈ r := hr.mem_iff.mpr
      (List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩)
    have hi := List.idxOf_lt_length_of_mem hm
    exact ⟨hi, by rw [List.getD_eq_getElem _ 0 hi]; exact List.getElem_idxOf hi⟩
  have hbentry (i : ℕ) (hi : i < h) :
      (b r).getD (r.getD i 0 - 1) 0 =
        if i + 1 < h then r.getD (i + 1) 0 + 1 else 1 := by
    have hv := hval i hi
    have hri : r.idxOf (r.getD i 0) = i := by
      rw [List.getD_eq_getElem _ 0 hi]
      simpa using List.get_idxOf hnd ⟨i, hi⟩
    have hbound : r.getD i 0 - 1 < (b r).length := by
      simp only [b, List.length_map, List.length_range']
      omega
    rw [List.getD_eq_getElem _ 0 hbound]
    simp only [b, List.getElem_map, List.getElem_range'_1]
    rw [show 1 + (r.getD i 0 - 1) = r.getD i 0 by omega, hri]
  have hnoR (i j k : ℕ) (hij : i < j) (hjk : j < k) (hk : k < h)
      (hikval : r.getD i 0 < r.getD k 0)
      (hkjval : r.getD k 0 < r.getD j 0) : False := by
    apply hravoid
    apply (contains132_iff_indices r).mpr
    refine ⟨⟨i, by omega⟩, ⟨j, by omega⟩, ⟨k, hk⟩, hij, hjk, ?_, ?_⟩
    · simpa only [← List.getD_eq_getElem _ 0 (by omega : i < r.length),
        ← List.getD_eq_getElem _ 0 hk] using hikval
    · simpa only [← List.getD_eq_getElem _ 0 hk,
        ← List.getD_eq_getElem _ 0 (by omega : j < r.length)] using hkjval
  have hnoB (i j k : ℕ) (hij : i < j) (hjk : j < k) (hk : k < h)
      (hikval : (b r).getD i 0 < (b r).getD k 0)
      (hkjval : (b r).getD k 0 < (b r).getD j 0) : False := by
    have hlen : (b r).length = h := by simp [b, h]
    apply hbavoid
    apply (contains132_iff_indices (b r)).mpr
    refine ⟨⟨i, by omega⟩, ⟨j, by omega⟩, ⟨k, by omega⟩, hij, hjk, ?_, ?_⟩
    · simpa only [← List.getD_eq_getElem _ 0 (by omega : i < (b r).length),
        ← List.getD_eq_getElem _ 0 (by omega : k < (b r).length)] using hikval
    · simpa only [← List.getD_eq_getElem _ 0 (by omega : k < (b r).length),
        ← List.getD_eq_getElem _ 0 (by omega : j < (b r).length)] using hkjval
  have hbmax : (b r).getD (h - 1) 0 = a + 1 := by
    simpa only [hfirst, if_pos (by omega : 0 + 1 < h)] using hbentry 0 (by omega)
  let k := r.idxOf (h - 1)
  have hk := hidx (h - 1) (by omega) (by omega)
  have hklen : k < h := hk.1
  have hkval : r.getD k 0 = h - 1 := hk.2
  have hkpos : 1 < k := by
    by_contra hnot
    have hcases : k = 0 ∨ k = 1 := by omega
    rcases hcases with heq | heq
    · rw [heq, hfirst] at hkval
      omega
    · rw [heq] at hkval
      omega
  let u := r.idxOf 1
  have hu := hidx 1 (by omega) (by omega)
  have hulen : u < h := hu.1
  have huval : r.getD u 0 = 1 := hu.2
  have hupos : 1 < u := by
    by_contra hnot
    have hcases : u = 0 ∨ u = 1 := by omega
    rcases hcases with heq | heq
    · rw [heq, hfirst] at huval
      omega
    · rw [heq] at huval
      omega
  have hune : u ≠ k := by intro heq; rw [heq, hkval] at huval; omega
  have hklast : k = h - 1 := by
    by_contra hnot
    have hkbefore : k < h - 1 := by omega
    have hlastval := hval (h - 1) (by omega)
    have hlastsmall : r.getD (h - 1) 0 < h - 1 := by
      have hne1 : r.getD (h - 1) 0 ≠ h := by
        intro heq
        have := hinj (h - 1) 0 (by omega) (by omega) (heq.trans hfirst.symm)
        omega
      have hne2 : r.getD (h - 1) 0 ≠ h - 1 := by
        intro heq
        have := hinj (h - 1) k (by omega) hklen (heq.trans hkval.symm)
        omega
      omega
    have huku : k < u := by
      by_contra hnot
      have huk : u < k := by omega
      have hlastne : r.getD (h - 1) 0 ≠ 1 := by
        intro heq
        have := hinj (h - 1) u (by omega) hulen (heq.trans huval.symm)
        omega
      exact hnoR u k (h - 1) huk hkbefore (by omega) (by omega) (by omega)
    let x := r.getD (k - 1) 0
    have hx := hval (k - 1) (by omega)
    have hxgt : 1 < x := by
      have hne : x ≠ 1 := by
        intro heq
        have := hinj (k - 1) u (by omega) hulen (heq.trans huval.symm)
        omega
      omega
    have hxlt : x < h := by
      have hne : x ≠ h := by
        intro heq
        have := hinj (k - 1) 0 (by omega) (by omega) (heq.trans hfirst.symm)
        omega
      omega
    have hbx : (b r).getD (x - 1) 0 = h := by
      have hstep := hbentry (k - 1) (by omega)
      rw [if_pos (by omega), show k - 1 + 1 = k by omega, hkval] at hstep
      change (b r).getD (x - 1) 0 = h - 1 + 1 at hstep
      omega
    have hbone : (b r).getD 0 0 ≤ a := by
      have hstep := hbentry u hulen
      rw [huval] at hstep
      simp only [Nat.sub_self] at hstep
      by_cases hunext : u + 1 < h
      · have hbelow : r.getD (u + 1) 0 < a := by
          have hnextval := hval (u + 1) hunext
          have hnextsmall : r.getD (u + 1) 0 < h - 1 := by
            have hne1 : r.getD (u + 1) 0 ≠ h := by
              intro heq
              have := hinj (u + 1) 0 hunext (by omega) (heq.trans hfirst.symm)
              omega
            have hne2 : r.getD (u + 1) 0 ≠ h - 1 := by
              intro heq
              have := hinj (u + 1) k hunext hklen (heq.trans hkval.symm)
              omega
            omega
          have hne : r.getD (u + 1) 0 ≠ a := by
            intro heq
            have := hinj (u + 1) 1 hunext (by omega) heq
            omega
          by_contra hnot
          exact hnoR 1 k (u + 1) hkpos (by omega) hunext (by omega) (by omega)
        rw [if_pos hunext] at hstep
        omega
      · rw [if_neg hunext] at hstep
        omega
    exact hnoB 0 (x - 1) (h - 1) (by omega) (by omega) (by omega)
      (by rw [hbmax]; omega) (by rw [hbmax, hbx]; omega)
  have hlast : r.getD (h - 1) 0 = h - 1 := by simpa [hklast] using hkval
  refine ⟨hlast, ?_⟩
  change r.getD (h - 2) 0 = 1
  by_contra hnot
  let x := r.getD (h - 2) 0
  have hx := hval (h - 2) (by omega)
  have hxgt : 1 < x := by omega
  have hxlt : x < h := by
    have hne : x ≠ h := by
      intro heq
      have := hinj (h - 2) 0 (by omega) (by omega) (heq.trans hfirst.symm)
      omega
    omega
  have hufinal : u < h - 2 := by
    have hne : u ≠ h - 1 := by intro heq; rw [heq, hlast] at huval; omega
    have hne2 : u ≠ h - 2 := by intro heq; rw [heq] at huval; exact hnot huval
    omega
  let v := r.getD (u + 1) 0
  have hv := hval (u + 1) (by omega)
  have hvle : v ≤ x := by
    by_cases heq : u + 1 = h - 2
    · simp [v, x, heq]
    · have hinc := suffix_after_one_increasing r hr hravoid u (u + 1) (h - 2)
        (by omega) (by omega) (by omega) huval
      omega
  have hbx : (b r).getD (x - 1) 0 = h := by
    have hstep := hbentry (h - 2) (by omega)
    rw [if_pos (by omega), show h - 2 + 1 = h - 1 by omega, hlast] at hstep
    change (b r).getD (x - 1) 0 = h - 1 + 1 at hstep
    omega
  have hbone : (b r).getD 0 0 = v + 1 := by
    have hstep := hbentry u hulen
    rw [huval, if_pos (by omega)] at hstep
    exact hstep
  have hav : a < v := by
    have hne : v ≠ a := by
      intro heq
      have := hinj (u + 1) 1 (by omega) (by omega) heq
      omega
    by_contra hnot
    exact hnoB 0 (x - 1) (h - 1) (by omega) (by omega) (by omega)
      (by rw [hbone, hbmax]; omega) (by rw [hbmax, hbx]; omega)
  let y := r.getD (u - 1) 0
  have hy := hval (u - 1) (by omega)
  have hylt : y < v := by
    by_cases heq : u - 1 = 1
    · simpa [y, a, heq] using hav
    · have hne : y ≠ v := by
        intro heq
        have := hinj (u - 1) (u + 1) (by omega) (by omega) heq
        omega
      by_contra hnot
      exact hnoR 1 (u - 1) (u + 1) (by omega) (by omega) (by omega) hav (by omega)
  have hby : (b r).getD (y - 1) 0 = 2 := by
    have hstep := hbentry (u - 1) (by omega)
    rw [if_pos (by omega), show u - 1 + 1 = u by omega, huval] at hstep
    exact hstep
  exact hnoB (y - 1) (x - 1) (h - 1) (by omega) (by omega) (by omega)
    (by rw [hby, hbmax]; omega) (by rw [hbmax, hbx]; omega)

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateFirstScan
