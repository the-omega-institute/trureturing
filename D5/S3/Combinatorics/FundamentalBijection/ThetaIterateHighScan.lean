/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateHighScan
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateHighScan
   mirror-E: none(waiver:forced-high-run-for-first-endpoint-family)
   anchors: []
   utility: none
   digest: The first skipped high value creates a 132 in the successor word. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateFirstScan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateHighScan

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycle
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateScan

theorem high_prefix_descending (r : List ℕ) (v : ℕ)
    (hr : r.Perm (List.range' 1 r.length)) (hsize : 4 ≤ r.length)
    (hfirst : r.getD 0 0 = r.length)
    (hsecond : r.getD 1 0 = r.length - 1)
    (hpenult : r.getD (r.length - 2) 0 = 1)
    (hlast : r.getD (r.length - 1) 0 = v) (hv : 2 ≤ v)
    (hravoid : ¬ Contains [1, 3, 2] [] 3 r)
    (hbavoid : ¬ Contains [1, 3, 2] [] 3 (b r)) :
    ∀ i, i < r.length - v → r.getD i 0 = r.length - i := by
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
  have hbentry (i : ℕ) (hi : i + 1 < h) :
      (b r).getD (r.getD i 0 - 1) 0 = r.getD (i + 1) 0 + 1 := by
    have hv := hval i (by omega)
    have hri : r.idxOf (r.getD i 0) = i := by
      rw [List.getD_eq_getElem _ 0 (by omega)]
      simpa using List.get_idxOf hnd ⟨i, by omega⟩
    have hbound : r.getD i 0 - 1 < (b r).length := by
      simp only [b, List.length_map, List.length_range']
      omega
    rw [List.getD_eq_getElem _ 0 hbound]
    simp only [b, List.getElem_map, List.getElem_range'_1]
    rw [show 1 + (r.getD i 0 - 1) = r.getD i 0 by omega, hri, if_pos hi]
  have hbone : (b r).getD 0 0 = v + 1 := by
    have hedge := hbentry (h - 2) (by omega)
    rw [hpenult, show h - 2 + 1 = h - 1 by omega, hlast] at hedge
    exact hedge
  obtain ⟨cut, _, hhigh, _, hcut, _, _⟩ :=
    final_value_cut r hr hravoid v (by omega) hlast
  have hhighrun (i : ℕ) (hi : i < h - v) : v < r.getD i 0 := by
    apply hhigh
    omega
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    have hilen : i < h := by omega
    by_cases hi0 : i = 0
    · subst i
      simpa using hfirst
    by_cases hi1 : i = 1
    · subst i
      exact hsecond
    have hipos : 2 ≤ i := by omega
    let e := h - i
    have hegt : v < e := by omega
    have helt : e < h := by omega
    have htailbound (j : ℕ) (hij : i ≤ j) (hj : j < h) : r.getD j 0 ≤ e := by
      have hjval := hval j hj
      by_contra hnot
      let earlier := h - r.getD j 0
      have hearlier : earlier < i := by omega
      have hearlierlen : earlier < h := by omega
      have hearliercut : earlier < h - v := by omega
      have hmatch : r.getD earlier 0 = r.getD j 0 := by
        have heq := ih earlier hearlier hearliercut
        have hsub : h - earlier = r.getD j 0 := by omega
        exact heq.trans hsub
      have := hinj earlier j hearlierlen hj hmatch
      omega
    by_contra hnot
    have ha := hhighrun i hi
    have hali := htailbound i (le_refl _) hilen
    have halt : r.getD i 0 < e := by omega
    have hemem : e ∈ r := hr.mem_iff.mpr
      (List.mem_range'.mpr ⟨e - 1, by omega, by omega⟩)
    let k := r.idxOf e
    have hklen : k < h := List.idxOf_lt_length_of_mem hemem
    have hkval : r.getD k 0 = e := by
      rw [List.getD_eq_getElem _ 0 hklen]
      exact List.getElem_idxOf hklen
    have hik : i < k := by
      by_contra hnot
      by_cases heq : k = i
      · rw [heq] at hkval
        omega
      have hki : k < i := by omega
      have hkc : k < h - v := by omega
      have hkeq := ih k hki hkc
      omega
    let x := r.getD (k - 1) 0
    have hx := hval (k - 1) (by omega)
    have hxbound : x ≤ e := htailbound (k - 1) (by omega) (by omega)
    have hxlt : x < e := by
      have hne : x ≠ e := by
        intro heq
        have := hinj (k - 1) k (by omega) hklen (heq.trans hkval.symm)
        omega
      omega
    have hxgt : 1 < x := by
      have hne : x ≠ 1 := by
        intro heq
        have heqidx := hinj (k - 1) (h - 2) (by omega) (by omega)
          (heq.trans hpenult.symm)
        have hkfinal : k = h - 1 := by omega
        rw [hkfinal, hlast] at hkval
        omega
      omega
    have hbx : (b r).getD (x - 1) 0 = e + 1 := by
      have hedge := hbentry (k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega, hkval] at hedge
      exact hedge
    have hprev : r.getD (i - 1) 0 = e + 1 := by
      have heq := ih (i - 1) (by omega) (by omega)
      have hsub : h - (i - 1) = e + 1 := by omega
      exact heq.trans hsub
    have hbe : (b r).getD e 0 = r.getD i 0 + 1 := by
      have hedge := hbentry (i - 1) (by omega)
      rw [hprev, show e + 1 - 1 = e by omega,
        show i - 1 + 1 = i by omega] at hedge
      exact hedge
    have hblen : (b r).length = h := by simp [b, h]
    apply hbavoid
    apply (contains132_iff_indices (b r)).mpr
    refine ⟨⟨0, by omega⟩, ⟨x - 1, by omega⟩, ⟨e, by omega⟩,
      ?_, ?_, ?_, ?_⟩
    · change 0 < x - 1
      omega
    · change x - 1 < e
      omega
    · have hlt : (b r).getD 0 0 < (b r).getD e 0 := by
        rw [hbone, hbe]
        omega
      simpa only [← List.getD_eq_getElem _ 0 (by omega : 0 < (b r).length),
        ← List.getD_eq_getElem _ 0 (by omega : e < (b r).length)] using hlt
    · have hlt : (b r).getD e 0 < (b r).getD (x - 1) 0 := by
        rw [hbe, hbx]
        omega
      simpa only [← List.getD_eq_getElem _ 0 (by omega : e < (b r).length),
        ← List.getD_eq_getElem _ 0 (by omega : x - 1 < (b r).length)] using hlt

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateHighScan
