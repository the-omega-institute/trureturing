/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateScan
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateScan
   mirror-E: none(waiver:final-value-scan-for-iterated-theta)
   anchors: []
   utility: none
   digest: Final-value scanning cuts and reassembles separated 132-avoiding runs. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIteratePositionBlocks
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseBlocks
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseGeneral

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateScan

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords

/-- Scanning a 132-avoider ending in `v` finds a single boundary: all earlier
values greater than `v` precede all earlier values smaller than `v`. -/
theorem final_value_cut (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length))
    (havoid : ¬ Contains [1, 3, 2] [] 3 p)
    (v : ℕ) (hv : 1 < v)
    (hlast : p.getD (p.length - 1) 0 = v) :
    ∃ c : ℕ, c < p.length - 1 ∧
      (∀ i, i < c → v < p.getD i 0) ∧
      (∀ i, c ≤ i → i < p.length - 1 → p.getD i 0 < v) ∧
      c = p.length - v ∧
      (p.take c).Perm (List.range' (v + 1) (p.length - v)) ∧
      ((p.drop c).take (p.length - 1 - c)).Perm (List.range' 1 (v - 1)) := by
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

  let n := p.length
  have hn : 0 < n := by
    by_contra h
    have : p = [] := List.length_eq_zero_iff.mp (by omega : p.length = 0)
    simp [this] at hlast
    omega
  have hnd : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have h1mem : 1 ∈ p := hp.mem_iff.mpr
    (List.mem_range'.mpr ⟨0, by omega, by simp⟩)
  have h1idx : p.idxOf 1 < n := List.idxOf_lt_length_of_mem h1mem
  have h1val : p.getD (p.idxOf 1) 0 = 1 := by
    rw [List.getD_eq_getElem _ 0 h1idx]
    exact List.getElem_idxOf h1idx
  have h1before : p.idxOf 1 < n - 1 := by
    by_contra h
    have heq : p.idxOf 1 = n - 1 := by omega
    rw [heq, hlast] at h1val
    omega
  have hex : ∃ i : ℕ, i < n - 1 ∧ p.getD i 0 < v :=
    ⟨p.idxOf 1, h1before, by omega⟩
  let c := Nat.find hex
  have hc : c < n - 1 ∧ p.getD c 0 < v := Nat.find_spec hex
  have hhigh (i : ℕ) (hic : i < c) : v < p.getD i 0 := by
    have hin : i < n - 1 := by omega
    have hnotlow : ¬ (i < n - 1 ∧ p.getD i 0 < v) := by
      intro hi
      have hci := Nat.find_min' hex hi
      omega
    have hne : p.getD i 0 ≠ v := by
      intro heq
      have helem : p[i] = p[n - 1] := by
        simpa only [← List.getD_eq_getElem _ 0 (by omega : i < p.length),
          ← List.getD_eq_getElem _ 0 (by omega : n - 1 < p.length)]
          using heq.trans hlast.symm
      have := (hnd.getElem_inj_iff).mp helem
      omega
    omega
  have hlow (i : ℕ) (hci : c ≤ i) (hin : i < n - 1) : p.getD i 0 < v := by
    by_cases hsame : c = i
    · simpa [← hsame] using hc.2
    have hci' : c < i := by omega
    have hne : p.getD i 0 ≠ v := by
      intro heq
      have helem : p[i] = p[n - 1] := by
        simpa only [← List.getD_eq_getElem _ 0 (by omega : i < p.length),
          ← List.getD_eq_getElem _ 0 (by omega : n - 1 < p.length)]
          using heq.trans hlast.symm
      have := (hnd.getElem_inj_iff).mp helem
      omega
    by_contra hnot
    have hhigh' : v < p.getD i 0 := by omega
    apply havoid
    apply (contains132_iff_indices p).mpr
    refine ⟨⟨c, by omega⟩, ⟨i, by omega⟩, ⟨n - 1, by omega⟩,
      hci', hin, ?_, ?_⟩
    · rw [← List.getD_eq_getElem _ 0 (by omega : c < p.length),
        ← List.getD_eq_getElem _ 0 (by omega : n - 1 < p.length), hlast]
      exact hc.2
    · rw [← List.getD_eq_getElem _ 0 (by omega : n - 1 < p.length),
        ← List.getD_eq_getElem _ 0 (by omega : i < p.length), hlast]
      exact hhigh'
  have hvbound : v ≤ n := by
    have hmem : p.getD (n - 1) 0 ∈ p := by
      rw [List.getD_eq_getElem _ 0 (by omega : n - 1 < p.length)]
      exact List.getElem_mem (by omega : n - 1 < p.length)
    obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hp.mem_iff.mp hmem)
    have hav : 1 + a = v := by simpa [n] using ha.symm.trans hlast
    omega
  have hprefix : (p.take c).Perm (List.range' (v + 1) (n - v)) := by
    have htnd : (p.take c).Nodup := (List.take_sublist c p).nodup hnd
    have hrnd : (List.range' (v + 1) (n - v)).Nodup := List.nodup_range'
    apply (List.subperm_of_subset htnd ?_).antisymm
      (List.subperm_of_subset hrnd ?_)
    · intro x hx
      have hxmem : x ∈ p := List.mem_of_mem_take hx
      have hxc : p.idxOf x < c := (List.mem_take_iff_idxOf_lt hxmem).mp hx
      have hxi : p.idxOf x < n := List.idxOf_lt_length_of_mem hxmem
      have hxval : p.getD (p.idxOf x) 0 = x := by
        rw [List.getD_eq_getElem _ 0 hxi]
        exact List.getElem_idxOf hxi
      have hxhigh : v < x := by rw [← hxval]; exact hhigh _ hxc
      obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hp.mem_iff.mp hxmem)
      apply List.mem_range'.mpr
      refine ⟨x - (v + 1), by omega, ?_⟩
      omega
    · intro x hx
      obtain ⟨a, ha, hxa⟩ := List.mem_range'.mp hx
      have hxhigh : v < x := by omega
      have hxmem : x ∈ p := hp.mem_iff.mpr
        (List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩)
      have hxi : p.idxOf x < n := List.idxOf_lt_length_of_mem hxmem
      have hxval : p.getD (p.idxOf x) 0 = x := by
        rw [List.getD_eq_getElem _ 0 hxi]
        exact List.getElem_idxOf hxi
      have hxbefore : p.idxOf x < n - 1 := by
        by_contra hnot
        have heq : p.idxOf x = n - 1 := by omega
        rw [heq, hlast] at hxval
        omega
      have hxc : p.idxOf x < c := by
        by_contra hnot
        have hlow' := hlow _ (by omega : c ≤ p.idxOf x) hxbefore
        omega
      exact (List.mem_take_iff_idxOf_lt hxmem).mpr hxc
  have hsize : c = n - v := by
    have hlen := hprefix.length_eq
    simp only [List.length_take, List.length_range'] at hlen
    change min c n = n - v at hlen
    omega
  have hlowpart : ((p.drop c).take (n - 1 - c)).Perm (List.range' 1 (v - 1)) := by
    have hdnd : (p.drop c).Nodup := (List.drop_sublist c p).nodup hnd
    have htnd : ((p.drop c).take (n - 1 - c)).Nodup :=
      (List.take_sublist (n - 1 - c) (p.drop c)).nodup hdnd
    have hrnd : (List.range' 1 (v - 1)).Nodup := List.nodup_range'
    apply (List.subperm_of_subset htnd ?_).antisymm
      (List.subperm_of_subset hrnd ?_)
    · intro x hx
      obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hx
      have hjbound : c + j < n - 1 := by
        simp only [List.length_take, List.length_drop] at hj
        omega
      have hxval : p.getD (c + j) 0 = x := by
        rw [List.getD_eq_getElem _ 0 (by omega : c + j < p.length)]
        simpa only [List.getElem_take, List.getElem_drop] using hjx
      have hxlow : x < v := by
        rw [← hxval]
        exact hlow (c + j) (by omega) hjbound
      have hxmem : x ∈ p := by
        rw [← hxval, List.getD_eq_getElem _ 0 (by omega : c + j < p.length)]
        exact List.getElem_mem (by omega : c + j < p.length)
      obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hp.mem_iff.mp hxmem)
      apply List.mem_range'.mpr
      refine ⟨x - 1, by omega, by omega⟩
    · intro x hx
      obtain ⟨a, ha, hxa⟩ := List.mem_range'.mp hx
      have hxpos : 0 < x := by omega
      have hxlow : x < v := by omega
      have hxmem : x ∈ p := hp.mem_iff.mpr
        (List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩)
      have hxi : p.idxOf x < n := List.idxOf_lt_length_of_mem hxmem
      have hxval : p.getD (p.idxOf x) 0 = x := by
        rw [List.getD_eq_getElem _ 0 hxi]
        exact List.getElem_idxOf hxi
      have hxbefore : p.idxOf x < n - 1 := by
        by_contra hnot
        have heq : p.idxOf x = n - 1 := by omega
        rw [heq, hlast] at hxval
        omega
      have hxc : c ≤ p.idxOf x := by
        by_contra hnot
        have hh := hhigh _ (by omega : p.idxOf x < c)
        omega
      let j := p.idxOf x - c
      have hindex : j < ((p.drop c).take (n - 1 - c)).length := by
        simp only [List.length_take, List.length_drop]
        omega
      apply List.mem_iff_getElem.mpr
      refine ⟨j, hindex, ?_⟩
      rw [List.getElem_take, List.getElem_drop]
      have heq : c + j = p.idxOf x := by dsimp [j]; omega
      simpa only [heq, ← List.getD_eq_getElem _ 0 hxi] using hxval
  exact ⟨c, hc.1, hhigh, hlow, hsize, hprefix, hlowpart⟩

/-- Appending `v` creates a 132 exactly when an earlier increasing pair
straddles `v`; all other occurrences were already present in the prefix. -/
theorem avoids132_append_iff (w : List ℕ) (v : ℕ) :
    (¬ Contains [1, 3, 2] [] 3 (w ++ [v])) ↔
      ¬ Contains [1, 3, 2] [] 3 w ∧
      ∀ i j, i < j → j < w.length →
        ¬ (w.getD i 0 < v ∧ v < w.getD j 0) := by
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

  have hprefix (i : ℕ) (hi : i < w.length) :
      (w ++ [v]).getD i 0 = w.getD i 0 :=
    List.getD_append _ _ _ _ hi
  have hfinal : (w ++ [v]).getD w.length 0 = v := by
    rw [List.getD_append_right w [v] 0 w.length (le_refl _)]
    simp
  constructor
  · intro hwhole
    constructor
    · intro hocc
      obtain ⟨i, j, k, hij, hjk, hik, hkj⟩ :=
        (contains132_iff_indices w).mp hocc
      have hiapp : i.val < (w ++ [v]).length := by
        simp only [List.length_append, List.length_singleton]
        omega
      have hjapp : j.val < (w ++ [v]).length := by
        simp only [List.length_append, List.length_singleton]
        omega
      have hkapp : k.val < (w ++ [v]).length := by
        simp only [List.length_append, List.length_singleton]
        omega
      apply hwhole
      apply (contains132_iff_indices (w ++ [v])).mpr
      refine ⟨⟨i.val, hiapp⟩, ⟨j.val, hjapp⟩,
        ⟨k.val, hkapp⟩, hij, hjk, ?_, ?_⟩
      · have h : w.getD i.val 0 < w.getD k.val 0 := by
          simpa only [List.getD_eq_getElem _ 0 i.isLt,
            List.getD_eq_getElem _ 0 k.isLt] using hik
        have h' : (w ++ [v]).getD i.val 0 < (w ++ [v]).getD k.val 0 := by
          simpa only [hprefix i.val i.isLt, hprefix k.val k.isLt] using h
        simpa only [List.getD_eq_getElem _ 0 hiapp,
          List.getD_eq_getElem _ 0 hkapp] using h'
      · have h : w.getD k.val 0 < w.getD j.val 0 := by
          simpa only [List.getD_eq_getElem _ 0 k.isLt,
            List.getD_eq_getElem _ 0 j.isLt] using hkj
        have h' : (w ++ [v]).getD k.val 0 < (w ++ [v]).getD j.val 0 := by
          simpa only [hprefix k.val k.isLt, hprefix j.val j.isLt] using h
        simpa only [List.getD_eq_getElem _ 0 hkapp,
          List.getD_eq_getElem _ 0 hjapp] using h'
    · intro i j hij hj ⟨hiv, hvj⟩
      have hi : i < w.length := by omega
      have hiapp : i < (w ++ [v]).length := by simp; omega
      have hjapp : j < (w ++ [v]).length := by simp; omega
      have hlastapp : w.length < (w ++ [v]).length := by simp
      apply hwhole
      apply (contains132_iff_indices (w ++ [v])).mpr
      refine ⟨⟨i, hiapp⟩, ⟨j, hjapp⟩, ⟨w.length, hlastapp⟩,
        hij, by omega, ?_, ?_⟩
      · have h : (w ++ [v]).getD i 0 < (w ++ [v]).getD w.length 0 := by
          rw [hprefix i hi, hfinal]
          exact hiv
        simpa only [List.getD_eq_getElem _ 0 hiapp,
          List.getD_eq_getElem _ 0 hlastapp] using h
      · have h : (w ++ [v]).getD w.length 0 < (w ++ [v]).getD j 0 := by
          rw [hprefix j hj, hfinal]
          exact hvj
        simpa only [List.getD_eq_getElem _ 0 hlastapp,
          List.getD_eq_getElem _ 0 hjapp] using h
  · rintro ⟨hcore, hcut⟩ hocc
    obtain ⟨i, j, k, hij, hjk, hik, hkj⟩ :=
      (contains132_iff_indices (w ++ [v])).mp hocc
    have hkbound : k.val < w.length + 1 := by simpa using k.isLt
    have hi : i.val < w.length := by omega
    by_cases hk : k.val = w.length
    · have hj' : j.val < w.length := by omega
      have hkval : (w ++ [v]).getD k.val 0 = v := by simpa only [hk] using hfinal
      have hik' : (w ++ [v]).getD i.val 0 < (w ++ [v]).getD k.val 0 := by
        simpa only [List.getD_eq_getElem _ 0 i.isLt,
          List.getD_eq_getElem _ 0 k.isLt] using hik
      rw [hprefix i.val hi, hkval] at hik'
      have hkj' : (w ++ [v]).getD k.val 0 < (w ++ [v]).getD j.val 0 := by
        simpa only [List.getD_eq_getElem _ 0 k.isLt,
          List.getD_eq_getElem _ 0 j.isLt] using hkj
      rw [hkval, hprefix j.val hj'] at hkj'
      exact (hcut i.val j.val hij hj') ⟨hik', hkj'⟩
    · have hk' : k.val < w.length := by omega
      have hj' : j.val < w.length := by omega
      apply hcore
      apply (contains132_iff_indices w).mpr
      refine ⟨⟨i.val, hi⟩, ⟨j.val, hj'⟩, ⟨k.val, hk'⟩, hij, hjk, ?_, ?_⟩
      · have h : (w ++ [v]).getD i.val 0 < (w ++ [v]).getD k.val 0 := by
          simpa only [List.getD_eq_getElem _ 0 i.isLt,
            List.getD_eq_getElem _ 0 k.isLt] using hik
        have h' : w.getD i.val 0 < w.getD k.val 0 := by
          simpa only [hprefix i.val hi, hprefix k.val hk'] using h
        simpa only [List.getD_eq_getElem _ 0 hi,
          List.getD_eq_getElem _ 0 hk'] using h'
      · have h : (w ++ [v]).getD k.val 0 < (w ++ [v]).getD j.val 0 := by
          simpa only [List.getD_eq_getElem _ 0 k.isLt,
            List.getD_eq_getElem _ 0 j.isLt] using hkj
        have h' : w.getD k.val 0 < w.getD j.val 0 := by
          simpa only [hprefix k.val hk', hprefix j.val hj'] using h
        simpa only [List.getD_eq_getElem _ 0 hk',
          List.getD_eq_getElem _ 0 hj'] using h'

/-- A leading value larger than every later letter cannot participate in a
132. The remaining final letter contributes exactly the straddling pairs. -/
theorem avoids132_cons_max_append_iff (w : List ℕ) (v top : ℕ)
    (htop : ∀ x ∈ w ++ [v], x < top) :
    (¬ Contains [1, 3, 2] [] 3 (top :: (w ++ [v]))) ↔
      ¬ Contains [1, 3, 2] [] 3 w ∧
      ∀ i j, i < j → j < w.length →
        ¬ (w.getD i 0 < v ∧ v < w.getD j 0) := by
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

  let tail := w ++ [v]
  have hshift (m : ℕ) (hm : 0 < m) :
      (top :: tail).getD m 0 = tail.getD (m - 1) 0 := by
    cases m with
    | zero => omega
    | succ t => simp
  have hcons : (¬ Contains [1, 3, 2] [] 3 (top :: tail)) ↔
      ¬ Contains [1, 3, 2] [] 3 tail := by
    constructor
    · intro hwhole hocc
      obtain ⟨i, j, k, hij, hjk, hik, hkj⟩ :=
        (contains132_iff_indices tail).mp hocc
      apply hwhole
      apply (contains132_iff_indices (top :: tail)).mpr
      refine ⟨⟨i.val + 1, by simp⟩,
        ⟨j.val + 1, by simp⟩,
        ⟨k.val + 1, by simp⟩, ?_, ?_, ?_, ?_⟩
      · change i.val + 1 < j.val + 1
        omega
      · change j.val + 1 < k.val + 1
        omega
      · simpa using hik
      · simpa using hkj
    · intro htail hocc
      obtain ⟨i, j, k, hij, hjk, hik, hkj⟩ :=
        (contains132_iff_indices (top :: tail)).mp hocc
      have hilen : i.val < tail.length + 1 := by simpa using i.isLt
      have hjlen : j.val < tail.length + 1 := by simpa using j.isLt
      have hklen : k.val < tail.length + 1 := by simpa using k.isLt
      by_cases hi0 : i.val = 0
      · have hkpos : 0 < k.val := by omega
        have hktail : k.val - 1 < tail.length := by omega
        have hkmem : tail.getD (k.val - 1) 0 ∈ tail := by
          rw [List.getD_eq_getElem _ 0 hktail]
          exact List.getElem_mem hktail
        have htopk : tail.getD (k.val - 1) 0 < top := htop _ (by simpa [tail] using hkmem)
        have hzero : (top :: tail)[i.val] = top := by simp [hi0]
        have hkval : (top :: tail)[k.val] = tail.getD (k.val - 1) 0 := by
          rw [← List.getD_eq_getElem _ 0 k.isLt]
          exact hshift _ hkpos
        rw [hzero, hkval] at hik
        omega
      · have hipos : 0 < i.val := by omega
        have hjpos : 0 < j.val := by omega
        have hkpos : 0 < k.val := by omega
        have hitail : i.val - 1 < tail.length := by omega
        have hjtail : j.val - 1 < tail.length := by omega
        have hktail : k.val - 1 < tail.length := by omega
        apply htail
        apply (contains132_iff_indices tail).mpr
        refine ⟨⟨i.val - 1, hitail⟩, ⟨j.val - 1, hjtail⟩,
          ⟨k.val - 1, hktail⟩, ?_, ?_, ?_, ?_⟩
        · change i.val - 1 < j.val - 1
          omega
        · change j.val - 1 < k.val - 1
          omega
        · have h : tail.getD (i.val - 1) 0 < tail.getD (k.val - 1) 0 := by
            rw [← List.getD_eq_getElem _ 0 i.isLt,
              ← List.getD_eq_getElem _ 0 k.isLt] at hik
            rw [hshift _ hipos, hshift _ hkpos] at hik
            exact hik
          simpa only [List.getD_eq_getElem _ 0 hitail,
            List.getD_eq_getElem _ 0 hktail] using h
        · have h : tail.getD (k.val - 1) 0 < tail.getD (j.val - 1) 0 := by
            rw [← List.getD_eq_getElem _ 0 k.isLt,
              ← List.getD_eq_getElem _ 0 j.isLt] at hkj
            rw [hshift _ hkpos, hshift _ hjpos] at hkj
            exact hkj
          simpa only [List.getD_eq_getElem _ 0 hktail,
            List.getD_eq_getElem _ 0 hjtail] using h
  exact hcons.trans (avoids132_append_iff w v)

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateScan
