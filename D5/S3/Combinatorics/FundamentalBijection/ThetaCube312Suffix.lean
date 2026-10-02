/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaCube312Suffix
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaCube312Suffix
   mirror-E: none(waiver:312-forced-suffix-adjacency)
   anchors: []
   utility: none
   digest: An upward edge and the forced tail locate the next large record. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Edge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Suffix

open D5.S3.Combinatorics.ArrowWilfDefs
open ThetaBasicInverse
open ThetaCube312Edge

set_option maxHeartbeats 1000000 in
/-- The upward edge and 312 avoidance leave no entry between `3,n-2`
and the prescribed terminal blocks. -/
theorem terminal_pair_positions (p : List ℕ) (n : ℕ)
    (hp : p.Perm (List.range' 1 n)) (hn : 7 ≤ n)
    (havoid : ¬ Contains [3, 1, 2] [] 3 p)
    (hpen : p.getD (n - 4) 0 = n - 1)
    (htwo : p.getD (n - 3) 0 = 2)
    (hmax : p.getD (n - 2) 0 = n)
    (hone : p.getD (n - 1) 0 = 1)
    (hhat : hat p 3 = n - 3) :
    p.getD (n - 6) 0 = 3 ∧ p.getD (n - 5) 0 = n - 2 := by
  have upward_hat_edge_closes_block (p : List ℕ)
      (hp : p.Perm (List.range' 1 p.length))
      (havoid : ¬ D5.S3.Combinatorics.ArrowWilfDefs.Contains [3, 1, 2] [] 3 p)
      (x : ℕ) (hx : x ∈ p) (hup : x < hat p x) :
      p.idxOf x + 1 = p.length ∨ IsLtrMax p (p.idxOf x + 1) := by
    have hcontains312 (p : List ℕ) :
        D5.S3.Combinatorics.ArrowWilfDefs.Contains [3, 1, 2] [] 3 p ↔
          ∃ i j k : Fin p.length, i < j ∧ j < k ∧ p[i.val] > p[k.val] ∧
          p[k.val] > p[j.val] := by
      constructor
      · rintro ⟨x, hlt, _, hsub, _⟩
        change List.Sublist [x 3, x 1, x 2] p at hsub
        obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
        have h0 : p[(f ⟨0, by simp⟩).val] = x 3 := by
          simpa using (hf ⟨0, by simp⟩).symm
        have h1 : p[(f ⟨1, by simp⟩).val] = x 1 := by
          simpa using (hf ⟨1, by simp⟩).symm
        have h2 : p[(f ⟨2, by simp⟩).val] = x 2 := by
          simpa using (hf ⟨2, by simp⟩).symm
        refine ⟨f ⟨0, by simp⟩, f ⟨1, by simp⟩, f ⟨2, by simp⟩,
          f.strictMono (by simp), f.strictMono (by simp), ?_, ?_⟩
        · simpa only [← h0, ← h2] using hlt 2 (by omega) (by omega)
        · simpa only [← h2, ← h1] using hlt 1 (by omega) (by omega)
      · rintro ⟨i, j, k, hij, hjk, hik, hkj⟩
        let x : ℕ → ℕ := fun t => if t = 1 then p[j.val] else if t = 2 then p[k.val]
          else p[i.val]
        have hx1 : x 1 = p[j.val] := by simp [x]
        have hx2 : x 2 = p[k.val] := by simp [x]
        have hx3 : x 3 = p[i.val] := by simp [x]
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
          rcases h with rfl | rfl <;> simp [hx1, hx2, hx3, hkj, hik]
        · intro t ht ht3
          have h : t = 1 ∨ t = 2 ∨ t = 3 := by omega
          rcases h with rfl | rfl | rfl <;> simp [hx1, hx2, hx3]
        · simpa [hx1, hx2, hx3] using hsub
    let i := p.idxOf x
    have hi : i < p.length := List.idxOf_lt_length_of_mem hx
    by_contra hnotclose
    have hnext : i + 1 < p.length := by
      by_contra hnot
      apply hnotclose
      left
      omega
    have hnon : ¬ IsLtrMax p (i + 1) := by
      intro h
      exact hnotclose (Or.inr h)
    let s := Nat.findGreatest (IsLtrMax p) i
    have hsle : s ≤ i := Nat.findGreatest_le _
    have hs : s < p.length := by omega
    have hzero : IsLtrMax p 0 := by
      intro j hj
      omega
    have hrecord : IsLtrMax p s := by
      exact Nat.findGreatest_spec (Nat.zero_le i) hzero
    have hgreatest : Nat.findGreatest (IsLtrMax p) (i + 1) = s := by
      rw [Nat.findGreatest_succ, if_neg hnon]
    have hbound : p.getD (i + 1) 0 ≤ p.getD s 0 := by
      simpa only [hgreatest] using
        last_record_bounds_prefix p (i + 1) hnext (i + 1) (le_refl _)
    have hvalue : p.getD i 0 = x := by
      rw [List.getD_eq_getElem _ 0 hi]
      exact List.getElem_idxOf hi
    have hhat : hat p x = p.getD (i + 1) 0 := by
      unfold hat
      exact if_pos ⟨hnext, hnon⟩
    have hrise : p.getD i 0 < p.getD (i + 1) 0 := by
      rw [hvalue, ← hhat]
      exact hup
    have hsi : s < i := by
      by_contra h
      have heq : s = i := by omega
      rw [heq] at hbound
      omega
    have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
    have hne : p.getD s 0 ≠ p.getD (i + 1) 0 := by
      intro heq
      rw [List.getD_eq_getElem _ 0 hs,
        List.getD_eq_getElem _ 0 hnext] at heq
      have := (hnodup.getElem_inj_iff).mp heq
      omega
    have hfall : p.getD (i + 1) 0 < p.getD s 0 := by omega
    apply havoid
    apply (hcontains312 p).mpr
    refine ⟨⟨s, hs⟩, ⟨i, hi⟩, ⟨i + 1, hnext⟩, hsi, ?_, ?_, ?_⟩
    · change i < i + 1
      omega
    · rw [← List.getD_eq_getElem _ 0 hs,
        ← List.getD_eq_getElem _ 0 hnext]
      exact hfall
    · rw [← List.getD_eq_getElem _ 0 hnext,
        ← List.getD_eq_getElem _ 0 hi]
      exact hrise
  have next_large_record (p : List ℕ) (n : ℕ)
      (hp : p.Perm (List.range' 1 n)) (hn : 7 ≤ n)
      (havoid : ¬ Contains [3, 1, 2] [] 3 p)
      (hpen : p.getD (n - 4) 0 = n - 1)
      (htwo : p.getD (n - 3) 0 = 2)
      (hmax : p.getD (n - 2) 0 = n)
      (hone : p.getD (n - 1) 0 = 1)
      (hhat : hat p 3 = n - 3) :
      p.idxOf (n - 2) = p.idxOf 3 + 1 := by
    have upward_edge_before_larger (p : List ℕ)
        (hp : p.Perm (List.range' 1 p.length))
        (havoid : ¬ Contains [3, 1, 2] [] 3 p)
        (x y : ℕ) (hx : x ∈ p) (hy : y ∈ p)
        (hup : x < hat p x) (hlarge : hat p x < y) :
        p.idxOf x < p.idxOf y := by
      have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
      have hix : p.idxOf x < p.length := List.idxOf_lt_length_of_mem hx
      have hiy : p.idxOf y < p.length := List.idxOf_lt_length_of_mem hy
      have hclose := upward_hat_edge_closes_block p hp havoid x hx hup
      have hbranch :
          ¬ (p.idxOf x + 1 < p.length ∧ ¬ IsLtrMax p (p.idxOf x + 1)) := by
        rcases hclose with he | hr
        · intro h; omega
        · intro h; exact h.2 hr
      have htarget : hat p x =
          p.getD (Nat.findGreatest (IsLtrMax p) (p.idxOf x)) 0 := by
        unfold hat
        exact if_neg hbranch
      by_contra hnot
      have hbound := last_record_bounds_prefix p (p.idxOf x) hix
        (p.idxOf y) (by omega)
      have hyval : p.getD (p.idxOf y) 0 = y := by
        rw [List.getD_eq_getElem _ 0 hiy]
        exact List.getElem_idxOf hiy
      rw [hyval, ← htarget] at hbound
      omega
    have hlen : p.length = n := by simpa using hp.length_eq
    have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
    have hmem (x : ℕ) (hx : 1 ≤ x) (hxn : x ≤ n) : x ∈ p := by
      apply hp.mem_iff.mpr
      exact List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩
    have h3mem : 3 ∈ p := hmem 3 (by omega) (by omega)
    have hm2mem : n - 2 ∈ p := hmem (n - 2) (by omega) (by omega)
    have hm3mem : n - 3 ∈ p := hmem (n - 3) (by omega) (by omega)
    have hgetinj (i j : ℕ) (hi : i < n) (hj : j < n)
        (heq : p.getD i 0 = p.getD j 0) : i = j := by
      have helem : p[i] = p[j] := by
        rw [← List.getD_eq_getElem _ 0 (by omega : i < p.length),
          ← List.getD_eq_getElem _ 0 (by omega : j < p.length), heq]
      exact (hnodup.getElem_inj_iff).mp helem
    have hm2lt : p.idxOf (n - 2) < n - 4 := by
      have hi : p.idxOf (n - 2) < n := by
        simpa [hlen] using List.idxOf_lt_length_of_mem hm2mem
      by_contra hnot
      have hval : p.getD (p.idxOf (n - 2)) 0 = n - 2 := by
        rw [List.getD_eq_getElem _ 0 (by omega : p.idxOf (n - 2) < p.length)]
        exact List.getElem_idxOf (by omega : p.idxOf (n - 2) < p.length)
      have hcases : p.idxOf (n - 2) = n - 4 ∨
          p.idxOf (n - 2) = n - 3 ∨
          p.idxOf (n - 2) = n - 2 ∨ p.idxOf (n - 2) = n - 1 := by omega
      rcases hcases with h | h | h | h
      · rw [h, hpen] at hval; omega
      · rw [h, htwo] at hval; omega
      · rw [h, hmax] at hval; omega
      · rw [h, hone] at hval; omega
    have h3before : p.idxOf 3 < p.idxOf (n - 2) :=
      upward_edge_before_larger p (by simpa [hlen] using hp) havoid
        3 (n - 2) h3mem hm2mem (by rw [hhat]; omega)
        (by rw [hhat]; omega)
    have h3lt : p.idxOf 3 < n - 4 := by omega
    have hnextlt : p.idxOf 3 + 1 < n - 4 := by omega
    have hclose := upward_hat_edge_closes_block p
      (by simpa [hlen] using hp) havoid 3 h3mem (by rw [hhat]; omega)
    have hnextrec : IsLtrMax p (p.idxOf 3 + 1) := by
      rcases hclose with he | he
      · omega
      · exact he
    let g := Nat.findGreatest (IsLtrMax p) (p.idxOf 3)
    have hbranch :
        ¬ (p.idxOf 3 + 1 < p.length ∧ ¬ IsLtrMax p (p.idxOf 3 + 1)) := by
      intro he
      exact he.2 hnextrec
    have hgv : p.getD g 0 = n - 3 := by
      have hh : hat p 3 = p.getD g 0 := by
        dsimp [g]
        unfold hat
        exact if_neg hbranch
      rw [hhat] at hh
      exact hh.symm
    have hglt : g < p.idxOf 3 + 1 := by
      have hg : g ≤ p.idxOf 3 := Nat.findGreatest_le _
      omega
    have hnextgt : n - 3 < p.getD (p.idxOf 3 + 1) 0 := by
      have hh := hnextrec g hglt
      rw [hgv] at hh
      exact hh
    have hnextle : p.getD (p.idxOf 3 + 1) 0 ≤ n - 2 := by
      have hj : p.idxOf 3 + 1 < p.length := by omega
      have hm : p.getD (p.idxOf 3 + 1) 0 ∈ p := by
        rw [List.getD_eq_getElem _ 0 hj]
        exact List.getElem_mem hj
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hm)
      have hnepen : p.getD (p.idxOf 3 + 1) 0 ≠ n - 1 := by
        intro he
        have hi := hgetinj (p.idxOf 3 + 1) (n - 4)
          (by omega) (by omega) (he.trans hpen.symm)
        omega
      have hnemax : p.getD (p.idxOf 3 + 1) 0 ≠ n := by
        intro he
        have hi := hgetinj (p.idxOf 3 + 1) (n - 2)
          (by omega) (by omega) (he.trans hmax.symm)
        omega
      omega
    have hnextval : p.getD (p.idxOf 3 + 1) 0 = n - 2 := by omega
    have hm2val : p.getD (p.idxOf (n - 2)) 0 = n - 2 := by
      rw [List.getD_eq_getElem _ 0 (by omega : p.idxOf (n - 2) < p.length)]
      exact List.getElem_idxOf (by omega : p.idxOf (n - 2) < p.length)
    exact (hgetinj (p.idxOf (n - 2)) (p.idxOf 3 + 1)
      (by omega) (by omega) (hm2val.trans hnextval.symm))
  have hlen : p.length = n := by simpa using hp.length_eq
  have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hmem (x : ℕ) (hx : 1 ≤ x) (hxn : x ≤ n) : x ∈ p := by
    apply hp.mem_iff.mpr
    exact List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩
  have h3mem : 3 ∈ p := hmem 3 (by omega) (by omega)
  have hm2mem : n - 2 ∈ p := hmem (n - 2) (by omega) (by omega)
  have hm3mem : n - 3 ∈ p := hmem (n - 3) (by omega) (by omega)
  have h3lt : p.idxOf 3 < n := by
    simpa [hlen] using List.idxOf_lt_length_of_mem h3mem
  have hm2lt : p.idxOf (n - 2) < n := by
    simpa [hlen] using List.idxOf_lt_length_of_mem hm2mem
  have hm3lt : p.idxOf (n - 3) < n := by
    simpa [hlen] using List.idxOf_lt_length_of_mem hm3mem
  have hgetinj (i j : ℕ) (hi : i < n) (hj : j < n)
      (heq : p.getD i 0 = p.getD j 0) : i = j := by
    have helem : p[i] = p[j] := by
      rw [← List.getD_eq_getElem _ 0 (by omega : i < p.length),
        ← List.getD_eq_getElem _ 0 (by omega : j < p.length), heq]
    exact (hnodup.getElem_inj_iff).mp helem
  have h3val : p.getD (p.idxOf 3) 0 = 3 := by
    rw [List.getD_eq_getElem _ 0 (by omega : p.idxOf 3 < p.length)]
    exact List.getElem_idxOf (by omega : p.idxOf 3 < p.length)
  have hm2val : p.getD (p.idxOf (n - 2)) 0 = n - 2 := by
    rw [List.getD_eq_getElem _ 0 (by omega : p.idxOf (n - 2) < p.length)]
    exact List.getElem_idxOf (by omega : p.idxOf (n - 2) < p.length)
  have hm3val : p.getD (p.idxOf (n - 3)) 0 = n - 3 := by
    rw [List.getD_eq_getElem _ 0 (by omega : p.idxOf (n - 3) < p.length)]
    exact List.getElem_idxOf (by omega : p.idxOf (n - 3) < p.length)
  have hnext := next_large_record p n hp hn havoid hpen htwo hmax hone hhat
  have hm2front : p.idxOf (n - 2) < n - 4 := by
    by_contra hnot
    have hcases : p.idxOf (n - 2) = n - 4 ∨
        p.idxOf (n - 2) = n - 3 ∨
        p.idxOf (n - 2) = n - 2 ∨ p.idxOf (n - 2) = n - 1 := by omega
    rcases hcases with h | h | h | h
    · rw [h, hpen] at hm2val; omega
    · rw [h, htwo] at hm2val; omega
    · rw [h, hmax] at hm2val; omega
    · rw [h, hone] at hm2val; omega
  have h3front : p.idxOf 3 + 1 < n - 4 := by omega
  have hclose := upward_hat_edge_closes_block p
    (by simpa [hlen] using hp) havoid 3 h3mem (by rw [hhat]; omega)
  have hbranch :
      ¬ (p.idxOf 3 + 1 < p.length ∧ ¬ IsLtrMax p (p.idxOf 3 + 1)) := by
    rcases hclose with he | he
    · intro h; omega
    · intro h; exact h.2 he
  have hm3before : p.idxOf (n - 3) ≤ p.idxOf 3 := by
    let g := Nat.findGreatest (IsLtrMax p) (p.idxOf 3)
    have hglt : g < p.length := by
      have hg := Nat.findGreatest_le (P := IsLtrMax p) (p.idxOf 3)
      dsimp [g]
      omega
    have hvalue : p.getD g 0 = n - 3 := by
      have hh : hat p 3 = p.getD g 0 := by
        dsimp [g]
        unfold hat
        exact if_neg hbranch
      rw [hhat] at hh
      exact hh.symm
    have hidx : p.idxOf (n - 3) = g := by
      rw [← hvalue, List.getD_eq_getElem _ 0 hglt]
      exact hnodup.idxOf_getElem (i := g) hglt
    rw [hidx]
    exact Nat.findGreatest_le _
  have hnogap : p.idxOf 3 + 2 = n - 4 := by
    by_contra hne
    have hk : p.idxOf 3 + 2 < n - 4 := by omega
    let k := p.idxOf 3 + 2
    let z := p.getD k 0
    have hzmem : z ∈ p := by
      dsimp [z]
      rw [List.getD_eq_getElem _ 0 (by omega : k < p.length)]
      exact List.getElem_mem (by omega : k < p.length)
    have hzidx : p.idxOf z = k := by
      dsimp [z]
      rw [List.getD_eq_getElem _ 0 (by omega : k < p.length)]
      exact hnodup.idxOf_getElem (i := k) (by omega : k < p.length)
    have hzne (v t : ℕ) (ht : t < n) (hkt : k ≠ t)
        (hv : p.getD t 0 = v) : z ≠ v := by
      intro he
      have hsame : p.getD k 0 = p.getD t 0 := by
        exact (show p.getD k 0 = v from he).trans hv.symm
      exact hkt (hgetinj k t (by omega) ht hsame)
    have hzrange : 1 ≤ z ∧ z ≤ n := by
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hzmem)
      omega
    have hzlow : 3 < z := by
      have hz1 := hzne 1 (n - 1) (by omega) (by omega) hone
      have hz2 := hzne 2 (n - 3) (by omega) (by omega) htwo
      have hz3 := hzne 3 (p.idxOf 3) h3lt (by dsimp [k]; omega) h3val
      omega
    have hzhigh : z < n - 3 := by
      have hzm3 := hzne (n - 3) (p.idxOf (n - 3)) hm3lt
        (by dsimp [k]; omega) hm3val
      have hzm2 := hzne (n - 2) (p.idxOf (n - 2)) hm2lt
        (by dsimp [k]; omega) hm2val
      have hzm1 := hzne (n - 1) (n - 4) (by omega) (by dsimp [k]; omega) hpen
      have hzn := hzne n (n - 2) (by omega) (by dsimp [k]; omega) hmax
      omega
    have hposition : p.idxOf 3 < p.idxOf z := by
      rw [hzidx]
      dsimp [k]
      omega
    exact no_upward_edge_over_later_value p (by simpa [hlen] using hp)
      havoid 3 z h3mem hzmem
      (by rw [hhat]; omega) hposition
  have h3pos : p.idxOf 3 = n - 6 := by omega
  have hm2pos : p.idxOf (n - 2) = n - 5 := by omega
  constructor
  · rw [← h3pos]
    exact h3val
  · rw [← hm2pos]
    exact hm2val

end D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Suffix
