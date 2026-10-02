/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaCube312Edge
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaCube312Edge
   mirror-E: none(waiver:upward-inverse-edge-obstruction)
   anchors: []
   utility: none
   digest: A 312-avoider cannot have an upward inverse edge straddling a later value. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Edge

open ThetaBasicInverse
open D5.S3.Combinatorics.ArrowWilfDefs

/-- In a 312-avoider an upward `hat` edge closes a record block. Its target
therefore occurs before the source, so any later intermediate value makes
a forbidden triple. -/
theorem no_upward_edge_over_later_value (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length))
    (havoid : ¬ Contains [3, 1, 2] [] 3 p)
    (x z : ℕ) (hx : x ∈ p) (hz : z ∈ p)
    (horder : x < z ∧ z < hat p x)
    (hposition : p.idxOf x < p.idxOf z) : False := by
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
  let y := hat p x
  have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hix : p.idxOf x < p.length := List.idxOf_lt_length_of_mem hx
  have hiz : p.idxOf z < p.length := List.idxOf_lt_length_of_mem hz
  have hclose := upward_hat_edge_closes_block p hp havoid x hx
    (lt_trans horder.1 horder.2)
  have hbranch :
      ¬ (p.idxOf x + 1 < p.length ∧ ¬ IsLtrMax p (p.idxOf x + 1)) := by
    rcases hclose with he | hr
    · intro h
      omega
    · intro h
      exact h.2 hr
  let g := Nat.findGreatest (IsLtrMax p) (p.idxOf x)
  have hg : g < p.length := lt_of_le_of_lt (Nat.findGreatest_le _) hix
  have hy : y = p.getD g 0 := by
    dsimp [y, g]
    unfold hat
    exact if_neg hbranch
  have hyidx : p.idxOf y = g := by
    rw [hy, List.getD_eq_getElem _ 0 hg]
    exact hnodup.idxOf_getElem (i := g) hg
  have hxval : p.getD (p.idxOf x) 0 = x := by
    rw [List.getD_eq_getElem _ 0 hix]
    exact List.getElem_idxOf hix
  have hyg : g < p.idxOf x := by
    have hle : g ≤ p.idxOf x := Nat.findGreatest_le _
    by_contra hnot
    have heq : g = p.idxOf x := by omega
    rw [heq, hxval] at hy
    dsimp [y] at hy
    omega
  apply havoid
  apply (hcontains312 p).mpr
  refine ⟨⟨p.idxOf y, by omega⟩, ⟨p.idxOf x, hix⟩,
    ⟨p.idxOf z, hiz⟩, ?_, ?_, ?_, ?_⟩
  · change p.idxOf y < p.idxOf x
    rw [hyidx]
    exact hyg
  · change p.idxOf x < p.idxOf z
    exact hposition
  · change p[p.idxOf y] > p[p.idxOf z]
    rw [List.getElem_idxOf (by omega : p.idxOf y < p.length),
      List.getElem_idxOf hiz]
    exact horder.2
  · change p[p.idxOf z] > p[p.idxOf x]
    rw [List.getElem_idxOf hiz, List.getElem_idxOf hix]
    exact horder.1

end D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Edge
