/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateRecords
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateRecords
   mirror-E: none(waiver:record-head-gap-for-iterated-theta)
   anchors: []
   utility: none
   digest: Consecutive record heads in a 132-avoiding permutation differ by one. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse

/-- Two successive record heads of a 132-avoider cannot skip a value: a skipped
value would either form a 132 after the second head or force an intervening record. -/
theorem adjacent_record_values (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length))
    (havoid : ¬ Contains [1, 3, 2] [] 3 p)
    (i j : ℕ) (hi : i < j) (hj : j < p.length)
    (hrec_i : IsLtrMax p i) (hrec_j : IsLtrMax p j)
    (hnone : ∀ k, i < k → k < j → ¬ IsLtrMax p k) :
    p.getD j 0 = p.getD i 0 + 1 := by
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

  have hiLen : i < p.length := by omega
  have hlt : p.getD i 0 < p.getD j 0 := hrec_j i hi
  by_contra hne
  have hgap : p.getD i 0 + 1 < p.getD j 0 := by omega
  let c := p.getD i 0 + 1
  have hjmem : p.getD j 0 ∈ p := by
    rw [List.getD_eq_getElem _ 0 hj]
    exact List.getElem_mem hj
  obtain ⟨u, hu, hju⟩ := List.mem_range'.mp (hp.mem_iff.mp hjmem)
  have hcMem : c ∈ p := hp.mem_iff.mpr (List.mem_range'.mpr ⟨c - 1, by omega, by omega⟩)
  let t := p.idxOf c
  have ht : t < p.length := List.idxOf_lt_length_of_mem hcMem
  have htc : p.getD t 0 = c := by
    rw [List.getD_eq_getElem _ 0 ht]
    exact List.getElem_idxOf ht
  have hit : i < t := by
    by_contra h
    have hti : t < i ∨ t = i := by omega
    rcases hti with hti | hti
    · have := hrec_i t hti
      rw [htc] at this
      dsimp [c] at this
      omega
    · rw [hti] at htc
      dsimp [c] at htc
      omega
  have htj : t < j := by
    by_contra h
    have hjt : j < t ∨ j = t := by omega
    rcases hjt with hjt | hjt
    · apply havoid
      apply (contains132_iff_indices p).mpr
      refine ⟨⟨i, hiLen⟩, ⟨j, hj⟩, ⟨t, ht⟩, hi, hjt, ?_, ?_⟩
      · have hict : p.getD i 0 < p.getD t 0 := by
          rw [htc]
          dsimp [c]
          omega
        simpa only [List.getD_eq_getElem _ 0 hiLen,
          List.getD_eq_getElem _ 0 ht] using hict
      · have htj' : p.getD t 0 < p.getD j 0 := by
          rw [htc]
          exact hgap
        simpa only [List.getD_eq_getElem _ 0 ht,
          List.getD_eq_getElem _ 0 hj] using htj'
    · rw [← hjt] at htc
      dsimp [c] at htc
      omega
  let k := Nat.findGreatest (IsLtrMax p) t
  have hkrec : IsLtrMax p k := by
    apply Nat.findGreatest_spec (Nat.zero_le t)
    intro v hv
    omega
  have hkt : k ≤ t := Nat.findGreatest_le t
  have hck : c ≤ p.getD k 0 := by
    simpa only [htc] using last_record_bounds_prefix p t ht t (le_refl t)
  have hik : i < k := by
    by_contra h
    have hki : k < i ∨ k = i := by omega
    rcases hki with hki | hki
    · have := hrec_i k hki
      dsimp [c] at hck
      omega
    · rw [hki] at hck
      dsimp [c] at hck
      omega
  exact (hnone k hik (by omega)) hkrec

/-- Every entry before a record head is larger than each entry in that head's tail.
If the inequality were reversed, the earlier entry, head, and tail entry form 132. -/
theorem earlier_entry_gt_later_tail (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length))
    (havoid : ¬ Contains [1, 3, 2] [] 3 p)
    (i s k : ℕ) (his : i < s) (hsk : s < k) (hk : k < p.length)
    (hs : IsLtrMax p s)
    (hnone : ∀ j, s < j → j ≤ k → ¬ IsLtrMax p j) :
    p.getD k 0 < p.getD i 0 := by
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

  have hnd : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hgreatest : Nat.findGreatest (IsLtrMax p) k = s := by
    have hle : s ≤ Nat.findGreatest (IsLtrMax p) k :=
      Nat.le_findGreatest (by omega) hs
    have hge : Nat.findGreatest (IsLtrMax p) k ≤ k := Nat.findGreatest_le k
    by_contra hne
    have hrec : IsLtrMax p (Nat.findGreatest (IsLtrMax p) k) := by
      apply Nat.findGreatest_spec (Nat.zero_le k)
      intro v hv
      omega
    exact hnone _ (by omega) hge hrec
  have hbound := last_record_bounds_prefix p k hk k (le_refl k)
  rw [hgreatest] at hbound
  have hneq : p.getD k 0 ≠ p.getD s 0 := by
    intro heq
    have hval : p[k] = p[s] := by
      simpa only [← List.getD_eq_getElem _ 0 hk,
        ← List.getD_eq_getElem _ 0 (by omega : s < p.length)] using heq
    have := (hnd.getElem_inj_iff).mp hval
    omega
  have hks : p.getD k 0 < p.getD s 0 := by omega
  have hik : p.getD i 0 ≠ p.getD k 0 := by
    intro heq
    have hval : p[i] = p[k] := by
      simpa only [← List.getD_eq_getElem _ 0 (by omega : i < p.length),
        ← List.getD_eq_getElem _ 0 hk] using heq
    have := (hnd.getElem_inj_iff).mp hval
    omega
  by_contra hnot
  have hfirst : p.getD i 0 < p.getD k 0 := by omega
  apply havoid
  apply (contains132_iff_indices p).mpr
  refine ⟨⟨i, by omega⟩, ⟨s, by omega⟩, ⟨k, hk⟩, his, hsk, ?_, ?_⟩
  · simpa only [← List.getD_eq_getElem _ 0 (by omega : i < p.length),
      ← List.getD_eq_getElem _ 0 hk] using hfirst
  · simpa only [← List.getD_eq_getElem _ 0 hk,
      ← List.getD_eq_getElem _ 0 (by omega : s < p.length)] using hks

/-- The record-block criterion for 132 avoidance. The second condition checks only
triples strictly inside one tail; the third condition orders different blocks. -/
theorem avoids132_iff_record_blocks (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length)) :
    (¬ Contains [1, 3, 2] [] 3 p) ↔
      (∀ i j, i < j → j < p.length → IsLtrMax p i → IsLtrMax p j →
          (∀ t, i < t → t < j → ¬ IsLtrMax p t) →
          p.getD j 0 = p.getD i 0 + 1) ∧
      (∀ s i j k, s < i → i < j → j < k → k < p.length →
          IsLtrMax p s →
          (∀ t, s < t → t ≤ k → ¬ IsLtrMax p t) →
          ¬ (p.getD i 0 < p.getD k 0 ∧ p.getD k 0 < p.getD j 0)) ∧
      (∀ i s k, i < s → s < k → k < p.length → IsLtrMax p s →
          (∀ t, s < t → t ≤ k → ¬ IsLtrMax p t) →
          p.getD k 0 < p.getD i 0) := by
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

  constructor
  · intro havoid
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij hj hi hrec hnone
      exact adjacent_record_values p hp havoid i j hij hj hi hrec hnone
    · intro s i j k hsi hij hjk hk _ _ ⟨hik, hkj⟩
      apply havoid
      apply (contains132_iff_indices p).mpr
      refine ⟨⟨i, by omega⟩, ⟨j, by omega⟩, ⟨k, hk⟩, hij, hjk, ?_, ?_⟩
      · simpa only [← List.getD_eq_getElem _ 0 (by omega : i < p.length),
          ← List.getD_eq_getElem _ 0 hk] using hik
      · simpa only [← List.getD_eq_getElem _ 0 hk,
          ← List.getD_eq_getElem _ 0 (by omega : j < p.length)] using hkj
    · intro i s k his hsk hk hs hnone
      exact earlier_entry_gt_later_tail p hp havoid i s k his hsk hk hs hnone
  · rintro ⟨_, htail, hcross⟩ hcontains
    obtain ⟨i, j, k, hij, hjk, hik, hkj⟩ :=
      (contains132_iff_indices p).mp hcontains
    have hk : k.val < p.length := k.isLt
    have hi : i.val < p.length := by omega
    have hj : j.val < p.length := by omega
    have hikD : p.getD i.val 0 < p.getD k.val 0 := by
      simpa only [List.getD_eq_getElem _ 0 hi,
        List.getD_eq_getElem _ 0 hk] using hik
    have hkjD : p.getD k.val 0 < p.getD j.val 0 := by
      simpa only [List.getD_eq_getElem _ 0 hk,
        List.getD_eq_getElem _ 0 hj] using hkj
    let s := Nat.findGreatest (IsLtrMax p) k.val
    have hs : IsLtrMax p s := by
      apply Nat.findGreatest_spec (Nat.zero_le k.val)
      intro v hv
      omega
    have hskle : s ≤ k.val := Nat.findGreatest_le k.val
    have hnone (t : ℕ) (hst : s < t) (htk : t ≤ k.val) :
        ¬ IsLtrMax p t := by
      intro hrec
      have hts : t ≤ s := Nat.le_findGreatest htk hrec
      omega
    by_cases hks : s = k.val
    · have hrec : IsLtrMax p k.val := hks ▸ hs
      have := hrec j.val (by omega)
      omega
    have hsk : s < k.val := by omega
    by_cases his : i.val < s
    · have := hcross i.val s k.val his hsk hk hs hnone
      omega
    have hsi : s ≤ i.val := by omega
    by_cases hsiEq : s = i.val
    · have hbound := last_record_bounds_prefix p k.val hk k.val (le_refl k.val)
      change p.getD k.val 0 ≤ p.getD s 0 at hbound
      rw [← hsiEq] at hikD
      omega
    have hsiLt : s < i.val := by omega
    exact htail s i.val j.val k.val hsiLt hij hjk hk hs hnone ⟨hikD, hkjD⟩


end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords
