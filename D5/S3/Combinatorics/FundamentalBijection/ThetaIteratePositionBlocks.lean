/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIteratePositionBlocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIteratePositionBlocks
   mirror-E: none(waiver:maximum-position-in-iterated-theta-avoiders)
   anchors: []
   utility: none
   digest: Record-block inverse edges constrain the positions of one and the maximum. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseGeneral

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIteratePosition

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse

local notation "B" =>
  (fun p : List ℕ => List.map (hat p) (List.range' 1 (List.length p)))

/-- Once the minimum has appeared, a 132-avoiding permutation has no later descent. -/
theorem suffix_after_one_increasing (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length))
    (havoid : ¬ Contains [1, 3, 2] [] 3 p)
    (i j k : ℕ) (hij : i < j) (hjk : j < k) (hk : k < p.length)
    (hone : p.getD i 0 = 1) : p.getD j 0 < p.getD k 0 := by
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
  have hpositive : 0 < p.getD k 0 := by
    have hmem : p.getD k 0 ∈ p := by
      rw [List.getD_eq_getElem _ 0 hk]
      exact List.getElem_mem hk
    obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hp.mem_iff.mp hmem)
    omega
  have hik : p.getD i 0 ≠ p.getD k 0 := by
    intro heq
    have hval : p[i] = p[k] := by
      simpa only [← List.getD_eq_getElem _ 0 (by omega : i < p.length),
        ← List.getD_eq_getElem _ 0 hk] using heq
    have := (hnd.getElem_inj_iff).mp hval
    omega
  have hfirst : p.getD i 0 < p.getD k 0 := by omega
  have hjk_ne : p.getD j 0 ≠ p.getD k 0 := by
    intro heq
    have hval : p[j] = p[k] := by
      simpa only [← List.getD_eq_getElem _ 0 (by omega : j < p.length),
        ← List.getD_eq_getElem _ 0 hk] using heq
    have := (hnd.getElem_inj_iff).mp hval
    omega
  by_contra hnot
  have hlast : p.getD k 0 < p.getD j 0 := by omega
  apply havoid
  apply (contains132_iff_indices p).mpr
  refine ⟨⟨i, by omega⟩, ⟨j, by omega⟩, ⟨k, hk⟩, hij, hjk, ?_, ?_⟩
  · simpa only [← List.getD_eq_getElem _ 0 (by omega : i < p.length),
      ← List.getD_eq_getElem _ 0 hk] using hfirst
  · simpa only [← List.getD_eq_getElem _ 0 hk,
      ← List.getD_eq_getElem _ 0 (by omega : j < p.length)] using hlast

/-- If the final record block is nontrivial and another block precedes it,
the predecessor of the maximum in that cycle must be the minimum. -/
theorem final_block_predecessor_one (q : List ℕ)
    (hq : q.Perm (List.range' 1 q.length))
    (havoidq : ¬ Contains [1, 3, 2] [] 3 q)
    (havoidB : ¬ Contains [1, 3, 2] [] 3 (B q))
    (s : ℕ) (hs0 : 0 < s) (hstail : s + 1 < q.length)
    (hsmax : q.getD s 0 = q.length) :
    q.getD (q.length - 1) 0 = 1 := by
  have final_tail_downward_closed (p : List ℕ)
      (hp : p.Perm (List.range' 1 p.length))
      (havoid : ¬ Contains [1, 3, 2] [] 3 p)
      (s k c : ℕ) (hsk : s < k) (hk : k < p.length)
      (hs : IsLtrMax p s)
      (hnone : ∀ j, s < j → j < p.length → ¬ IsLtrMax p j)
      (hc : c ∈ p) (hcv : c < p.getD k 0) : s < p.idxOf c := by
    have hnd : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
    have ht : p.idxOf c < p.length := List.idxOf_lt_length_of_mem hc
    have htc : p.getD (p.idxOf c) 0 = c := by
      rw [List.getD_eq_getElem _ 0 ht]
      exact List.getElem_idxOf ht
    by_contra hnot
    have hle : p.idxOf c ≤ s := by omega
    by_cases heq : p.idxOf c = s
    · have hgreatest : Nat.findGreatest (IsLtrMax p) k = s := by
        have hlow : s ≤ Nat.findGreatest (IsLtrMax p) k :=
          Nat.le_findGreatest (by omega) hs
        have hupp : Nat.findGreatest (IsLtrMax p) k ≤ k := Nat.findGreatest_le k
        by_contra hne
        have hrec : IsLtrMax p (Nat.findGreatest (IsLtrMax p) k) := by
          apply Nat.findGreatest_spec (Nat.zero_le k)
          intro v hv
          omega
        exact hnone _ (by omega) (by omega) hrec
      have hbound := last_record_bounds_prefix p k hk k (le_refl k)
      rw [hgreatest] at hbound
      rw [heq] at htc
      omega
    · have hbefore : p.idxOf c < s := by omega
      have hcross := ((avoids132_iff_record_blocks p hp).mp havoid).2.2
        (p.idxOf c) s k hbefore hsk hk hs
        (by intro j hsj hjk; exact hnone j hsj (by omega))
      rw [htc] at hcross
      omega
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

  let n := q.length
  have hnd : q.Nodup := hq.nodup_iff.mpr List.nodup_range'
  have hs : IsLtrMax q s := by
    intro i hi
    have hil : i < n := by omega
    have hmem : q.getD i 0 ∈ q := by
      rw [List.getD_eq_getElem _ 0 hil]
      exact List.getElem_mem hil
    obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hq.mem_iff.mp hmem)
    have hneq : q.getD i 0 ≠ q.getD s 0 := by
      intro heq
      have hval : q[i] = q[s] := by
        simpa only [← List.getD_eq_getElem _ 0 hil,
          ← List.getD_eq_getElem _ 0 (by omega : s < q.length)] using heq
      have := (hnd.getElem_inj_iff).mp hval
      omega
    omega
  have hno (i : ℕ) (hsi : s < i) (hin : i < n) : ¬ IsLtrMax q i := by
    intro hrec
    have hlt := hrec s hsi
    have hmem : q.getD i 0 ∈ q := by
      rw [List.getD_eq_getElem _ 0 hin]
      exact List.getElem_mem hin
    obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hq.mem_iff.mp hmem)
    omega
  have hidx (i : ℕ) (hi : i < n) : q.idxOf (q.getD i 0) = i := by
    rw [List.getD_eq_getElem _ 0 hi]
    simpa using List.get_idxOf hnd ⟨i, hi⟩
  have hblock : (∀ i, s ≤ i → i + 1 < n →
      hat q (q.getD i 0) = q.getD (i + 1) 0) ∧
      hat q (q.getD (n - 1) 0) = q.getD s 0 := by
    constructor
    · intro i hsi hin
      unfold hat
      rw [hidx i (by omega), if_pos ⟨hin, hno _ (by omega) hin⟩]
    · unfold hat
      rw [hidx (n - 1) (by omega), if_neg (by intro hh; omega)]
      congr 1
      exact Nat.findGreatest_eq_iff.mpr
        ⟨by omega, fun _ => hs, fun j hsj hj => hno j hsj (by omega)⟩
  let t := q.getD (n - 1) 0
  have htmem : t ∈ q := by
    dsimp [t]
    rw [List.getD_eq_getElem _ 0 (by omega : n - 1 < q.length)]
    exact List.getElem_mem (by omega : n - 1 < q.length)
  obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hq.mem_iff.mp htmem)
  have htpos : 0 < t := by omega
  have htn : t < n := by
    have hneq : t ≠ q.getD s 0 := by
      intro heq
      have hval : q[n - 1] = q[s] := by
        simpa only [← List.getD_eq_getElem _ 0 (by omega : n - 1 < q.length),
          ← List.getD_eq_getElem _ 0 (by omega : s < q.length)] using heq
      have := (hnd.getElem_inj_iff).mp hval
      omega
    omega
  by_contra ht1
  have htne : t ≠ 1 := by simpa [t, n] using ht1
  have h1t : 1 < t := by omega
  have h1mem : 1 ∈ q := hq.mem_iff.mpr
    (List.mem_range'.mpr ⟨0, by omega, by simp⟩)
  have h1after : s < q.idxOf 1 :=
    final_tail_downward_closed q hq havoidq s (n - 1) 1
      (by omega) (by omega) hs
      (by intro j hsj hj; exact hno j hsj hj)
      h1mem (by simpa [t] using h1t)
  have h1idx : q.idxOf 1 < n := List.idxOf_lt_length_of_mem h1mem
  have htidx : q.idxOf t = n - 1 := by
    dsimp [t]
    rw [List.getD_eq_getElem _ 0 (by omega : n - 1 < q.length)]
    simpa using (List.get_idxOf hnd ⟨n - 1, by omega⟩)
  have h1next : q.idxOf 1 + 1 < n := by
    by_contra hnot
    have heq : q.idxOf 1 = n - 1 := by omega
    have hget : q.getD (q.idxOf 1) 0 = 1 := by
      rw [List.getD_eq_getElem _ 0 h1idx]
      exact List.getElem_idxOf h1idx
    rw [heq] at hget
    exact ht1 (by simpa [t] using hget)
  have hhat1 : hat q 1 = q.getD (q.idxOf 1 + 1) 0 := by
    have hget : q.getD (q.idxOf 1) 0 = 1 := by
      rw [List.getD_eq_getElem _ 0 h1idx]
      exact List.getElem_idxOf h1idx
    simpa only [hget] using hblock.1 (q.idxOf 1) (by omega) h1next
  have hleftval : q.getD (n - 1) 0 < q.getD 0 0 :=
    earlier_entry_gt_later_tail q hq havoidq 0 s (n - 1)
      hs0 (by omega) (by omega) hs
      (by intro j hsj hj; exact hno j hsj (by omega))
  let l := q.getD 0 0
  have hlt : t < l := by simpa [t, l] using hleftval
  have hln : l < n := by
    change q.getD 0 0 < q.length
    rw [← hsmax]
    exact hs 0 hs0
  have hlpos : 0 < l := by omega
  have hidxl : q.idxOf l = 0 := by
    dsimp [l]
    rw [List.getD_eq_getElem _ 0 (by omega : 0 < q.length)]
    simpa using (List.get_idxOf hnd ⟨0, by omega⟩)
  have hhatl : ∃ i, i < s ∧ hat q l = q.getD i 0 := by
    by_cases hrec : IsLtrMax q 1
    · refine ⟨0, hs0, ?_⟩
      unfold hat
      rw [hidxl, if_neg (by simp [hrec])]
      simp
    · have h1s : 1 < s := by
        by_contra hnot
        have heq : s = 1 := by omega
        exact hrec (by simpa [heq] using hs)
      refine ⟨1, h1s, ?_⟩
      unfold hat
      rw [hidxl, if_pos (by simp [hrec, show 1 < q.length by omega])]
  obtain ⟨i, his, hhati⟩ := hhatl
  have hcross : q.getD (q.idxOf 1 + 1) 0 < q.getD i 0 :=
    earlier_entry_gt_later_tail q hq havoidq i s (q.idxOf 1 + 1)
      his (by omega) h1next hs
      (by intro j hsj hj; exact hno j hsj (by omega))
  have hhatlt : hat q 1 < hat q l := by rw [hhat1, hhati]; exact hcross
  have hhatn : hat q l < n := by
    rw [hhati]
    exact hs i his |>.trans_eq hsmax
  have hBget (x : ℕ) (hx0 : 0 < x) (hxn : x ≤ n) :
      (B q).getD (x - 1) 0 = hat q x := by
    have hindex : x - 1 < n := by omega
    rw [List.getD_eq_getElem _ 0 (by simpa using hindex)]
    simp [List.getElem_range', Nat.add_sub_of_le hx0]
  have hBlen : (B q).length = n := by simp [n]
  have hBt : hat q t = n := by
    simpa [t, n] using hblock.2.trans hsmax
  have hocc : Contains [1, 3, 2] [] 3 (B q) := by
    apply (contains132_iff_indices (B q)).mpr
    refine ⟨⟨0, by omega⟩, ⟨t - 1, by omega⟩, ⟨l - 1, by omega⟩,
      by simp; omega, by simp; omega, ?_, ?_⟩
    · have h := hhatlt
      rw [← hBget 1 (by omega) (by omega),
        ← hBget l hlpos (by omega)] at h
      simpa only [List.getD_eq_getElem _ 0 (by omega : 0 < (B q).length),
        List.getD_eq_getElem _ 0 (by omega : l - 1 < (B q).length)] using h
    · have h := hhatn
      rw [← hBt, ← hBget l hlpos (by omega),
        ← hBget t htpos (by omega)] at h
      simpa only [List.getD_eq_getElem _ 0 (by omega : l - 1 < (B q).length),
        List.getD_eq_getElem _ 0 (by omega : t - 1 < (B q).length)] using h
  exact havoidB hocc

/-- A single record block whose inverse places its maximum in an interior
position must have 1 immediately after its head. -/
theorem one_block_second_one (q : List ℕ)
    (hq : q.Perm (List.range' 1 q.length))
    (havoidq : ¬ Contains [1, 3, 2] [] 3 q)
    (havoidB : ¬ Contains [1, 3, 2] [] 3 (B q))
    (hn : 3 ≤ q.length) (hfirst : q.getD 0 0 = q.length)
    (ht : 1 < q.getD (q.length - 1) 0) :
    q.getD 1 0 = 1 := by
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

  have hat_one_block (word : List ℕ)
      (hmaximum : ∀ value ∈ word, value ≤ word.getD 0 0)
      (value : ℕ) (hvalue : value ∈ word) :
      hat word value = if word.idxOf value + 1 < word.length then
        word.getD (word.idxOf value + 1) 0 else word.getD 0 0 := by
    have hindex : word.idxOf value < word.length :=
      List.idxOf_lt_length_of_mem hvalue
    have hnonrecord (index : ℕ) (hpositive : 0 < index) (hbound : index < word.length) :
        ¬ IsLtrMax word index := by
      intro hrecord
      have hlt := hrecord 0 hpositive
      have hmember : word.getD index 0 ∈ word := by
        rw [List.getD_eq_getElem _ 0 hbound]
        exact List.getElem_mem hbound
      have hle := hmaximum _ hmember
      omega
    have hgreatest : Nat.findGreatest (IsLtrMax word) (word.idxOf value) = 0 := by
      apply Nat.findGreatest_eq_zero_iff.mpr
      intro index hpositive hbound
      exact hnonrecord index hpositive (by omega)
    unfold hat
    by_cases hnext : word.idxOf value + 1 < word.length
    · rw [if_pos ⟨hnext, hnonrecord _ (by omega) hnext⟩, if_pos hnext]
    · rw [if_neg (fun hcase => hnext hcase.1), if_neg hnext, hgreatest]
  let n := q.length
  let t := q.getD (n - 1) 0
  let c := q.getD 1 0
  have hnd : q.Nodup := hq.nodup_iff.mpr List.nodup_range'
  have B_perm (p : List ℕ) (hp : p.Perm (List.range' 1 p.length)) :
      (B p).Perm (List.range' 1 p.length) := by
    have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
    have hmem (x : ℕ) (hx : x ∈ p) : hat p x ∈ p := by
      have hi : p.idxOf x < p.length := List.idxOf_lt_length_of_mem hx
      unfold hat
      dsimp only
      split_ifs with h
      · rw [List.getD_eq_getElem _ 0 h.1]
        exact List.getElem_mem h.1
      · have hg : Nat.findGreatest (IsLtrMax p) (p.idxOf x) < p.length :=
          lt_of_le_of_lt (Nat.findGreatest_le _) hi
        rw [List.getD_eq_getElem _ 0 hg]
        exact List.getElem_mem hg
    have hmapNodup : (p.map (hat p)).Nodup := hnodup.map_on (hat_inj_on p hnodup)
    have hsubset : (p.map (hat p)).toFinset ⊆ p.toFinset := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      exact List.mem_toFinset.mpr (hmem a ha)
    have hcard : (p.map (hat p)).toFinset.card = p.toFinset.card := by
      simp [List.card_toFinset, List.dedup_eq_self.mpr hmapNodup,
        List.dedup_eq_self.mpr hnodup]
    have heq : (p.map (hat p)).toFinset = p.toFinset :=
      Finset.eq_of_subset_of_card_le hsubset (by omega)
    have hperm : (p.map (hat p)).Perm p :=
      List.perm_of_nodup_nodup_toFinset_eq hmapNodup hnodup heq
    exact ((hp.symm.map _).trans hperm).trans hp
  have hBperm := B_perm q hq
  have hBlen : (B q).length = n := by simp [n]
  have hmem (i : ℕ) (hi : i < n) : q.getD i 0 ∈ q := by
    rw [List.getD_eq_getElem _ 0 hi]
    exact List.getElem_mem hi
  have hval (i : ℕ) (hi : i < n) : 0 < q.getD i 0 ∧ q.getD i 0 ≤ n := by
    obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hq.mem_iff.mp (hmem i hi))
    omega
  have hmax : ∀ y ∈ q, y ≤ q.getD 0 0 := by
    intro y hy
    obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hq.mem_iff.mp hy)
    omega
  have hgetidx (i : ℕ) (hi : i < n) : q.idxOf (q.getD i 0) = i := by
    rw [List.getD_eq_getElem _ 0 hi]
    simpa using (List.get_idxOf hnd ⟨i, hi⟩)
  have htpos : 1 < t := ht
  have htidx : q.idxOf t = n - 1 := hgetidx (n - 1) (by omega)
  have htn : t < n := by
    have hneq : t ≠ q.getD 0 0 := by
      intro heq
      have hval' : q[n - 1] = q[0] := by
        simpa only [← List.getD_eq_getElem _ 0 (by omega : n - 1 < q.length),
          ← List.getD_eq_getElem _ 0 (by omega : 0 < q.length)] using heq
      have := (hnd.getElem_inj_iff).mp hval'
      omega
    have hbound := (hval (n - 1) (by omega)).2
    omega
  have hcpos : 0 < c := (hval 1 (by omega)).1
  have hcn : c < n := by
    have hneq : c ≠ q.getD 0 0 := by
      intro heq
      have hval' : q[1] = q[0] := by
        simpa only [← List.getD_eq_getElem _ 0 (by omega : 1 < q.length),
          ← List.getD_eq_getElem _ 0 (by omega : 0 < q.length)] using heq
      have := (hnd.getElem_inj_iff).mp hval'
      omega
    have hbound := (hval 1 (by omega)).2
    omega
  have hBget (x : ℕ) (hx0 : 0 < x) (hxn : x ≤ n) :
      (B q).getD (x - 1) 0 = hat q x := by
    have hindex : x - 1 < n := by omega
    rw [List.getD_eq_getElem _ 0 (by simpa using hindex)]
    simp [List.getElem_range', Nat.add_sub_of_le hx0]
  have hhat_t : hat q t = n := by
    rw [hat_one_block q hmax t (hmem (n - 1) (by omega)), htidx,
      if_neg (by omega)]
    exact hfirst
  have hhat_n : hat q n = c := by
    have hidxn : q.idxOf n = 0 := by
      change q.idxOf q.length = 0
      rw [← hfirst]
      exact hgetidx 0 (by omega)
    have hnmem : n ∈ q := by
      change q.length ∈ q
      rw [← hfirst]
      exact hmem 0 (by omega)
    rw [hat_one_block q hmax n hnmem,
      hidxn, if_pos (by omega)]
  by_contra hc1
  have hcgt : 1 < c := by
    have hcne : c ≠ 1 := by simpa [c] using hc1
    omega
  have h1mem : 1 ∈ q := hq.mem_iff.mpr
    (List.mem_range'.mpr ⟨0, by omega, by simp⟩)
  have h1idx : q.idxOf 1 < n := List.idxOf_lt_length_of_mem h1mem
  have h1gt : 1 < q.idxOf 1 := by
    have hget : q.getD (q.idxOf 1) 0 = 1 := by
      rw [List.getD_eq_getElem _ 0 h1idx]
      exact List.getElem_idxOf h1idx
    by_contra hnot
    have hcase : q.idxOf 1 = 0 ∨ q.idxOf 1 = 1 := by omega
    rcases hcase with h0 | h1
    · rw [h0] at hget
      omega
    · rw [h1] at hget
      omega
  have h1next : q.idxOf 1 + 1 < n := by
    by_contra hnot
    have heq : q.idxOf 1 = n - 1 := by omega
    have hget : q.getD (q.idxOf 1) 0 = 1 := by
      rw [List.getD_eq_getElem _ 0 h1idx]
      exact List.getElem_idxOf h1idx
    rw [heq] at hget
    omega
  let v := q.getD (q.idxOf 1 + 1) 0
  have hhat_1 : hat q 1 = v := by
    rw [hat_one_block q hmax 1 h1mem, if_pos h1next]
  have hvpos : 0 < v := (hval _ h1next).1
  have hvne : v ≠ c := by
    intro heq
    have hval' : q[q.idxOf 1 + 1] = q[1] := by
      simpa only [← List.getD_eq_getElem _ 0 h1next,
        ← List.getD_eq_getElem _ 0 (by omega : 1 < q.length)] using heq
    have := (hnd.getElem_inj_iff).mp hval'
    omega
  have hcv : c < v := by
    by_contra hnot
    have hvc : v < c := by omega
    apply havoidB
    apply (contains132_iff_indices (B q)).mpr
    refine ⟨⟨0, by omega⟩, ⟨t - 1, by omega⟩, ⟨n - 1, by omega⟩,
      by simp; omega, by simp; omega, ?_, ?_⟩
    · have h := hvc
      rw [← hhat_1, ← hhat_n, ← hBget 1 (by omega) (by omega),
        ← hBget n (by omega) (by omega)] at h
      simpa only [List.getD_eq_getElem _ 0 (by omega : 0 < (B q).length),
        List.getD_eq_getElem _ 0 (by omega : n - 1 < (B q).length)] using h
    · have h' : hat q n < hat q t := by rw [hhat_n, hhat_t]; exact hcn
      rw [← hBget n (by omega) (by omega),
        ← hBget t (by omega) (by omega)] at h'
      simpa only [List.getD_eq_getElem _ 0 (by omega : n - 1 < (B q).length),
        List.getD_eq_getElem _ 0 (by omega : t - 1 < (B q).length)] using h'
  have hvt : v ≤ t := by
    by_cases hlast : q.idxOf 1 + 1 = n - 1
    · have h : v = t := by simp [v, t, hlast]
      omega
    · have hinc := suffix_after_one_increasing q hq havoidq
        (q.idxOf 1) (q.idxOf 1 + 1) (n - 1)
        (by omega) (by omega) (by omega)
        (by rw [List.getD_eq_getElem _ 0 h1idx]; exact List.getElem_idxOf h1idx)
      change v < t at hinc
      omega
  have hct : c < t := by omega
  have hlast : t = n - 1 := by
    by_contra hne
    let y := t + 1
    have hyn : y < n := by omega
    have hymem : y ∈ q := hq.mem_iff.mpr
      (List.mem_range'.mpr ⟨y - 1, by omega, by omega⟩)
    have hyidx : q.idxOf y < n := List.idxOf_lt_length_of_mem hymem
    have hyget : q.getD (q.idxOf y) 0 = y := by
      rw [List.getD_eq_getElem _ 0 hyidx]
      exact List.getElem_idxOf hyidx
    have hybefore : q.idxOf y < q.idxOf 1 := by
      by_contra hnot
      have hne1 : q.idxOf y ≠ q.idxOf 1 := by
        intro heq
        rw [heq] at hyget
        have hget1 : q.getD (q.idxOf 1) 0 = 1 := by
          rw [List.getD_eq_getElem _ 0 h1idx]
          exact List.getElem_idxOf h1idx
        omega
      have hafter : q.idxOf 1 < q.idxOf y := by omega
      by_cases heq : q.idxOf y = n - 1
      · rw [heq] at hyget
        omega
      · have hinc := suffix_after_one_increasing q hq havoidq
          (q.idxOf 1) (q.idxOf y) (n - 1)
          hafter (by omega) (by omega)
          (by rw [List.getD_eq_getElem _ 0 h1idx]; exact List.getElem_idxOf h1idx)
        rw [hyget] at hinc
        change y < t at hinc
        omega
    have hyafter : 1 < q.idxOf y := by
      by_contra hnot
      have hcase : q.idxOf y = 0 ∨ q.idxOf y = 1 := by omega
      rcases hcase with h0 | h1
      · rw [h0, hfirst] at hyget
        omega
      · rw [h1] at hyget
        omega
    apply havoidq
    apply (contains132_iff_indices q).mpr
    refine ⟨⟨1, by omega⟩, ⟨q.idxOf y, hyidx⟩, ⟨n - 1, by omega⟩,
      by simp; omega, by simp; omega, ?_, ?_⟩
    · simpa only [← List.getD_eq_getElem _ 0 (by omega : 1 < q.length),
        ← List.getD_eq_getElem _ 0 (by omega : n - 1 < q.length)] using hct
    · have hty : t < y := by omega
      rw [← hyget] at hty
      simpa only [← List.getD_eq_getElem _ 0 (by omega : n - 1 < q.length),
        ← List.getD_eq_getElem _ 0 hyidx] using hty
  have hB1mem : 1 ∈ B q := hBperm.mem_iff.mpr
    (List.mem_range'.mpr ⟨0, by omega, by simp⟩)
  have hB1idx : (B q).idxOf 1 < n := by
    simpa [hBlen] using List.idxOf_lt_length_of_mem hB1mem
  have hB1val : (B q).getD ((B q).idxOf 1) 0 = 1 := by
    rw [List.getD_eq_getElem _ 0 (by simpa [hBlen] using hB1idx)]
    exact List.getElem_idxOf (by simpa [hBlen] using hB1idx)
  have hB1before : (B q).idxOf 1 < t - 1 := by
    have hBt : (B q).getD (t - 1) 0 = n := by rw [hBget t (by omega) (by omega), hhat_t]
    have hBn : (B q).getD (n - 1) 0 = c := by rw [hBget n (by omega) (by omega), hhat_n]
    by_contra hnot
    have hcase : (B q).idxOf 1 = t - 1 ∨ (B q).idxOf 1 = n - 1 := by omega
    rcases hcase with heq | heq
    · rw [heq] at hB1val
      omega
    · rw [heq] at hB1val
      omega
  apply havoidB
  apply (contains132_iff_indices (B q)).mpr
  refine ⟨⟨(B q).idxOf 1, by simpa [hBlen] using hB1idx⟩,
    ⟨t - 1, by omega⟩, ⟨n - 1, by omega⟩,
    by simp; omega, by simp; omega, ?_, ?_⟩
  · have hBn : (B q).getD (n - 1) 0 = c := by rw [hBget n (by omega) (by omega), hhat_n]
    have h : (B q).getD ((B q).idxOf 1) 0 < (B q).getD (n - 1) 0 := by
      rw [hB1val, hBn]
      omega
    have hconvert : (B q).getD ((B q).idxOf 1) 0 =
        (B q)[(B q).idxOf 1] :=
      List.getD_eq_getElem _ 0 (by simpa [hBlen] using hB1idx)
    rw [hconvert] at h
    simpa only [
      List.getD_eq_getElem _ 0 (by omega : n - 1 < (B q).length)] using h
  · have hBn : (B q).getD (n - 1) 0 = c := by rw [hBget n (by omega) (by omega), hhat_n]
    have hBt : (B q).getD (t - 1) 0 = n := by rw [hBget t (by omega) (by omega), hhat_t]
    have h : (B q).getD (n - 1) 0 < (B q).getD (t - 1) 0 := by
      rw [hBn, hBt]
      omega
    simpa only [← List.getD_eq_getElem _ 0 (by omega : n - 1 < (B q).length),
      ← List.getD_eq_getElem _ 0 (by omega : t - 1 < (B q).length)] using h

end D5.S3.Combinatorics.FundamentalBijection.ThetaIteratePosition
