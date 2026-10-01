/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateShortCycle
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateShortCycle
   mirror-E: none(waiver:first-endpoint-three-cycle-obstruction)
   anchors: []
   utility: none
   digest: A final cycle containing the two largest letters and one obstructs 132 avoidance. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateShortCycle

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseTail
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords

theorem second_to_penultimate_forces_one_block (q : List ℕ)
    (hq : q.Perm (List.range' 1 q.length)) (hsize : 4 ≤ q.length)
    (havoid : ¬ Contains [1, 3, 2] [] 3 q)
    (hfirst : hat q 1 = q.length)
    (hsecond : hat q 2 = q.length - 1)
    (hmax : 1 < hat q q.length) :
    hat q (q.length - 1) = 1 ∧ q.getD 0 0 = q.length := by
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

  let h := q.length
  change 1 < hat q h at hmax
  have hnd : q.Nodup := hq.nodup_iff.mpr List.nodup_range'
  have hval (i : ℕ) (hi : i < h) : 1 ≤ q.getD i 0 ∧ q.getD i 0 ≤ h := by
    have hm : q.getD i 0 ∈ q := by
      rw [List.getD_eq_getElem _ 0 hi]
      exact List.getElem_mem hi
    obtain ⟨j, hj, heq⟩ := List.mem_range'.mp (hq.mem_iff.mp hm)
    omega
  have hinj (i j : ℕ) (hi : i < h) (hj : j < h)
      (heq : q.getD i 0 = q.getD j 0) : i = j := by
    rw [List.getD_eq_getElem _ 0 hi, List.getD_eq_getElem _ 0 hj] at heq
    exact hnd.getElem_inj_iff.mp heq
  have hlast : q.getD (h - 1) 0 = 1 := by
    apply B_first_max_forces_last_one q hq (by omega)
    rw [List.getD_eq_getElem _ 0 (by simp; omega)]
    simpa using hfirst
  have hm : h ∈ q := hq.mem_iff.mpr
    (List.mem_range'.mpr ⟨h - 1, by omega, by omega⟩)
  let s := q.idxOf h
  have hslen : s < h := List.idxOf_lt_length_of_mem hm
  have hsval : q.getD s 0 = h := by
    rw [List.getD_eq_getElem _ 0 hslen]
    exact List.getElem_idxOf hslen
  have hsrec : IsLtrMax q s := by
    intro j hjs
    have hjlen : j < h := by omega
    have hv := hval j hjlen
    have hne : q.getD j 0 ≠ h := by
      intro heq
      have := hinj j s hjlen hslen (heq.trans hsval.symm)
      omega
    omega
  have hnon : ∀ j, s < j → j < h → ¬ IsLtrMax q j := by
    intro j hsj hj hrec
    have hv := hval j hj
    have hlt := hrec s hsj
    omega
  have hsnext : s + 1 < h := by
    have hne : s ≠ h - 1 := by intro heq; rw [heq, hlast] at hsval; omega
    omega
  have hblock (i : ℕ) (hsi : s ≤ i) (hin : i + 1 < h) :
      hat q (q.getD i 0) = q.getD (i + 1) 0 := by
    have hidx : q.idxOf (q.getD i 0) = i := by
      rw [List.getD_eq_getElem _ 0 (by omega)]
      simpa using List.get_idxOf hnd ⟨i, by omega⟩
    unfold hat
    rw [hidx, if_pos ⟨hin, hnon _ (by omega) hin⟩]
  have hc : q.getD (s + 1) 0 = hat q h := by
    have hedge := hblock s (le_refl _) hsnext
    rw [hsval] at hedge
    exact hedge.symm
  have htwo : 2 ∈ q := hq.mem_iff.mpr
    (List.mem_range'.mpr ⟨1, by omega, by omega⟩)
  let u := q.idxOf 2
  have hulen : u < h := List.idxOf_lt_length_of_mem htwo
  have huval : q.getD u 0 = 2 := by
    rw [List.getD_eq_getElem _ 0 hulen]
    exact List.getElem_idxOf hulen
  have hsu : s < u := by
    by_cases heq : q.getD (s + 1) 0 = 2
    · have := hinj (s + 1) u hsnext hulen (heq.trans huval.symm)
      omega
    · exact final_tail_downward_closed q hq havoid s (s + 1) 2 (by omega)
        hsnext hsrec hnon htwo (by omega)
  have hunext : u + 1 < h := by
    have hne : u ≠ h - 1 := by intro heq; rw [heq, hlast] at huval; omega
    omega
  have hnext : q.getD (u + 1) 0 = h - 1 := by
    have hedge := hblock u (by omega) hunext
    rw [huval] at hedge
    exact hedge.symm.trans hsecond
  have hunnext : u + 2 < h := by
    have hne : u + 1 ≠ h - 1 := by intro heq; rw [heq, hlast] at hnext; omega
    omega
  have hufinal : u + 2 = h - 1 := by
    by_contra hnot
    have hbefore : u + 2 < h - 1 := by omega
    have hv := hval (u + 2) hunnext
    have hvne1 : q.getD (u + 2) 0 ≠ 1 := by
      intro heq
      have := hinj (u + 2) (h - 1) hunnext (by omega) (heq.trans hlast.symm)
      omega
    have hvne2 : q.getD (u + 2) 0 ≠ 2 := by
      intro heq
      have := hinj (u + 2) u hunnext hulen (heq.trans huval.symm)
      omega
    have hvneh : q.getD (u + 2) 0 ≠ h := by
      intro heq
      have := hinj (u + 2) s hunnext hslen (heq.trans hsval.symm)
      omega
    have hvnepred : q.getD (u + 2) 0 ≠ h - 1 := by
      intro heq
      have := hinj (u + 2) (u + 1) hunnext hunext (heq.trans hnext.symm)
      omega
    apply havoid
    apply (contains132_iff_indices q).mpr
    refine ⟨⟨u, hulen⟩, ⟨u + 1, hunext⟩, ⟨u + 2, hunnext⟩,
      by simp, by simp, ?_, ?_⟩
    · have hlt : q.getD u 0 < q.getD (u + 2) 0 := by omega
      simpa only [← List.getD_eq_getElem _ 0 hulen,
        ← List.getD_eq_getElem _ 0 hunnext] using hlt
    · have hlt : q.getD (u + 2) 0 < q.getD (u + 1) 0 := by omega
      simpa only [← List.getD_eq_getElem _ 0 hunnext,
        ← List.getD_eq_getElem _ 0 hunext] using hlt
  have hpred : hat q (h - 1) = 1 := by
    have hedge := hblock (u + 1) (by omega) (by omega)
    rw [hnext, show u + 1 + 1 = h - 1 by omega, hlast] at hedge
    exact hedge
  refine ⟨hpred, ?_⟩
  have hs0 : s = 0 := by
    by_contra hnot
    have hv := hval 0 (by omega)
    have hvneh : q.getD 0 0 ≠ h := by
      intro heq
      have := hinj 0 s (by omega) hslen (heq.trans hsval.symm)
      omega
    have hvnepred : q.getD 0 0 ≠ h - 1 := by
      intro heq
      have := hinj 0 (u + 1) (by omega) hunext (heq.trans hnext.symm)
      omega
    have hvsmall : q.getD 0 0 < q.getD (u + 1) 0 := by omega
    have hvindex : q.idxOf (q.getD 0 0) = 0 := by
      rw [List.getD_eq_getElem _ 0 (by omega)]
      simpa using List.get_idxOf hnd ⟨0, by omega⟩
    have hvafter := final_tail_downward_closed q hq havoid s (u + 1) (q.getD 0 0)
      (by omega) hunext hsrec hnon
      (by rw [List.getD_eq_getElem _ 0 (by omega)]; exact List.getElem_mem _) hvsmall
    omega
  simpa only [hs0] using hsval

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateShortCycle
