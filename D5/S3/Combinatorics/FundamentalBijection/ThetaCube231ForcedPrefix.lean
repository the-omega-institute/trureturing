/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaCube231ForcedPrefix
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaCube231ForcedPrefix
   mirror-E: none(waiver:forced-prefix-in-231-chase)
   anchors: [mathlib/module/Mathlib.Data.List.Sort]
   utility: none
   digest: A 231-avoider with the terminal-value adjacency has a forced high prefix. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Prefix
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaCube231ForcedPrefix

open ThetaBasicInverse ThetaCube231Prefix

/-- The prefix before `1` is the decreasing interval from `n` down to
`c+1`, forced by 231 avoidance and the adjacent `c+1,1` pair. -/
theorem forced_high_prefix (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length))
    (havoid : ¬ D5.S3.Combinatorics.ArrowWilfDefs.Contains [2, 3, 1] [] 3 p)
    (t c : ℕ) (ht : 0 < t) (htlast : t < p.length - 1)
    (hone : p.getD t 0 = 1)
    (hpred : p.getD (t - 1) 0 = c + 1)
    (hlast : p.getD (p.length - 1) 0 = c) :
    p.take t = (List.range' (c + 1) (p.length - c)).reverse := by
  have hcontains231 (p : List ℕ) :
      D5.S3.Combinatorics.ArrowWilfDefs.Contains [2, 3, 1] [] 3 p ↔
        ∃ i j k : Fin p.length, i < j ∧ j < k ∧ p[j.val] > p[i.val] ∧
        p[i.val] > p[k.val] := by
    constructor
    · rintro ⟨x, hlt, _, hsub, _⟩
      change List.Sublist [x 2, x 3, x 1] p at hsub
      obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      have h0 : p[(f ⟨0, by simp⟩).val] = x 2 := by
        simpa using (hf ⟨0, by simp⟩).symm
      have h1 : p[(f ⟨1, by simp⟩).val] = x 3 := by
        simpa using (hf ⟨1, by simp⟩).symm
      have h2 : p[(f ⟨2, by simp⟩).val] = x 1 := by
        simpa using (hf ⟨2, by simp⟩).symm
      refine ⟨f ⟨0, by simp⟩, f ⟨1, by simp⟩, f ⟨2, by simp⟩,
        f.strictMono (by simp), f.strictMono (by simp), ?_, ?_⟩
      · simpa only [← h1, ← h0] using hlt 2 (by omega) (by omega)
      · simpa only [← h0, ← h2] using hlt 1 (by omega) (by omega)
    · rintro ⟨i, j, k, hij, hjk, hji, hik⟩
      let x : ℕ → ℕ := fun t => if t = 1 then p[k.val] else if t = 2 then p[i.val]
        else p[j.val]
      have hx1 : x 1 = p[k.val] := by simp [x]
      have hx2 : x 2 = p[i.val] := by simp [x]
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
        rcases h with rfl | rfl <;> simp [hx1, hx2, hx3, hik, hji]
      · intro t ht ht3
        have h : t = 1 ∨ t = 2 ∨ t = 3 := by omega
        rcases h with rfl | rfl | rfl <;> simp [hx1, hx2, hx3]
      · simpa [hx1, hx2, hx3] using hsub
  have hn : 0 < p.length := by omega
  have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hidx1 : p.idxOf 1 = t := by
    have hit : t < p.length := by omega
    have hget : p[t] = 1 := by
      exact (List.getD_eq_getElem p 0 hit).symm.trans hone
    have hidx := hnodup.idxOf_getElem (i := t) hit
    rw [hget] at hidx
    exact hidx
  have hbound (x : ℕ) (hx : x ∈ p) : 1 ≤ x ∧ x ≤ p.length := by
    obtain ⟨i, hi, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hx)
    omega
  have hsorted : (p.take t).SortedGT := by
    apply List.sortedGT_iff_getElem_gt_getElem_of_lt.mpr
    intro i j hi hj hji
    have hitake : i < t := by
      have hi' : i < min t p.length := by simpa using hi
      exact (Nat.lt_min.mp hi').1
    have hjtake : j < t := by
      have hj' : j < min t p.length := by simpa using hj
      exact (Nat.lt_min.mp hj').1
    have h := avoid231_prefix_before_one_decreasing p hp hn havoid
      j i hji (by omega : i < p.idxOf 1)
    simpa only [List.getElem_take,
      List.getD_eq_getElem _ 0 (by omega : i < p.length),
      List.getD_eq_getElem _ 0 (by omega : j < p.length)] using h
  have hmem (x : ℕ) : x ∈ p.take t ↔ x ∈ List.range' (c + 1) (p.length - c) := by
    constructor
    · intro hx
      have hxp : x ∈ p := List.mem_of_mem_take hx
      have hi : p.idxOf x < t := (List.mem_take_iff_idxOf_lt hxp).mp hx
      have hidxlt : p.idxOf x < p.length := List.idxOf_lt_length_of_mem hxp
      have hvalue : p.getD (p.idxOf x) 0 = x := by
        rw [List.getD_eq_getElem _ 0 hidxlt]
        exact List.getElem_idxOf hidxlt
      have hlow : c + 1 ≤ x := by
        by_cases heq : p.idxOf x = t - 1
        · rw [heq, hpred] at hvalue
          omega
        · have hlt : p.idxOf x < t - 1 := by omega
          have h := avoid231_prefix_before_one_decreasing p hp hn havoid
            (p.idxOf x) (t - 1) hlt (by omega : t - 1 < p.idxOf 1)
          rw [hvalue, hpred] at h
          omega
      have hupp := (hbound x hxp).2
      apply List.mem_range'.mpr
      refine ⟨x - (c + 1), ?_, by omega⟩
      omega
    · intro hx
      obtain ⟨i, hi, heq⟩ := List.mem_range'.mp hx
      have hbounds : c + 1 ≤ x ∧ x ≤ p.length := by omega
      have hxp : x ∈ p := hp.mem_iff.mpr
        (List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩)
      by_cases heq' : x = c + 1
      · have hpos : t - 1 < p.length := by omega
        have hval : p[t - 1] = x := by
          exact (List.getD_eq_getElem p 0 hpos).symm.trans (by simpa [heq'] using hpred)
        have htake : t - 1 < (p.take t).length := by simp; omega
        have hmem : x ∈ p.take t := by
          have h := List.getElem_mem (l := p.take t) htake
          simpa only [List.getElem_take, hval] using h
        exact hmem
      · have hbefore : p.idxOf x < t := by
          have hi : p.idxOf x < p.length := List.idxOf_lt_length_of_mem hxp
          have hvalue : p.getD (p.idxOf x) 0 = x := by
            rw [List.getD_eq_getElem _ 0 hi]
            exact List.getElem_idxOf hi
          have hnotOne : p.idxOf x ≠ t := by
            intro heq
            rw [heq, hone] at hvalue
            omega
          have hnotLast : p.idxOf x ≠ p.length - 1 := by
            intro heq
            rw [heq, hlast] at hvalue
            omega
          by_contra hnotBefore
          have hmiddle : t < p.idxOf x := by omega
          have hbeforeLast : p.idxOf x < p.length - 1 := by omega
          apply havoid
          apply (hcontains231 p).mpr
          refine ⟨⟨t - 1, by omega⟩, ⟨p.idxOf x, hi⟩,
            ⟨p.length - 1, by omega⟩, ?_, hbeforeLast, ?_, ?_⟩
          · change t - 1 < p.idxOf x
            omega
          · rw [← List.getD_eq_getElem _ 0 hi,
              ← List.getD_eq_getElem _ 0 (by omega : t - 1 < p.length),
              hvalue, hpred]
            omega
          · rw [← List.getD_eq_getElem _ 0 (by omega : t - 1 < p.length),
              ← List.getD_eq_getElem _ 0 (by omega : p.length - 1 < p.length),
              hpred, hlast]
            omega
        exact (List.mem_take_iff_idxOf_lt hxp).mpr hbefore
  have hrange : (List.range' (c + 1) (p.length - c)).SortedLT :=
    List.sortedLT_range' (c + 1) (p.length - c) (s := 1) (by decide)
  exact List.SortedGT.eq_reverse_of_mem_iff_of_sortedLT hmem hsorted hrange

end D5.S3.Combinatorics.FundamentalBijection.ThetaCube231ForcedPrefix
