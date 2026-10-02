/- GID: D5/S3/Combinatorics/Fishburn/FishburnBasicSmallValues
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnBasicSmallValues
   mirror-E: none(waiver:descending-predecessor-chain)
   anchors: [mathlib/module/Mathlib.Data.List.NodupEquivFin]
   utility: none
   digest: Eligible 213-free Fishburn prefixes contain their ordered lower values. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicAscents
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnBasicSmallValues

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicAscents

theorem small_value_chain (n : ℕ) (p : List ℕ)
    (hperm : p.Perm (List.range' 1 n)) (hfish : IsFishburn p)
    (last : ℕ) (hlast : last < p.length)
    (havoid : ¬ NonnestingDefs.Occurs [2, 1, 3] (p.take (last + 1)))
    (hpred : ∀ earlier, earlier < p.length →
      p.getD earlier 0 + 1 = p.getD last 0 → earlier < last) :
    (∀ index, index < p.length → p.getD index 0 ≤ p.getD last 0 → index ≤ last) ∧
    (∀ first second, first < p.length → second < p.length →
      p.getD first 0 < p.getD second 0 → p.getD second 0 ≤ p.getD last 0 →
      first < second) := by
  have hnodup : p.Nodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
  have hvalues (index : ℕ) (hi : index < p.length) :
      1 ≤ p.getD index 0 ∧ p.getD index 0 ≤ n := by
    have hm : p.getD index 0 ∈ p := by
      rw [List.getD_eq_getElem p 0 hi]
      exact List.getElem_mem hi
    have hr := hperm.mem_iff.mp hm
    simp only [List.mem_range', Nat.one_mul] at hr
    obtain ⟨offset, ho, hv⟩ := hr
    omega
  have hmember (value : ℕ) (hl : 1 ≤ value) (hh : value ≤ n) :
      ∃ index, index < p.length ∧ p.getD index 0 = value := by
    have hm : value ∈ p := by
      apply hperm.mem_iff.mpr
      simp only [List.mem_range', Nat.one_mul]
      exact ⟨value - 1, by omega, by omega⟩
    obtain ⟨index, hi, hv⟩ := List.mem_iff_getElem.mp hm
    exact ⟨index, hi, by rw [List.getD_eq_getElem p 0 hi, hv]⟩
  have hselected : ∀ (word : List ℕ) (positions : List ℕ),
      positions.Pairwise (· < ·) → (∀ index ∈ positions, index < word.length) →
      (positions.map (fun index => word.getD index 0)).Sublist word := by
    intro word positions ho hb
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    let select : Fin (positions.map (fun index => word.getD index 0)).length →
        Fin word.length := fun index =>
      ⟨positions[index.val]'(by simpa using index.is_lt),
        hb _ (List.getElem_mem (by simpa using index.is_lt))⟩
    have hmono : StrictMono select := by
      intro first second hlt
      exact List.pairwise_iff_getElem.mp ho first.val second.val
        (by simpa using first.is_lt) (by simpa using second.is_lt) hlt
    refine ⟨OrderEmbedding.ofStrictMono select hmono, ?_⟩
    intro index
    simp only [List.get_eq_getElem, List.getElem_map, OrderEmbedding.coe_ofStrictMono]
    exact List.getD_eq_getElem word 0 _
  have htake (index : ℕ) (hi : index ≤ last) :
      (p.take (last + 1)).getD index 0 = p.getD index 0 := by
    rw [List.getD_eq_getElem _ 0 (by simp only [List.length_take]; omega),
      List.getElem_take, List.getD_eq_getElem p 0 (by omega)]
  have hchain : ∀ gap value, gap = p.getD last 0 - value → 1 ≤ value →
      value ≤ p.getD last 0 →
      ∃ index, index ≤ last ∧ p.getD index 0 = value ∧
        (∀ earlier, earlier < p.length → p.getD earlier 0 + 1 = value →
          earlier < index) := by
    intro gap
    induction gap using Nat.strong_induction_on with
    | h gap ih =>
      intro value hgap hv htop
      by_cases heq : value = p.getD last 0
      · exact ⟨last, le_rfl, heq.symm, by simpa [heq] using hpred⟩
      · obtain ⟨next, hn, hnvalue, hnpredecessor⟩ :=
          ih (p.getD last 0 - (value + 1)) (by omega) (value + 1) rfl (by omega) (by omega)
        obtain ⟨index, hi, hvalue⟩ := hmember value hv (by have := hvalues last hlast; omega)
        have hindexnext : index < next := hnpredecessor index hi (by omega)
        have hindexlast : index < last := by omega
        have hascent : p.getD index 0 < p.getD (index + 1) 0 := by
          rcases lt_trichotomy (p.getD index 0) (p.getD (index + 1) 0) with
            hlt | hequal | hgt
          · exact hlt
          · have := (List.getD_inj hi (by omega) hnodup).mp hequal
            omega
          · have hnextlast : index + 1 < last := by
              by_contra hnot
              have hequal : index + 1 = last := by omega
              rw [hequal] at hgt
              omega
            apply False.elim
            apply havoid
            change ArrowWilfDefs.Contains [2, 1, 3] [] 3 (p.take (last + 1))
            let values : ℕ → ℕ := fun rank =>
              if rank = 1 then p.getD (index + 1) 0
              else if rank = 2 then value else p.getD last 0
            have hs := hselected (p.take (last + 1)) [index, index + 1, last]
              (by simp [List.pairwise_cons]; omega) (by
                intro pos hp
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                rcases hp with rfl | rfl | rfl <;> simp only [List.length_take] <;> omega)
            rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil,
              htake index (by omega), htake (index + 1) (by omega), htake last le_rfl,
              hvalue] at hs
            refine ⟨values, ?_, ?_, ?_, by simp⟩
            · intro rank hl hh
              have hc : rank = 1 ∨ rank = 2 := by omega
              rcases hc with rfl | rfl <;>
                simp only [values, ↓reduceIte, Nat.reduceAdd, Nat.reduceEqDiff] <;> omega
            · intro rank hl hh
              have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
              rcases hc with rfl | rfl | rfl <;> apply hs.subset <;> simp [values]
            · simpa only [List.map_cons, List.map_nil, values, ↓reduceIte,
                Nat.reduceEqDiff] using hs
        refine ⟨index, by omega, hvalue, ?_⟩
        intro earlier hearlier hpredvalue
        have hfb := (isFishburn_iff_ascent_predecessor n p hperm).mp hfish index
          (by omega) hascent
        rcases hfb with hone | ⟨previous, hp, hpvalue⟩
        · have hpositive := (hvalues earlier hearlier).1
          omega
        · have hequal : p.getD earlier 0 = p.getD previous 0 := by omega
          have := (List.getD_inj hearlier (by omega) hnodup).mp hequal
          omega
  have hposition (index : ℕ) (hi : index < p.length)
      (hh : p.getD index 0 ≤ p.getD last 0) :
      index ≤ last ∧ ∀ earlier, earlier < p.length →
        p.getD earlier 0 + 1 = p.getD index 0 → earlier < index := by
    obtain ⟨chosen, hc, hv, hp⟩ := hchain (p.getD last 0 - p.getD index 0)
      (p.getD index 0) rfl (hvalues index hi).1 hh
    have heq := (List.getD_inj (by omega) hi hnodup).mp hv
    subst chosen
    exact ⟨hc, hp⟩
  constructor
  · intro index hi hh
    exact (hposition index hi hh).1
  · have horder : ∀ value, value ≤ p.getD last 0 → ∀ second, second < p.length →
        p.getD second 0 = value → ∀ first, first < p.length →
          p.getD first 0 < value → first < second := by
      intro value
      induction value using Nat.strong_induction_on with
      | h value ih =>
        intro hv second hs hsvalue first hf hlt
        have hpositive := (hvalues first hf).1
        obtain ⟨previous, hp, hpvalue⟩ := hmember (value - 1) (by omega)
          (by have := hvalues second hs; omega)
        have hprevious := (hposition second hs (by omega)).2 previous hp (by omega)
        by_cases heq : p.getD first 0 = value - 1
        · have := (List.getD_inj hf hp hnodup).mp (heq.trans hpvalue.symm)
          omega
        · have hbefore := ih (value - 1) (by omega) (by omega) previous hp hpvalue first hf
            (by omega)
          omega
    intro first second hf hs hlt hh
    exact horder (p.getD second 0) hh second hs rfl first hf hlt

end D5.S3.Combinatorics.Fishburn.FishburnBasicSmallValues
