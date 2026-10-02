/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenElevenClassicalPairs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenElevenClassicalPairs
   mirror-E: none(waiver:exceptional-classical-block-recovery)
   anchors: [mathlib/module/Mathlib.Data.List.Sort]
   utility: none
   digest: Every extra classical insertion cut recovers its unique descending-block pair. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenElevenClassicalSites
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenElevenClassicalPairs

open D5.S3.Combinatorics Nonnesting FishburnClassicalDefs FishburnTenElevenClassicalSites

theorem exceptional_pair_recovery (n : ℕ) (p : List ℕ)
    (hparent : p ∈ classicalAvoiders n [[1, 2, 3], [3, 2, 4, 1]])
    (site : ℕ) (hsite : site ≤ p.length) (hextra : 2 ≤ site)
    (hactive : p.insertIdx site (n + 1) ∈
      classicalAvoiders (n + 1) [[1, 2, 3], [3, 2, 4, 1]]) :
    1 ≤ p.getD 1 0 ∧ p.getD 1 0 < p.getD 0 0 ∧ p.getD 0 0 ≤ n ∧
    site = p.getD 1 0 + 1 ∧
    p = p.getD 0 0 :: (List.range' 1 (p.getD 1 0)).reverse ++
      ((List.range' (p.getD 1 0 + 1) (n - p.getD 1 0)).reverse).erase (p.getD 0 0) := by
  have hperm := hparent.1
  have hnodup : p.Nodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
  have hlen : p.length = n := by simpa using hperm.length_eq
  obtain hsmall | ⟨hprefix, htail⟩ := (classical_active_sites n p hparent site hsite).mp hactive
  · omega
  have hdec (first second : ℕ) (hfs : first < second) (hs : second < site) :
      p.getD second 0 < p.getD first 0 := by
    have hh := List.pairwise_iff_getElem.mp hprefix first second
      (by simp only [List.length_take]; omega) (by simp only [List.length_take]; omega) hfs
    rw [List.getD_eq_getElem p 0 (by omega), List.getD_eq_getElem p 0 (by omega)]
    simpa only [List.getElem_take] using hh
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
  let low := (p.take site).drop 1
  let high := p.drop site
  have hlowlen : low.length = site - 1 := by
    simp only [low, List.length_drop, List.length_take]
    omega
  have hlowentry (index : ℕ) (hi : index < low.length) :
      low.getD index 0 = p.getD (index + 1) 0 := by
    rw [List.getD_eq_getElem low 0 hi, List.getD_eq_getElem p 0 (by omega)]
    simp only [low, List.getElem_drop, List.getElem_take, Nat.add_comm]
  have hhighentry (index : ℕ) (hi : index < high.length) :
      high.getD index 0 = p.getD (site + index) 0 := by
    rw [List.getD_eq_getElem high 0 hi,
      List.getD_eq_getElem p 0 (by simp only [high, List.length_drop] at hi; omega)]
    simp only [high, List.getElem_drop]
  have hm := hvalues 1 (by omega)
  have hk := hvalues 0 (by omega)
  have hmk := hdec 0 1 (by omega) (by omega)
  have hlowmem (value : ℕ) : value ∈ low ↔ 1 ≤ value ∧ value ≤ p.getD 1 0 := by
    constructor
    · intro hv
      obtain ⟨index, hi, hv⟩ := List.mem_iff_getElem.mp hv
      have he : p.getD (index + 1) 0 = value := by
        rw [← hlowentry index hi, List.getD_eq_getElem low 0 hi, hv]
      have hb := (hvalues (index + 1) (by omega)).1
      by_cases hzero : index = 0
      · subst index
        simp only [Nat.zero_add] at he
        omega
      · have := hdec 1 (index + 1) (by omega) (by omega)
        omega
    · rintro ⟨hl, hh⟩
      obtain ⟨index, hi, he⟩ := hmember value hl (by omega)
      have hbefore : index < site := by
        by_contra hnot
        have := htail index (by omega) hi
        omega
      have hpositive : 0 < index := by
        by_contra hnot
        have hzero : index = 0 := by omega
        rw [hzero] at he
        omega
      apply List.mem_iff_getElem.mpr
      refine ⟨index - 1, by omega, ?_⟩
      have hentry := hlowentry (index - 1) (by omega)
      rw [List.getD_eq_getElem low 0 (by omega)] at hentry
      have hequal : index - 1 + 1 = index := by omega
      rw [hequal] at hentry
      exact hentry.trans he
  have hloworder : low.Pairwise (· > ·) := hprefix.drop
  have hrangeorder (start count : ℕ) :
      (List.range' start count).reverse.Pairwise (· > ·) := by
    rw [List.pairwise_reverse]
    exact List.pairwise_lt_range'
  have hloweq : low = (List.range' 1 (p.getD 1 0)).reverse := by
    apply hloworder.eq_of_mem_iff (hrangeorder 1 (p.getD 1 0))
    intro value
    rw [hlowmem, List.mem_reverse]
    simp only [List.mem_range', Nat.one_mul]
    constructor
    · rintro ⟨hl, hh⟩
      exact ⟨value - 1, by omega, by omega⟩
    · rintro ⟨offset, ho, hv⟩
      omega
  have hsitevalue : site = p.getD 1 0 + 1 := by
    have he := congrArg List.length hloweq
    simp only [List.length_reverse, List.length_range'] at he
    omega
  have hhighmem (value : ℕ) : value ∈ high ↔
      p.getD 1 0 < value ∧ value ≤ n ∧ value ≠ p.getD 0 0 := by
    constructor
    · intro hv
      obtain ⟨index, hi, hv⟩ := List.mem_iff_getElem.mp hv
      have hb : site + index < p.length := by
        simp only [high, List.length_drop] at hi
        omega
      have he : p.getD (site + index) 0 = value := by
        rw [← hhighentry index hi, List.getD_eq_getElem high 0 hi, hv]
      refine ⟨by have := htail (site + index) (by omega) hb; omega,
        by have := (hvalues (site + index) hb).2; omega, ?_⟩
      intro heq
      have hindex := (List.getD_inj hb (by omega) hnodup).mp (he.trans heq)
      omega
    · rintro ⟨hl, hh, hne⟩
      obtain ⟨index, hi, he⟩ := hmember value (by omega) hh
      have hafter : site ≤ index := by
        by_contra hnot
        by_cases hzero : index = 0
        · subst index
          exact hne he.symm
        · by_cases hone : index = 1
          · subst index
            omega
          · have := hdec 1 index (by omega) (by omega)
            omega
      apply List.mem_iff_getElem.mpr
      refine ⟨index - site, by simp only [high, List.length_drop]; omega, ?_⟩
      have hentry := hhighentry (index - site)
        (by simp only [high, List.length_drop]; omega)
      rw [List.getD_eq_getElem high 0 (by simp only [high, List.length_drop]; omega)]
        at hentry
      have hequal : site + (index - site) = index := by omega
      rw [hequal] at hentry
      exact hentry.trans he
  have hselected : ∀ (positions : List ℕ), positions.Pairwise (· < ·) →
      (∀ index ∈ positions, index < p.length) →
      (positions.map (fun index => p.getD index 0)).Sublist p := by
    intro positions ho hb
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    let select : Fin (positions.map (fun index => p.getD index 0)).length →
        Fin p.length := fun index =>
      ⟨positions[index.val]'(by simpa using index.is_lt),
        hb _ (List.getElem_mem (by simpa using index.is_lt))⟩
    have hmono : StrictMono select := by
      intro first second hlt
      exact List.pairwise_iff_getElem.mp ho first.val second.val
        (by simpa using first.is_lt) (by simpa using second.is_lt) hlt
    refine ⟨OrderEmbedding.ofStrictMono select hmono, ?_⟩
    intro index
    simp only [List.get_eq_getElem, List.getElem_map, OrderEmbedding.coe_ofStrictMono]
    exact List.getD_eq_getElem p 0 _
  obtain ⟨one, hob, ho⟩ := hmember 1 (by omega) (by omega)
  have honecut : one < site := by
    by_contra hnot
    have := htail one (by omega) hob
    omega
  have hhighorder : high.Pairwise (· > ·) := by
    rw [List.pairwise_iff_getElem]
    intro first second hf hs hfs
    have hfirst : site + first < p.length := by
      simp only [high, List.length_drop] at hf
      omega
    have hsecond : site + second < p.length := by
      simp only [high, List.length_drop] at hs
      omega
    have hdecrease : p.getD (site + second) 0 < p.getD (site + first) 0 := by
      rcases lt_trichotomy (p.getD (site + second) 0) (p.getD (site + first) 0) with
        hlt | heq | hgt
      · exact hlt
      · have := (List.getD_inj hsecond hfirst hnodup).mp heq
        omega
      · apply False.elim
        apply hparent.2 [1, 2, 3] (by simp)
        change ArrowWilfDefs.Contains [1, 2, 3] [] 3 p
        let values : ℕ → ℕ := fun rank => if rank = 1 then 1
          else if rank = 2 then p.getD (site + first) 0 else p.getD (site + second) 0
        have hsub := hselected [one, site + first, site + second]
          (by simp [List.pairwise_cons]; omega) (by
            intro index hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl | rfl <;> omega)
        simp only [List.map_cons, List.map_nil, ho] at hsub
        refine ⟨values, ?_, ?_, ?_, by simp⟩
        · intro rank hl hh
          have hc : rank = 1 ∨ rank = 2 := by omega
          have := htail (site + first) (by omega) hfirst
          rcases hc with rfl | rfl <;>
            simp only [values, ↓reduceIte, Nat.reduceAdd, Nat.reduceEqDiff] <;> omega
        · intro rank hl hh
          have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
          rcases hc with rfl | rfl | rfl <;> apply hsub.subset <;> simp [values]
        · simpa only [List.map_cons, List.map_nil, values, ↓reduceIte,
            Nat.reduceEqDiff] using hsub
    rw [← hhighentry first hf, ← hhighentry second hs,
      List.getD_eq_getElem high 0 hf, List.getD_eq_getElem high 0 hs] at hdecrease
    exact hdecrease
  have hcanonicalnodup : (List.range' (p.getD 1 0 + 1) (n - p.getD 1 0)).reverse.Nodup :=
    List.nodup_reverse.mpr (List.nodup_range' _)
  have hhigheq : high =
      ((List.range' (p.getD 1 0 + 1) (n - p.getD 1 0)).reverse).erase (p.getD 0 0) := by
    apply hhighorder.eq_of_mem_iff ((hrangeorder _ _).erase _)
    intro value
    rw [hhighmem, hcanonicalnodup.mem_erase_iff, List.mem_reverse]
    simp only [List.mem_range', Nat.one_mul]
    constructor
    · rintro ⟨hl, hh, hne⟩
      exact ⟨hne, value - (p.getD 1 0 + 1), by omega, by omega⟩
    · rintro ⟨hne, offset, ho, hv⟩
      omega
  have hprefixeq : p.take site = p.getD 0 0 :: low := by
    have hnonempty : p.take site ≠ [] := by
      intro heq
      have := congrArg List.length heq
      simp only [List.length_take, List.length_nil] at this
      omega
    have heq := List.cons_head_tail hnonempty
    have hhead : (p.take site).head hnonempty = p.getD 0 0 := by
      rw [List.head_eq_getElem, List.getElem_take, List.getD_eq_getElem p 0 (by omega)]
    simpa only [hhead, List.drop_one, low] using heq.symm
  refine ⟨hm.1, hmk, hk.2, hsitevalue, ?_⟩
  calc
    p = p.take site ++ high := (List.take_append_drop site p).symm
    _ = p.getD 0 0 :: low ++ high := by rw [hprefixeq]
    _ = _ := by rw [hloweq, hhigheq]

end D5.S3.Combinatorics.Fishburn.FishburnTenElevenClassicalPairs
