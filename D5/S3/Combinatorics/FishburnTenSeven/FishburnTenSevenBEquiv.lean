/- GID: D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBEquiv
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBEquiv
   mirror-E: none(waiver:second-class-interval-constructor)
   anchors: [mathlib/module/Mathlib.Data.List.Sort]
   utility: none
   digest: The second interval constructor preserves Fishburn membership and pattern avoidance. -/

import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenBStructure
import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenBParameters
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenBEquiv

open D5.S3.Combinatorics Nonnesting Fishburn.FishburnDefs
open FishburnTenSevenAuxiliary
open FishburnTenSevenBStructure FishburnTenSevenBParameters FishburnTenSevenMinimum

set_option maxHeartbeats 2400000 in
theorem B_typeII_mem (n m d h : ℕ) (hd : 2 ≤ d) (hdh : d ≤ h)
    (hhm : h < m) (hmn : m ≤ n) (q : ↥(avoiders (d - 2) [[2, 1, 3]])) :
    (List.range' (m + 1) (n - m)).reverse ++
      (List.range' d (h + 1 - d)).reverse ++
        1 :: (List.range' (h + 1) (m - h - 1) ++ m :: q.val.map (· + 1)) ∈
      avoiders n [[1, 3, 2, 4], [2, 1, 4, 3], [3, 1, 2, 4]] := by
  let upper := List.range' (m + 1) (n - m)
  let lower := List.range' d (h + 1 - d)
  let rising := List.range' (h + 1) (m - h)
  let ending := q.val.map (· + 1)
  let before := upper.reverse ++ lower.reverse
  let word := before ++ 1 :: (rising ++ ending)
  have hrising : rising = List.range' (h + 1) (m - h - 1) ++ [m] := by
    dsimp [rising]
    rw [show m - h = m - h - 1 + 1 by omega, List.range'_concat]
    simp [show h + 1 + (m - h - 1) = m by omega]
  have htarget : word = (List.range' (m + 1) (n - m)).reverse ++
      (List.range' d (h + 1 - d)).reverse ++
        1 :: (List.range' (h + 1) (m - h - 1) ++ m :: ending) := by
    simp [word, before, upper, lower, hrising, List.append_assoc]
  rw [← htarget]
  have huMem : ∀ value, value ∈ upper ↔ m < value ∧ value ≤ n := by
    intro value
    simp only [upper, List.mem_range', Nat.one_mul]
    constructor
    · rintro ⟨offset, hoffset, rfl⟩
      omega
    · rintro ⟨hlo, hhi⟩
      exact ⟨value - (m + 1), by omega, by omega⟩
  have hlMem : ∀ value, value ∈ lower ↔ d ≤ value ∧ value ≤ h := by
    intro value
    simp only [lower, List.mem_range', Nat.one_mul]
    constructor
    · rintro ⟨offset, hoffset, rfl⟩
      omega
    · rintro ⟨hlo, hhi⟩
      exact ⟨value - d, by omega, by omega⟩
  have hrMem : ∀ value, value ∈ rising ↔ h < value ∧ value ≤ m := by
    intro value
    simp only [rising, List.mem_range', Nat.one_mul]
    constructor
    · rintro ⟨offset, hoffset, rfl⟩
      omega
    · rintro ⟨hlo, hhi⟩
      exact ⟨value - (h + 1), by omega, by omega⟩
  have hqMem : ∀ value, value ∈ q.val ↔ 1 ≤ value ∧ value ≤ d - 2 := by
    intro value
    rw [q.property.1.mem_iff]
    simp only [List.mem_range'_1]
    omega
  have heMem : ∀ value, value ∈ ending ↔ 2 ≤ value ∧ value < d := by
    intro value
    simp only [ending, List.mem_map]
    constructor
    · rintro ⟨old, hold, rfl⟩
      have := (hqMem old).mp hold
      omega
    · rintro ⟨hlo, hhi⟩
      exact ⟨value - 1, (hqMem _).mpr (by omega), by omega⟩
  have hbMem : ∀ value, value ∈ before ↔
      (m < value ∧ value ≤ n) ∨ (d ≤ value ∧ value ≤ h) := by
    intro value
    simp only [before, List.mem_append, List.mem_reverse, huMem, hlMem]
  have hbDec : before.Pairwise (· > ·) := by
    apply List.pairwise_append.mpr
    refine ⟨List.pairwise_reverse.mpr (List.pairwise_lt_range'),
      List.pairwise_reverse.mpr (List.pairwise_lt_range'), ?_⟩
    intro high hhigh low hlow
    have hh := (huMem high).mp (List.mem_reverse.mp hhigh)
    have hl := (hlMem low).mp (List.mem_reverse.mp hlow)
    omega
  have hePerm : ending.Perm (List.range' 2 (d - 2)) := by
    have ht := q.property.1.map (· + 1)
    have hf : (fun value : ℕ => value + 1) = (1 + ·) :=
      funext (fun value => Nat.add_comm value 1)
    simpa only [ending, hf, List.map_add_range', Nat.reduceAdd] using ht
  have hjoin (start middle finish : ℕ) (hsm : start ≤ middle) (hmf : middle ≤ finish) :
      List.range' start (middle - start) ++ List.range' middle (finish - middle) =
        List.range' start (finish - start) := by
    have hb : start + 1 * (middle - start) = middle := by omega
    have hs : (middle - start) + (finish - middle) = finish - start := by omega
    simpa only [hb, hs] using
      (List.range'_append (s := start) (m := middle - start) (n := finish - middle)
        (step := 1))
  have hcanonical : (1 :: ((List.range' 2 (d - 2)) ++ lower ++ rising ++ upper)) =
      List.range' 1 n := by
    have hfirst : [1] = List.range' 1 1 := by simp
    change [1] ++ List.range' 2 (d - 2) ++ lower ++ rising ++ upper = _
    rw [hfirst]
    change List.range' 1 1 ++ List.range' 2 (d - 2) ++
      List.range' d (h + 1 - d) ++ List.range' (h + 1) (m - h) ++
        List.range' (m + 1) (n - m) = List.range' 1 n
    rw [hjoin 1 2 d (by omega) hd]
    have hlow := hjoin 1 d (h + 1) (by omega) (by omega)
    have hrise := hjoin 1 (h + 1) (m + 1) (by omega) (by omega)
    have hhigh := hjoin 1 (m + 1) (n + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel, Nat.add_sub_add_right] at hlow hrise hhigh
    rw [hlow, hrise, hhigh]
  have hperm : word.Perm (List.range' 1 n) := by
    have hreverses : word.Perm (upper ++ lower ++ 1 :: (rising ++ ending)) := by
      exact ((List.reverse_perm _).append (List.reverse_perm _)).append (List.Perm.refl _)
    have hmove : (upper ++ lower ++ 1 :: (rising ++ ending)).Perm
        (1 :: (ending ++ lower ++ rising ++ upper)) := by
      apply List.Perm.trans List.perm_middle
      apply List.Perm.cons
      have hrotate : (upper ++ lower ++ (rising ++ ending)).Perm
          (ending ++ (upper ++ lower ++ rising)) := by
        simpa only [List.append_assoc] using
          (List.perm_append_comm (l₁ := upper ++ lower ++ rising) (l₂ := ending))
      have hrotate' : (ending ++ (upper ++ lower ++ rising)).Perm
          (ending ++ (lower ++ rising ++ upper)) := by
        simpa only [List.append_assoc] using
          (List.perm_append_comm (l₁ := upper) (l₂ := lower ++ rising)).append_left ending
      simpa only [List.append_assoc] using hrotate.trans hrotate'
    have hmapped : (1 :: (ending ++ lower ++ rising ++ upper)).Perm
        (1 :: (List.range' 2 (d - 2) ++ lower ++ rising ++ upper)) := by
      simpa only [List.append_assoc] using (hePerm.append_right (lower ++ rising ++ upper)).cons 1
    exact ((hreverses.trans hmove).trans hmapped).trans (List.Perm.of_eq hcanonical)
  have hlength : word.length = before.length + 1 + rising.length + ending.length := by
    simp [word]
    omega
  let start := before.length + 1
  let finish := start + rising.length
  have hlength' : word.length = finish + ending.length := by omega
  have hatBefore (index : ℕ) (hi : index < before.length) :
      word.getD index 0 = before.getD index 0 := List.getD_append _ _ _ _ hi
  have hatOne : word.getD before.length 0 = 1 := by
    rw [List.getD_append_right before _ 0 _ (by omega)]
    simp
  have hatRising (index : ℕ) (hlo : start ≤ index) (hhi : index < finish) :
      word.getD index 0 = h + 1 + (index - start) := by
    change (before ++ 1 :: (rising ++ ending)).getD index 0 = _
    rw [List.getD_append_right before _ 0 _ (by omega)]
    rw [show index - before.length = (index - start) + 1 by omega,
      List.getD_cons_succ, List.getD_append rising ending 0 _ (by omega)]
    rw [List.getD_eq_getElem _ _ (by omega)]
    simp [rising]
  have hatEnding (index : ℕ) (hi : finish ≤ index) :
      word.getD index 0 = ending.getD (index - finish) 0 := by
    change (before ++ 1 :: (rising ++ ending)).getD index 0 = _
    rw [List.getD_append_right before _ 0 _ (by omega)]
    rw [show index - before.length = (index - start) + 1 by omega,
      List.getD_cons_succ, List.getD_append_right rising ending 0 _ (by omega)]
    congr 1
    omega
  have hbValue (index : ℕ) (hi : index < before.length) :
      (m < word.getD index 0 ∧ word.getD index 0 ≤ n) ∨
        (d ≤ word.getD index 0 ∧ word.getD index 0 ≤ h) := by
    rw [hatBefore index hi]
    apply (hbMem _).mp
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hrValue (index : ℕ) (hlo : start ≤ index) (hhi : index < finish) :
      h < word.getD index 0 ∧ word.getD index 0 ≤ m := by
    rw [hatRising index hlo hhi]
    have hrlen : rising.length = m - h := by simp [rising]
    omega
  have heValue (index : ℕ) (hlo : finish ≤ index) (hhi : index < word.length) :
      2 ≤ word.getD index 0 ∧ word.getD index 0 < d := by
    rw [hatEnding index hlo]
    have hi : index - finish < ending.length := by omega
    apply (heMem _).mp
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have heTranslate (index : ℕ) (hi : index < ending.length) :
      ending.getD index 0 = q.val.getD index 0 + 1 := by
    have hqindex : index < q.val.length := by simpa [ending] using hi
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hqindex]
    exact List.getElem_map _
  have hfish : IsFishburn word := by
    intro first later hgap hlater hbad
    by_cases hb : first < before.length
    · by_cases hnext : first + 1 < before.length
      · have hdec := List.pairwise_iff_getElem.mp hbDec first (first + 1) hb hnext
          (by omega)
        rw [hatBefore first hb, hatBefore (first + 1) hnext,
          List.getD_eq_getElem _ _ hb, List.getD_eq_getElem _ _ hnext] at hbad
        omega
      · have heq : first + 1 = before.length := by omega
        have hv := hbValue first hb
        rw [heq, hatOne] at hbad
        rcases hv with hv | hv <;> omega
    · by_cases hone : first = before.length
      · subst first
        have hpos : 1 ≤ word.getD later 0 := by
          by_cases hr : later < finish
          · have := hrValue later (by omega) hr
            omega
          · have := (heValue later (by omega) hlater).1
            omega
        rw [hatOne] at hbad
        omega
      · have hs : start ≤ first := by omega
        by_cases hr : first < finish
        · have hf := hrValue first hs hr
          by_cases hl : later < finish
          · rw [hatRising first hs hr, hatRising later (by omega) hl] at hbad
            omega
          · have hv := heValue later (by omega) hlater
            omega
        · have hf : finish ≤ first := by omega
          rw [hatEnding first hf, hatEnding later (by omega),
            hatEnding (first + 1) (by omega), heTranslate _ (by omega),
            heTranslate _ (by omega), heTranslate _ (by omega)] at hbad
          apply q.property.2.1 (first - finish) (later - finish) (by omega)
            (by simpa [ending] using (show later - finish < ending.length by omega))
          rw [show first + 1 - finish = first - finish + 1 by omega] at hbad
          omega
  have hselected (positions : List ℕ) (horder : positions.Pairwise (· < ·))
      (hbound : ∀ index ∈ positions, index < q.val.length) :
      (positions.map (fun index => q.val.getD index 0)).Sublist q.val := by
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    let select : Fin (positions.map (fun index => q.val.getD index 0)).length →
        Fin q.val.length := fun index =>
      ⟨positions[index.val]'(by simpa using index.isLt),
        hbound _ (List.getElem_mem (by simpa using index.isLt))⟩
    have hmono : StrictMono select := by
      intro first second hlt
      exact List.pairwise_iff_getElem.mp horder first.val second.val
        (by simpa using first.isLt) (by simpa using second.isLt) hlt
    refine ⟨OrderEmbedding.ofStrictMono select hmono, ?_⟩
    intro index
    simp only [List.get_eq_getElem, List.getElem_map, OrderEmbedding.coe_ofStrictMono]
    exact List.getD_eq_getElem q.val 0 _
  have hnoTriple (first second third : ℕ) (h12 : before.length < first)
      (h23 : first < second) (h34 : second < third) (hbound : third < word.length)
      (hlow : word.getD second 0 < word.getD first 0)
      (hhigh : word.getD first 0 < word.getD third 0) : False := by
    by_cases hfirst : first < finish
    · have hf := hrValue first (by omega) hfirst
      by_cases hsecond : second < finish
      · rw [hatRising first (by omega) hfirst,
          hatRising second (by omega) hsecond] at hlow
        omega
      · have ht := heValue third (by omega) hbound
        omega
    · have hf : finish ≤ first := by omega
      have hs : finish ≤ second := by omega
      have ht : finish ≤ third := by omega
      rw [hatEnding first hf, hatEnding second hs,
        heTranslate _ (by omega), heTranslate _ (by omega)] at hlow
      rw [hatEnding first hf, hatEnding third ht,
        heTranslate _ (by omega), heTranslate _ (by omega)] at hhigh
      apply q.property.2.2 [2, 1, 3] (by simp)
      change ArrowWilfDefs.Contains [2, 1, 3] [] 3 q.val
      let values : ℕ → ℕ := fun rank => if rank = 1 then q.val.getD (second - finish) 0
        else if rank = 2 then q.val.getD (first - finish) 0
        else q.val.getD (third - finish) 0
      have hsub := hselected [first - finish, second - finish, third - finish]
        (by simp [List.pairwise_cons]; omega) (by
          intro index hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl <;> simp [ending] at hlength' <;> omega)
      refine ⟨values, ?_, ?_, by simpa [values] using hsub, by simp⟩
      · intro rank hl hh
        have : rank = 1 ∨ rank = 2 := by omega
        rcases this with rfl | rfl
        · change q.val.getD (second - finish) 0 < q.val.getD (first - finish) 0
          omega
        · change q.val.getD (first - finish) 0 < q.val.getD (third - finish) 0
          omega
      · intro rank hl hh
        have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases this with rfl | rfl | rfl <;> simp [values] <;> apply hsub.subset <;> simp
  have htests := minimum_pattern_tests n word hperm hfish before.length
    (by simp [word]) hatOne
  have h1324 : ¬ NonnestingDefs.Occurs [1, 3, 2, 4] word := by
    intro hocc
    obtain ⟨first, second, third, h12, h23, h34, hb, hl, hh⟩ := htests.1.mp hocc
    exact hnoTriple first second third h12 h23 h34 hb hl hh
  have h2143 : ¬ NonnestingDefs.Occurs [2, 1, 4, 3] word := by
    intro hocc
    obtain ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩ :=
      (htests.2.2 h1324).1.mp hocc
    have hv := hbValue first hf
    by_cases he : finish ≤ third
    · have hvthird := heValue third he ht
      rcases hv with hv | hv <;> omega
    · have hsecond : second < finish := by omega
      rw [hatRising second (by omega) hsecond, hatRising third (by omega) (by omega)]
        at hhigh
      omega
  have h3124 : ¬ NonnestingDefs.Occurs [3, 1, 2, 4] word := by
    intro hocc
    obtain ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩ :=
      (htests.2.2 h1324).2.mp hocc
    have hv := hbValue first hf
    by_cases he : finish ≤ second
    · have hvthird := heValue third (by omega) ht
      rcases hv with hv | hv <;> omega
    · have hvsecond := hrValue second (by omega) (by omega)
      rcases hv with hv | hv
      · by_cases het : finish ≤ third
        · have hvthird := heValue third het ht
          omega
        · have hvthird := hrValue third (by omega) (by omega)
          omega
      · omega
  refine ⟨hperm, hfish, ?_⟩
  intro pattern hpattern
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
  rcases hpattern with rfl | rfl | rfl
  · exact h1324
  · exact h2143
  · exact h3124

end D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenBEquiv
