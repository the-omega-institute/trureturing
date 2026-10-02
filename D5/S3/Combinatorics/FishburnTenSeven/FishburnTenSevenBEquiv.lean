/- GID: D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBEquiv
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBEquiv
   mirror-E: none(waiver:reversible-second-class-normal-forms)
   anchors: [mathlib/module/Mathlib.Data.List.Sort]
   utility: none
   digest: Both interval constructors are valid and uniquely recover their parameters. -/

import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenBStructure
import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenBParameters
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenBEquiv

open D5.S3.Combinatorics Nonnesting Fishburn.FishburnDefs
open FishburnTenSevenAuxiliary FishburnTenSevenAuxiliaryCounting
open FishburnTenSevenBStructure FishburnTenSevenBParameters FishburnTenSevenMinimum

set_option maxHeartbeats 2400000 in
theorem B_typeI_mem (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) (s : HStart m) :
    (List.range' (m + 1) (n - m)).reverse ++ s.val.val ∈
      avoiders n [[1, 3, 2, 4], [2, 1, 4, 3], [3, 1, 2, 4]] := by
  have hfull : ∀ size, m ≤ size →
      ((List.range' (m + 1) (size - m)).reverse ++ s.val.val).Perm
          (List.range' 1 size) ∧
        IsFishburn ((List.range' (m + 1) (size - m)).reverse ++ s.val.val) ∧
        ¬ NonnestingDefs.Occurs [2, 1, 3]
          ((List.range' (m + 1) (size - m)).reverse ++ s.val.val) := by
    intro size
    induction size with
    | zero => omega
    | succ size ih =>
      intro hbound
      by_cases heq : m = size + 1
      · subst m
        simpa using s.val.property
      · have hprev := ih (by omega)
        have hword : (List.range' (m + 1) (size + 1 - m)).reverse ++ s.val.val =
            (size + 1) :: ((List.range' (m + 1) (size - m)).reverse ++ s.val.val) := by
          rw [show size + 1 - m = size - m + 1 by omega, List.range'_concat]
          simp [List.reverse_append, show m + 1 + (size - m) = size + 1 by omega]
        rw [hword]
        apply (H_head_decomposition size _).mpr
        exact ⟨⟨_, hprev⟩, Or.inl rfl⟩
  obtain ⟨hperm, hfish, h213⟩ := hfull n hmn
  refine ⟨hperm, hfish, ?_⟩
  have htriple (low middle high : ℕ) (hlm : low < middle) (hmh : middle < high)
      (hsub : [middle, low, high].Sublist
        ((List.range' (m + 1) (n - m)).reverse ++ s.val.val)) : False := by
    apply h213
    change ArrowWilfDefs.Contains [2, 1, 3] [] 3 _
    let values : ℕ → ℕ := fun rank => if rank = 1 then low
      else if rank = 2 then middle else high
    refine ⟨values, ?_, ?_, by simpa [values] using hsub, by simp⟩
    · intro rank hl hh
      have : rank = 1 ∨ rank = 2 := by omega
      rcases this with rfl | rfl <;> simp [values] <;> omega
    · intro rank hl hh
      have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases this with rfl | rfl | rfl <;>
        simp only [values, ↓reduceIte, Nat.reduceEqDiff] <;> apply hsub.subset <;> simp
  intro pattern hpattern hoccurs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
  rcases hpattern with rfl | rfl | rfl
  · obtain ⟨values, hstep, _, hsub, _⟩ := hoccurs
    apply htriple (values 2) (values 3) (values 4)
      (hstep 2 (by omega) (by change 2 < 4; omega))
      (hstep 3 (by omega) (by change 3 < 4; omega))
    have ht : [3, 2, 4].Sublist [1, 3, 2, 4] := by decide
    simpa using (ht.map values).trans hsub
  · obtain ⟨values, hstep, _, hsub, _⟩ := hoccurs
    apply htriple (values 1) (values 2) (values 4)
      (hstep 1 (by omega) (by change 1 < 4; omega)) (by
        have h23 : values 2 < values 3 := hstep 2 (by omega) (by change 2 < 4; omega)
        have h34 : values 3 < values 4 := hstep 3 (by omega) (by change 3 < 4; omega)
        omega)
    have ht : [2, 1, 4].Sublist [2, 1, 4, 3] := by decide
    simpa using (ht.map values).trans hsub
  · obtain ⟨values, hstep, _, hsub, _⟩ := hoccurs
    apply htriple (values 1) (values 3) (values 4) (by
        have h12 : values 1 < values 2 := hstep 1 (by omega) (by change 1 < 4; omega)
        have h23 : values 2 < values 3 := hstep 2 (by omega) (by change 2 < 4; omega)
        omega) (hstep 3 (by omega) (by change 3 < 4; omega))
    have ht : [3, 1, 4].Sublist [3, 1, 2, 4] := by decide
    simpa using (ht.map values).trans hsub

set_option maxHeartbeats 2400000 in
theorem B_typeII_mem (n m d h : ℕ) (hd : 2 ≤ d) (hdh : d ≤ h)
    (hhm : h < m) (hmn : m ≤ n) (q : H (d - 2)) :
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
      apply q.property.2.2
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

set_option maxHeartbeats 2400000 in
noncomputable def B_normalForm_equiv (n : ℕ) (hn : 1 ≤ n) :
    {p : List ℕ // p ∈ avoiders n [[1, 3, 2, 4], [2, 1, 4, 3], [3, 1, 2, 4]]} ≃
      BParameters n := by
  classical
  let initial (code : BParameters n) : List ℕ :=
    (List.range' (code.1.val + 1) (n - code.1.val)).reverse ++
      match code.2 with
      | Sum.inl _ => []
      | Sum.inr data => (List.range' data.1.val (data.2.1.val + 1 - data.1.val)).reverse
  let suffix (code : BParameters n) : List ℕ :=
    match code.2 with
    | Sum.inl s => s.val.val
    | Sum.inr data => 1 :: (List.range' (data.2.1.val + 1)
        (code.1.val - data.2.1.val - 1) ++ code.1.val :: data.2.2.val.map (· + 1))
  let word (code : BParameters n) := initial code ++ suffix code
  have hwordMem (code : BParameters n) :
      word code ∈ avoiders n [[1, 3, 2, 4], [2, 1, 4, 3], [3, 1, 2, 4]] := by
    rcases code with ⟨maximum, s | ⟨low, high, q⟩⟩
    · simpa [word, initial, suffix] using
        B_typeI_mem n maximum.val maximum.property.1 maximum.property.2 s
    · simpa [word, initial, suffix, List.append_assoc] using
        B_typeII_mem n maximum.val low.val high.val low.property.1 high.property.1
          high.property.2 maximum.property.2 q
  have hspec (code : BParameters n) : (suffix code).head? = some 1 ∧
      code.1.val ∈ suffix code ∧ ∀ value ∈ suffix code, value ≤ code.1.val := by
    rcases code with ⟨maximum, s | ⟨low, high, q⟩⟩
    · refine ⟨s.property, ?_, ?_⟩
      · apply s.val.property.1.mem_iff.mpr
        simp only [List.mem_range'_1]
        omega
      · intro value hv
        change value ≤ maximum.val
        have := s.val.property.1.mem_iff.mp hv
        simp only [List.mem_range'_1] at this
        omega
    · refine ⟨by simp [suffix], by simp [suffix], ?_⟩
      intro value hv
      change value ≤ maximum.val
      simp only [suffix, List.mem_cons, List.mem_append, List.mem_map] at hv
      rcases hv with rfl | hv | rfl | ⟨old, hold, rfl⟩
      · exact maximum.property.1
      · obtain ⟨offset, hoffset, rfl⟩ := List.mem_range'.mp hv
        simp only [Nat.one_mul] at *
        have := high.property.2
        omega
      · exact le_rfl
      · have := q.property.1.mem_iff.mp hold
        simp only [List.mem_range'_1] at this
        have := low.property.2
        omega
  have hnotOne (code : BParameters n) : 1 ∉ initial code := by
    rcases code with ⟨maximum, s | ⟨low, high, q⟩⟩ <;>
      simp only [initial, List.mem_append, List.mem_reverse, List.not_mem_nil, or_false,
        List.mem_range', Nat.one_mul]
    · rintro ⟨offset, _, heq⟩
      have := maximum.property.1
      omega
    · rintro (⟨offset, _, heq⟩ | ⟨offset, _, heq⟩)
      · have := maximum.property.1
        omega
      · have := low.property.1
        omega
  have hindex (code : BParameters n) : (word code).idxOf 1 = (initial code).length := by
    obtain ⟨tail, htail⟩ := List.head?_eq_some_iff.mp (hspec code).1
    dsimp only [word]
    rw [List.idxOf_append, if_neg (hnotOne code), htail]
    simp
  have hinterval (low high value : ℕ) (hle : low ≤ high) :
      value ∈ (List.range' low (high + 1 - low)).reverse ↔
        low ≤ value ∧ value ≤ high := by
    simp only [List.mem_reverse, List.mem_range', Nat.one_mul]
    constructor
    · rintro ⟨offset, hoffset, rfl⟩
      omega
    · rintro ⟨hlo, hhi⟩
      exact ⟨value - low, by omega, by omega⟩
  have hinjective : Function.Injective word := by
    intro first second heq
    have hlength : (initial first).length = (initial second).length := by
      rw [← hindex first, ← hindex second, heq]
    obtain ⟨hprefix, hsuffix⟩ := List.append_inj heq hlength
    have hfirstMem := (hspec first).2.1
    have hsecondMem := (hspec second).2.1
    rw [hsuffix] at hfirstMem
    rw [← hsuffix] at hsecondMem
    have hle := (hspec second).2.2 _ hfirstMem
    have hge := (hspec first).2.2 _ hsecondMem
    rcases first with ⟨maximum, body⟩
    rcases second with ⟨maximum', body'⟩
    have hmaximum : maximum = maximum' := Subtype.ext (by simpa using Nat.le_antisymm hle hge)
    subst maximum'
    have hbody : body = body' := by
      rcases body with s | ⟨low, high, q⟩ <;> rcases body' with s' | ⟨low', high', q'⟩
      · apply congrArg Sum.inl
        apply Subtype.ext
        apply Subtype.ext
        exact hsuffix
      · simp only [initial, List.length_append, List.length_reverse,
          List.length_range', List.length_nil, Nat.add_zero] at hlength
        have := high'.property.1
        omega
      · simp only [initial, List.length_append, List.length_reverse,
          List.length_range', List.length_nil, Nat.add_zero] at hlength
        have := high.property.1
        omega
      · have hblocks : (List.range' low.val (high.val + 1 - low.val)).reverse =
            (List.range' low'.val (high'.val + 1 - low'.val)).reverse := by
          exact List.append_cancel_left hprefix
        have hlow : low.val ∈ (List.range' low.val (high.val + 1 - low.val)).reverse :=
          (hinterval _ _ _ high.property.1).mpr ⟨le_rfl, high.property.1⟩
        have hlow' : low'.val ∈
            (List.range' low'.val (high'.val + 1 - low'.val)).reverse :=
          (hinterval _ _ _ high'.property.1).mpr ⟨le_rfl, high'.property.1⟩
        rw [hblocks] at hlow
        rw [← hblocks] at hlow'
        have hbound := (hinterval _ _ _ high'.property.1).mp hlow
        have hbound' := (hinterval _ _ _ high.property.1).mp hlow'
        have hloweq : low = low' := Subtype.ext (by omega)
        subst low'
        have hhigh : high.val ∈ (List.range' low.val (high.val + 1 - low.val)).reverse :=
          (hinterval _ _ _ high.property.1).mpr ⟨high.property.1, le_rfl⟩
        have hhigh' : high'.val ∈
            (List.range' low.val (high'.val + 1 - low.val)).reverse :=
          (hinterval _ _ _ high'.property.1).mpr ⟨high'.property.1, le_rfl⟩
        rw [hblocks] at hhigh
        rw [← hblocks] at hhigh'
        have hbound := (hinterval _ _ _ high'.property.1).mp hhigh
        have hbound' := (hinterval _ _ _ high.property.1).mp hhigh'
        have hhigheq : high = high' := Subtype.ext (by omega)
        subst high'
        have htail := (List.cons.inj hsuffix).2
        have hpeak := List.append_cancel_left htail
        have hshift := (List.cons.inj hpeak).2
        have hq : q = q' := by
          apply Subtype.ext
          have ht := congrArg (List.map (· - 1)) hshift
          simpa [List.map_map, Function.comp_def] using ht
        subst q'
        rfl
    exact congrArg (Sigma.mk maximum) hbody
  have hexists (p : {p : List ℕ //
      p ∈ avoiders n [[1, 3, 2, 4], [2, 1, 4, 3], [3, 1, 2, 4]]}) :
      ∃ code : BParameters n, word code = p.val := by
    obtain ⟨maximum, hpositive, hbound, hform⟩ := B_interval_normalForm n p.val hn p.property
    rcases hform with ⟨s, hhead, heq⟩ | ⟨low, high, hlo, hlh, hhm, q, heq⟩
    · refine ⟨⟨⟨maximum, hpositive, hbound⟩, Sum.inl ⟨s, hhead⟩⟩, ?_⟩
      simpa [word, initial, suffix] using heq.symm
    · refine ⟨⟨⟨maximum, hpositive, hbound⟩,
        Sum.inr ⟨⟨low, hlo, by change low < maximum; omega⟩,
          ⟨high, hlh, hhm⟩, q⟩⟩, ?_⟩
      simpa [word, initial, suffix, List.append_assoc] using heq.symm
  let encode (p : {p : List ℕ //
      p ∈ avoiders n [[1, 3, 2, 4], [2, 1, 4, 3], [3, 1, 2, 4]]}) :=
    Classical.choose (hexists p)
  have hencode (p : {p : List ℕ //
      p ∈ avoiders n [[1, 3, 2, 4], [2, 1, 4, 3], [3, 1, 2, 4]]}) :
      word (encode p) = p.val := Classical.choose_spec (hexists p)
  refine
    { toFun := encode
      invFun := fun code => ⟨word code, hwordMem code⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    exact Subtype.ext (hencode p)
  · intro code
    exact hinjective (hencode ⟨word code, hwordMem code⟩)

end D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenBEquiv
