/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateLastEndpoint
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateLastEndpoint
   mirror-E: none(waiver:last-endpoint-cycle-construction)
   anchors: []
   utility: none
   digest: Closing the stem cycle identifies the surviving first-maximum last-endpoint words. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateTail
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateInsertion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateLastEndpoint

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseBlocks
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycle
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateInsertion
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycleReduction
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateScan

local notation "B" =>
  (fun word : List ℕ => List.map (hat word) (List.range' 1 (List.length word)))

set_option maxHeartbeats 1200000 in
theorem last_endpoint_cycle (stem : List ℕ)
    (hperm : stem.Perm (List.range' 1 stem.length)) (hsize : 2 ≤ stem.length)
    (hfirst : stem.getD 0 0 = stem.length) :
    (P (stem ++ [stem.length + 1]) ∈
        ThetaIterateDefs.iterateAvoiders (stem.length + 3) 2 [1, 3, 2] →
      stem.getD (stem.length - 1) 0 = 1) ∧
      ∀ _ : stem.getD (stem.length - 1) 0 = 1,
        (B stem).getD 0 0 = stem.length ∧ ThetaFixedDefs.theta (B stem) = stem ∧
          (P (stem ++ [stem.length + 1]) ∈
              ThetaIterateDefs.iterateAvoiders (stem.length + 3) 2 [1, 3, 2] ↔
            B stem ∈ ThetaIterateDefs.iterateAvoiders stem.length 2 [1, 3, 2]) := by
  let size := stem.length
  let parameter := stem ++ [size + 1]
  let inverse := B stem
  have hplen : parameter.length = size + 1 := by simp [parameter, size]
  have hilen : inverse.length = size := by simp [inverse, size]
  have hnd := hperm.nodup_iff.mpr List.nodup_range'
  have hvalue (index : ℕ) (hi : index < size) :
      1 ≤ stem.getD index 0 ∧ stem.getD index 0 ≤ size := by
    have hm : stem.getD index 0 ∈ stem := by
      rw [List.getD_eq_getElem _ 0 hi]
      exact List.getElem_mem hi
    obtain ⟨offset, ho, heq⟩ := List.mem_range'.mp (hperm.mem_iff.mp hm)
    dsimp [size]
    omega
  have hmem (value : ℕ) (hpositive : 1 ≤ value) (hbound : value ≤ size) :
      value ∈ stem := hperm.mem_iff.mpr
    (List.mem_range'.mpr ⟨value - 1, by dsimp [size] at *; omega, by omega⟩)
  have hnon (index : ℕ) (hpositive : 0 < index) (hi : index < size) :
      ¬ IsLtrMax stem index := by
    intro hrecord
    have hlt := hrecord 0 hpositive
    have hb := hvalue index hi
    dsimp [size] at hb
    omega
  have hidx (index : ℕ) (hi : index < size) :
      stem.idxOf (stem.getD index 0) = index := by
    rw [List.getD_eq_getElem _ 0 hi]
    simpa using List.get_idxOf hnd ⟨index, hi⟩
  have hparameter : parameter.Perm (List.range' 1 parameter.length) := by
    rw [hplen, show List.range' 1 (size + 1) =
      List.range' 1 size ++ [size + 1] by
        simpa only [one_mul, Nat.add_comm] using
          (List.range'_concat (s := 1) (n := size) (step := 1))]
    exact hperm.append (List.Perm.refl _)
  have hget (index : ℕ) (hi : index < size) :
      parameter.getD index 0 = stem.getD index 0 := by
    exact List.getD_append _ _ _ _ hi
  have hlastParameter : parameter.getD size 0 = size + 1 := by
    simp [parameter, size]
  have himages := (ThetaIterateCycleReduction.P_cycle_reduction parameter hparameter
    (by rw [hplen]; omega)).2.2.2
  have necessary : P parameter ∈
      ThetaIterateDefs.iterateAvoiders (size + 3) 2 [1, 3, 2] →
        stem.getD (stem.length - 1) 0 = 1 := by
    intro hm
    by_contra hlast
    have honeMem := hmem 1 (by omega) (by dsimp [size]; omega)
    have honeIndex : stem.idxOf 1 < size := List.idxOf_lt_length_of_mem honeMem
    have honeValue : stem.getD (stem.idxOf 1) 0 = 1 := by
      rw [List.getD_eq_getElem _ 0 honeIndex]
      exact List.getElem_idxOf honeIndex
    have honePositive : 0 < stem.idxOf 1 := by
      by_contra hnot
      have hzero : stem.idxOf 1 = 0 := by omega
      rw [hzero, hfirst] at honeValue
      omega
    have honeNotLast : stem.idxOf 1 ≠ size - 1 := by
      intro heq
      exact hlast (by simpa only [heq, size] using honeValue)
    have hnext : stem.idxOf 1 + 1 < size := by omega
    have hnextBounds := hvalue (stem.idxOf 1 + 1) hnext
    have hnextNe : stem.getD (stem.idxOf 1 + 1) 0 ≠ size := by
      intro heq
      have hsame : stem.getD (stem.idxOf 1 + 1) 0 = stem.getD 0 0 :=
        heq.trans hfirst.symm
      rw [List.getD_eq_getElem _ 0 hnext,
        List.getD_eq_getElem _ 0 (by omega)] at hsame
      have hindex := hnd.getElem_inj_iff.mp hsame
      omega
    let final := stem.getD (size - 1) 0
    have hfinalBounds := hvalue (size - 1) (by dsimp [size]; omega)
    have hfinalLarge : 1 < final := by dsimp [final, size] at *; omega
    have hfinalMem : final ∈ stem := by
      change stem.getD (size - 1) 0 ∈ stem
      rw [List.getD_eq_getElem _ 0 (by omega)]
      exact List.getElem_mem (by dsimp [size]; omega)
    have hPone : (P parameter).getD 1 0 =
        stem.getD (stem.idxOf 1 + 1) 0 + 1 := by
      rw [himages.2.2 1 (List.mem_append_left _ honeMem),
        List.idxOf_append_of_mem honeMem, if_pos (by rw [hplen]; omega), hget _ hnext]
    have hPfinal : (P parameter).getD final 0 = size + 2 := by
      rw [himages.2.2 final (List.mem_append_left _ hfinalMem),
        List.idxOf_append_of_mem hfinalMem, hidx _ (by dsimp [size]; omega),
        if_pos (by rw [hplen]; omega), show size - 1 + 1 = size by omega,
        hlastParameter]
    have hPend : (P parameter).getD (size + 2) 0 = size + 1 := by
      rw [show size + 2 = parameter.length + 1 by omega, himages.2.1,
        hget 0 (by dsimp [size]; omega), hfirst]
    have hPlen : (P parameter).length = size + 3 := by simp [P, hplen]
    have hsub : [(P parameter).getD 1 0, size + 2, size + 1].Sublist (P parameter) := by
      let positions : Fin 3 → Fin (P parameter).length := fun index =>
        if index.val = 0 then ⟨1, by rw [hPlen]; omega⟩
        else if index.val = 1 then ⟨final, by rw [hPlen]; dsimp [final]; omega⟩
        else ⟨size + 2, by rw [hPlen]; omega⟩
      have hmono : StrictMono positions := by
        intro left right hlt
        fin_cases left <;> fin_cases right <;> (simp_all [positions] <;> omega)
      apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
      refine ⟨OrderEmbedding.ofStrictMono positions hmono, ?_⟩
      intro index
      fin_cases index
      · exact List.getD_eq_getElem _ 0 (by rw [hPlen]; omega)
      · exact hPfinal.symm.trans (List.getD_eq_getElem _ 0 (by rw [hPlen]; omega))
      · exact hPend.symm.trans (List.getD_eq_getElem _ 0 (by rw [hPlen]; omega))
    have hcontains : Contains [1, 3, 2] [] 3 (P parameter) := by
      let values : ℕ → ℕ := fun index => if index = 1 then (P parameter).getD 1 0
        else if index = 2 then size + 1 else size + 2
      refine ⟨values, ?_, ?_, ?_, by simp⟩
      · intro index hi hn
        have hc : index = 1 ∨ index = 2 := by omega
        rcases hc with rfl | rfl
        · change (P parameter).getD 1 0 < size + 1
          omega
        · change size + 1 < size + 2
          omega
      · intro index hi hn
        have hc : index = 1 ∨ index = 2 ∨ index = 3 := by omega
        rcases hc with rfl | rfl | rfl
        · rw [show values 1 = (P parameter).getD 1 0 by simp [values],
            List.getD_eq_getElem _ 0 (by rw [hPlen]; omega)]
          exact List.getElem_mem (by rw [hPlen]; omega)
        · rw [show values 2 = size + 1 by simp [values], ← hPend,
            List.getD_eq_getElem _ 0 (by rw [hPlen]; omega)]
          exact List.getElem_mem (by rw [hPlen]; omega)
        · rw [show values 3 = size + 2 by simp [values], ← hPfinal,
            List.getD_eq_getElem _ 0 (by rw [hPlen]; omega)]
          exact List.getElem_mem (by rw [hPlen]; omega)
      · simpa [values] using hsub
    exact (hm.2 0 (by omega)) (by simpa using hcontains)
  refine ⟨necessary, ?_⟩
  intro hlast
  have hone : stem.idxOf 1 = size - 1 := by
    have heq := hidx (size - 1) (by dsimp [size]; omega)
    simpa only [size, hlast] using heq
  have hedge (value : ℕ) (hv : value ∈ stem) :
      hat stem value = if stem.idxOf value + 1 < size then
        stem.getD (stem.idxOf value + 1) 0 else size := by
    have hi : stem.idxOf value < size := List.idxOf_lt_length_of_mem hv
    have hgreatest : Nat.findGreatest (IsLtrMax stem) (stem.idxOf value) = 0 := by
      apply Nat.findGreatest_eq_zero_iff.mpr
      intro index hpositive hbound
      exact hnon index hpositive (by omega)
    unfold hat
    by_cases hn : stem.idxOf value + 1 < size
    · rw [if_pos ⟨hn, hnon _ (by omega) hn⟩, if_pos hn]
    · rw [if_neg (fun hb => hn hb.1), if_neg hn, hgreatest, hfirst]
  have hinverse (index : ℕ) (hi : index < size) :
      inverse.getD index 0 = hat stem (index + 1) := by
    rw [List.getD_eq_getElem _ 0 (by rw [hilen]; exact hi)]
    simp only [inverse, List.getElem_map, List.getElem_range'_1, Nat.add_comm]
  have hPget (index : ℕ) (hi : index < size + 3) :
      (P parameter).getD index 0 = if index = 0 then size + 3
        else if index = 1 then size + 2
        else if index ≤ size then inverse.getD (index - 1) 0 + 1
        else if index = size + 1 then 1 else size + 1 := by
    by_cases hzero : index = 0
    · subst index
      simpa [hplen, Nat.add_assoc] using himages.1
    by_cases honeIndex : index = 1
    · subst index
      have hm : 1 ∈ parameter := List.mem_append_left _ (hmem 1 (by omega) (by omega))
      have hidxOne : parameter.idxOf 1 = size - 1 := by
        rw [List.idxOf_append_of_mem (hmem 1 (by omega) (by omega)), hone]
      rw [himages.2.2 1 hm, hidxOne, if_pos (by rw [hplen]; omega),
        show size - 1 + 1 = size by omega, hlastParameter]
      simp
    by_cases hmiddle : index ≤ size
    · have hm := hmem index (by omega) hmiddle
      have hidxParameter : parameter.idxOf index = stem.idxOf index :=
        List.idxOf_append_of_mem hm
      have hindex : stem.idxOf index < size := List.idxOf_lt_length_of_mem hm
      have hnotLast : stem.idxOf index ≠ size - 1 := by
        intro heq
        have hv : stem.getD (stem.idxOf index) 0 = index := by
          rw [List.getD_eq_getElem _ 0 hindex]
          exact List.getElem_idxOf hindex
        rw [heq, hlast] at hv
        omega
      have hnext : stem.idxOf index + 1 < size := by omega
      rw [himages.2.2 index (List.mem_append_left _ hm), hidxParameter,
        if_pos (by rw [hplen]; omega), hget _ hnext]
      rw [if_neg hzero, if_neg honeIndex, if_pos hmiddle,
        hinverse _ (by omega), show index - 1 + 1 = index by omega,
        hedge index hm, if_pos hnext]
    · have hcases : index = size + 1 ∨ index = size + 2 := by omega
      rcases hcases with rfl | rfl
      · have hnotmem : size + 1 ∉ stem := by
          intro hm
          obtain ⟨offset, ho, heq⟩ := List.mem_range'.mp (hperm.mem_iff.mp hm)
          dsimp [size] at *
          omega
        have hidxLast : parameter.idxOf (size + 1) = size := by
          simp only [parameter, List.idxOf_append_of_notMem hnotmem,
            List.idxOf_cons_self, Nat.add_zero]
          rfl
        have hm : size + 1 ∈ parameter := by simp [parameter]
        rw [himages.2.2 _ hm, hidxLast, if_neg (by rw [hplen]; omega)]
        simp only [if_neg (by omega : size + 1 ≠ 0),
          if_neg (by omega : size + 1 ≠ 1), if_neg (by omega : ¬ size + 1 ≤ size),
          ite_true]
      · have hfinal : size + 2 = parameter.length + 1 := by omega
        rw [if_neg (by omega : size + 2 ≠ 0),
          if_neg (by omega : size + 2 ≠ 1), if_neg (by omega : ¬ size + 2 ≤ size),
          if_neg (by omega : size + 2 ≠ size + 1), hfinal, himages.2.1,
          hget 0 (by dsimp [size]; omega), hfirst]
  have hIget (index : ℕ) (hi : index < size + 3) :
      (I inverse).getD index 0 = if index = 0 then size + 3
        else if index = 1 then size + 2
        else if index ≤ size then inverse.getD (index - 1) 0 + 1
        else if index = size + 1 then 1 else size + 1 := by
    by_cases hzero : index = 0
    · subst index
      simp [I, hilen]
    by_cases honeIndex : index = 1
    · subst index
      simp [I, hilen]
    have hhead : ([inverse.length + 3, inverse.length + 2] : List ℕ).length ≤ index :=
      by simp; omega
    rw [I, List.append_assoc, List.getD_append_right _ _ 0 index hhead]
    simp only [List.length_cons, List.length_nil]
    by_cases hmiddle : index ≤ size
    · rw [List.getD_append _ _ 0 _ (by simp [hilen]; omega),
        List.getD_eq_getElem _ 0 (by simp [hilen]; omega), List.getElem_map,
        List.getElem_drop, ← List.getD_eq_getElem inverse 0 (by rw [hilen]; omega)]
      simp only [if_neg hzero, if_neg honeIndex, if_pos hmiddle]
      congr 2
      omega
    · rw [List.getD_append_right _ _ 0 _ (by simp [hilen]; omega)]
      simp only [List.length_map, List.length_drop, hilen]
      have hcases : index = size + 1 ∨ index = size + 2 := by omega
      rcases hcases with rfl | rfl
      · rw [show size + 1 - 2 - (size - 1) = 0 by omega]
        simp [show size ≠ 0 by dsimp [size]; omega]
      · rw [show size + 2 - 2 - (size - 1) = 1 by omega]
        simp
  have hconstructed : P parameter = I inverse := by
    apply List.ext_getElem
    · simp [P, I, hplen, hilen]
      omega
    · intro index hp hi
      have hbound : index < size + 3 := by
        simpa [P, hplen, Nat.add_assoc] using hp
      rw [← List.getD_eq_getElem _ 0 hp, ← List.getD_eq_getElem _ 0 hi,
        hPget index hbound, hIget index hbound]
  have hinversePerm : inverse.Perm (List.range' 1 inverse.length) := by
    have hmapnd : (stem.map (hat stem)).Nodup :=
      hnd.map_on (hat_inj_on stem hnd)
    have hclosed (value : ℕ) (hv : value ∈ stem) : hat stem value ∈ stem := by
      rw [hedge value hv]
      split_ifs with hn
      · rw [List.getD_eq_getElem _ 0 hn]
        exact List.getElem_mem hn
      · exact hmem size (by dsimp [size]; omega) (le_refl _)
    have hsubset : (stem.map (hat stem)).toFinset ⊆ stem.toFinset := by
      intro value hv
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
      exact List.mem_toFinset.mpr (hclosed old ho)
    have hcard : (stem.map (hat stem)).toFinset.card = stem.toFinset.card := by
      simp [List.card_toFinset, List.dedup_eq_self.mpr hmapnd,
        List.dedup_eq_self.mpr hnd]
    have heq := Finset.eq_of_subset_of_card_le hsubset (by omega)
    have hmapperm := List.perm_of_nodup_nodup_toFinset_eq hmapnd hnd heq
    rw [hilen]
    exact ((hperm.symm.map _).trans hmapperm).trans hperm
  have hinverseFirst : inverse.getD 0 0 = inverse.length := by
    rw [hinverse 0 (by dsimp [size]; omega), hedge 1 (hmem 1 (by omega) (by omega)),
      hone, if_neg (by omega), hilen]
  have hcycle : ThetaFixedDefs.cycleFrom inverse size = stem := by
    have hrec : IsLtrMax stem 0 := by intro index hi; omega
    have hc := cycleFrom_B_record_block stem hperm 0 stem.length
      (by omega) (le_refl _) hrec hnon (Or.inl rfl)
    simpa only [Nat.sub_zero, List.drop_zero, List.take_length, hfirst] using hc
  have hinverseTheta : ThetaFixedDefs.theta inverse = stem := by
    have hfilter : (List.range' 1 inverse.length).filter
        (fun value => decide (ThetaFixedDefs.IsLeader inverse value)) = [size] := by
      apply List.Pairwise.eq_of_mem_iff
        ((List.pairwise_lt_range' 1 (by omega : 0 < (1 : ℕ))).filter _)
        (by simp)
      intro value
      constructor
      · intro hv
        obtain ⟨hrange, hleader⟩ := List.mem_filter.mp hv
        obtain ⟨offset, ho, heq⟩ := List.mem_range'.mp hrange
        have hm := hmem value (by omega) (by rw [hilen] at ho; omega)
        by_contra hnot
        have hne : value ≠ size := by simpa using hnot
        have hindex := List.idxOf_lt_length_of_mem hm
        have hpositive : 0 < stem.idxOf value := by
          by_contra hz
          have hz' : stem.idxOf value = 0 := by omega
          have hv : stem.getD (stem.idxOf value) 0 = value := by
            rw [List.getD_eq_getElem _ 0 hindex]
            exact List.getElem_idxOf hindex
          rw [hz', hfirst] at hv
          exact hne hv.symm
        exact nonrecord_not_B_leader stem hperm value hm
          (hnon _ hpositive hindex) (decide_eq_true_eq.mp hleader)
      · intro hv
        have heq : value = size := by simpa using hv
        subst value
        apply List.mem_filter.mpr
        refine ⟨List.mem_range'.mpr ⟨size - 1, by rw [hilen]; omega, by omega⟩, ?_⟩
        apply decide_eq_true
        intro value hv
        rw [hcycle] at hv
        obtain ⟨offset, ho, heq⟩ := List.mem_range'.mp (hperm.mem_iff.mp hv)
        dsimp [size]
        omega
    unfold ThetaFixedDefs.theta
    rw [hfilter]
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hcycle
  have pattern (word : List ℕ) : Contains [1, 3, 2] [] 3 word ↔
      ∃ first middle last : Fin word.length, first < middle ∧ middle < last ∧
        word[first.val] < word[last.val] ∧ word[last.val] < word[middle.val] := by
    constructor
    · rintro ⟨values, hlt, _, hsub, _⟩
      change [values 1, values 3, values 2].Sublist word at hsub
      obtain ⟨positions, hp⟩ :=
        List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      have hp0 : word[(positions ⟨0, by simp⟩).val] = values 1 := by
        simpa using (hp ⟨0, by simp⟩).symm
      have hp1 : word[(positions ⟨1, by simp⟩).val] = values 3 := by
        simpa using (hp ⟨1, by simp⟩).symm
      have hp2 : word[(positions ⟨2, by simp⟩).val] = values 2 := by
        simpa using (hp ⟨2, by simp⟩).symm
      refine ⟨positions ⟨0, by simp⟩, positions ⟨1, by simp⟩,
        positions ⟨2, by simp⟩, positions.strictMono (by simp),
        positions.strictMono (by simp), ?_, ?_⟩
      · simpa only [hp0, hp2] using hlt 1 (by omega) (by omega)
      · simpa only [hp2, hp1] using hlt 2 (by omega) (by omega)
    · rintro ⟨first, middle, last, hfm, hml, hfl, hlm⟩
      let values : ℕ → ℕ := fun index => if index = 1 then word[first.val]
        else if index = 2 then word[last.val] else word[middle.val]
      have hsub : [word[first.val], word[middle.val], word[last.val]].Sublist word := by
        let positions : Fin 3 → Fin word.length := fun index =>
          if index.val = 0 then first else if index.val = 1 then middle else last
        have hmono : StrictMono positions := by
          intro left right hlt
          fin_cases left <;> fin_cases right <;> (simp_all [positions] <;> omega)
        apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
        refine ⟨OrderEmbedding.ofStrictMono positions hmono, ?_⟩
        intro index
        fin_cases index <;> simp [positions]
      refine ⟨values, ?_, ?_, ?_, by simp⟩
      · intro index hpositive hbound
        have hcases : index = 1 ∨ index = 2 := by omega
        rcases hcases with rfl | rfl <;> simp [values, hfl, hlm]
      · intro index hpositive hbound
        have hcases : index = 1 ∨ index = 2 ∨ index = 3 := by omega
        rcases hcases with rfl | rfl | rfl <;> simp [values]
      · simpa [values] using hsub
  have shift (word : List ℕ) :
      (¬ Contains [1, 3, 2] [] 3 (word.map (· + 1))) ↔
        ¬ Contains [1, 3, 2] [] 3 word := by
    apply not_congr
    rw [pattern, pattern]
    simp only [List.getElem_map]
    constructor
    · rintro ⟨first, middle, last, hfm, hml, hfl, hlm⟩
      refine ⟨⟨first.val, by simpa using first.isLt⟩,
        ⟨middle.val, by simpa using middle.isLt⟩,
        ⟨last.val, by simpa using last.isLt⟩, hfm, hml, ?_, ?_⟩
      · change word[first.val] < word[last.val]
        omega
      · change word[last.val] < word[middle.val]
        omega
    · rintro ⟨first, middle, last, hfm, hml, hfl, hlm⟩
      refine ⟨⟨first.val, by simp⟩,
        ⟨middle.val, by simp⟩,
        ⟨last.val, by simp⟩, hfm, hml, ?_, ?_⟩
      · change word[first.val] + 1 < word[last.val] + 1
        omega
      · change word[last.val] + 1 < word[middle.val] + 1
        omega
  have appendTop (word : List ℕ) (top : ℕ) (hb : ∀ value ∈ word, value ≤ top) :
      (¬ Contains [1, 3, 2] [] 3 (word ++ [top])) ↔
        ¬ Contains [1, 3, 2] [] 3 word := by
    rw [avoids132_append_iff]
    have hc : ∀ first middle, first < middle → middle < word.length →
        ¬ (word.getD first 0 < top ∧ top < word.getD middle 0) := by
      intro first middle hfm hm hcross
      have hm' : word.getD middle 0 ∈ word := by
        rw [List.getD_eq_getElem _ 0 hm]
        exact List.getElem_mem hm
      have hbound := hb _ hm'
      omega
    exact ⟨fun h => h.1, fun h => ⟨h, hc⟩⟩
  have appendOne (word : List ℕ) (hb : ∀ value ∈ word, 1 ≤ value) :
      (¬ Contains [1, 3, 2] [] 3 (word ++ [1])) ↔
        ¬ Contains [1, 3, 2] [] 3 word := by
    rw [avoids132_append_iff]
    have hc : ∀ first middle, first < middle → middle < word.length →
        ¬ (word.getD first 0 < 1 ∧ 1 < word.getD middle 0) := by
      intro first middle hfm hm hcross
      have hf : first < word.length := by omega
      have hf' : word.getD first 0 ∈ word := by
        rw [List.getD_eq_getElem _ 0 hf]
        exact List.getElem_mem hf
      have hbound := hb _ hf'
      omega
    exact ⟨fun h => h.1, fun h => ⟨h, hc⟩⟩
  have hstemBounds (value : ℕ) (hv : value ∈ stem) : 1 ≤ value ∧ value ≤ size := by
    obtain ⟨offset, ho, heq⟩ := List.mem_range'.mp (hperm.mem_iff.mp hv)
    dsimp [size]
    omega
  have hthetaBounds (value : ℕ) (hv : value ∈ ThetaFixedDefs.theta stem) :
      value ≤ size := by
    obtain ⟨leader, hl, hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨hlrange, hlprop⟩ := List.mem_filter.mp hl
    have hlb : leader ≤ size := by
      obtain ⟨offset, ho, heq⟩ := List.mem_range'.mp hlrange
      dsimp [size]
      omega
    have hleader := decide_eq_true_eq.mp hlprop
    exact (hleader value hv).trans hlb
  have hinverseScan := insertion_scan inverse hinversePerm
    (by rw [hilen]; dsimp [size]; omega) hinverseFirst
  have hPperm : (P parameter).Perm (List.range' 1 (size + 3)) := by
    rw [hconstructed]
    simpa only [hilen] using hinverseScan.1
  have hPavoid : (¬ Contains [1, 3, 2] [] 3 (P parameter)) ↔
      ¬ Contains [1, 3, 2] [] 3 inverse := by
    rw [hconstructed]
    exact hinverseScan.2.2.1
  have hparameterBounds (value : ℕ) (hv : value ∈ parameter) :
      1 ≤ value ∧ value ≤ size + 1 := by
    rcases List.mem_append.mp hv with hs | hs
    · have hb := hstemBounds _ hs
      omega
    · have heq : value = size + 1 := by simpa using hs
      omega
  have hparameterAvoid : (¬ Contains [1, 3, 2] [] 3 parameter) ↔
      ¬ Contains [1, 3, 2] [] 3 stem :=
    appendTop stem (size + 1) (fun value hv => by have hb := hstemBounds value hv; omega)
  have hthetaParameter : ThetaFixedDefs.theta parameter =
      ThetaFixedDefs.theta stem ++ [size + 1] :=
    ThetaIterateTail.theta_append_max stem hperm
  have hthetaParameterBounds (value : ℕ) (hv : value ∈ ThetaFixedDefs.theta parameter) :
      value ≤ size + 1 := by
    rw [hthetaParameter] at hv
    rcases List.mem_append.mp hv with hs | hs
    · have hb := hthetaBounds _ hs
      omega
    · have heq : value = size + 1 := by simpa using hs
      omega
  have hthetaParameterAvoid : (¬ Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta parameter)) ↔
      ¬ Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta stem) := by
    rw [hthetaParameter]
    exact appendTop _ _ (fun value hv => by have hb := hthetaBounds value hv; omega)
  have hcycles := P_cycle_reduction parameter hparameter (by rw [hplen]; omega)
  have hfirstIterate : (¬ Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta (P parameter))) ↔
      ¬ Contains [1, 3, 2] [] 3 stem := by
    rw [hcycles.1, List.cons_append]
    have htop : ∀ value ∈ parameter.map (· + 1) ++ [1], value < parameter.length + 2 := by
      intro value hv
      rcases List.mem_append.mp hv with hm | hm
      · obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
        have hb := hparameterBounds old ho
        omega
      · have heq : value = 1 := by simpa using hm
        omega
    rw [avoids132_cons_max_append_iff _ _ _ htop]
    have hnoone : ∀ first middle, first < middle → middle < (parameter.map (· + 1)).length →
        ¬ ((parameter.map (· + 1)).getD first 0 < 1 ∧
          1 < (parameter.map (· + 1)).getD middle 0) := by
      intro first middle hfm hm hcross
      have hf : first < (parameter.map (· + 1)).length := by omega
      rw [List.getD_eq_getElem _ 0 hf, List.getElem_map] at hcross
      omega
    constructor
    · intro ha
      exact hparameterAvoid.mp ((shift parameter).mp ha.1)
    · intro ha
      exact ⟨(shift parameter).mpr (hparameterAvoid.mpr ha), hnoone⟩
  have hsecondIterate :
      (¬ Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta (ThetaFixedDefs.theta (P parameter)))) ↔
        ¬ Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta stem) := by
    rw [hcycles.2.1, show [parameter.length + 2, 1] = [parameter.length + 2] ++ [1] by rfl,
      ← List.append_assoc]
    rw [appendOne _ (by
      intro value hv
      rcases List.mem_append.mp hv with hm | hm
      · obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
        omega
      · have heq : value = parameter.length + 2 := by simpa using hm
        omega)]
    rw [appendTop _ _ (by
      intro value hv
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hv
      have hb := hthetaParameterBounds old ho
      omega), shift, hthetaParameterAvoid]
  have hmember (word : List ℕ) (length : ℕ) (hp : word.Perm (List.range' 1 length)) :
      word ∈ ThetaIterateDefs.iterateAvoiders length 2 [1, 3, 2] ↔
        ¬ Contains [1, 3, 2] [] 3 word ∧
        ¬ Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta word) ∧
        ¬ Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta (ThetaFixedDefs.theta word)) := by
    constructor
    · intro hm
      exact ⟨by simpa using hm.2 0 (by omega),
        by simpa using hm.2 1 (by omega),
        by simpa [Function.iterate_succ_apply'] using hm.2 2 (by omega)⟩
    · rintro ⟨hzero, hone, htwo⟩
      refine ⟨hp, ?_⟩
      intro count hc
      have hcases : count = 0 ∨ count = 1 ∨ count = 2 := by omega
      rcases hcases with rfl | rfl | rfl
      · simpa using hzero
      · simpa using hone
      · simpa [Function.iterate_succ_apply'] using htwo
  refine ⟨by simpa only [hilen] using hinverseFirst, hinverseTheta, ?_⟩
  change P parameter ∈ ThetaIterateDefs.iterateAvoiders (size + 3) 2 [1, 3, 2] ↔
    inverse ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2]
  rw [hmember _ _ hPperm, hmember _ _ (by simpa only [hilen] using hinversePerm),
    hPavoid, hfirstIterate, hsecondIterate, hinverseTheta]

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateLastEndpoint
