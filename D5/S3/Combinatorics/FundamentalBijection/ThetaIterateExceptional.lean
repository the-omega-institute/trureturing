/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateExceptional
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateExceptional
   mirror-E: none(waiver:cyclic-last-endpoint-construction)
   anchors: []
   utility: none
   digest: The cyclic-shift stem survives the last-endpoint reduction in every size. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycleReduction
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateTail
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateVFamilies

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateExceptional

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArcherCyclicDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaFixedDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycle
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycleReduction

open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse

local notation "B" =>
  (fun word : List ℕ => List.map (hat word) (List.range' 1 (List.length word)))

set_option maxHeartbeats 2400000 in
theorem cyclic_last_endpoint (size : ℕ) (hsize : 3 ≤ size) :
    let stem := List.range' 2 (size - 1) ++ [1]
    let inverse := size :: List.range' 2 (size - 2) ++ [1]
    theta stem = size :: List.range' 1 (size - 1) ∧
      theta inverse = stem ∧
        inverse ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2] ∧
          P (stem ++ [size + 1]) ∈
            ThetaIterateDefs.iterateAvoiders (size + 3) 2 [1, 3, 2] ∧
          (4 ≤ size →
            let earlier := P (List.range' 1 (size - 2))
            theta earlier = inverse ∧
            earlier ∈ ThetaIterateDefs.iterateAvoiders size 5 [1, 3, 2] ∧
            earlier ∉ ThetaIterateDefs.iterateAvoiders size 6 [1, 3, 2] ∧
            inverse ∈ ThetaIterateDefs.iterateAvoiders size 4 [1, 3, 2] ∧
            inverse ∉ ThetaIterateDefs.iterateAvoiders size 5 [1, 3, 2] ∧
            stem ∈ ThetaIterateDefs.iterateAvoiders size 3 [1, 3, 2] ∧
            stem ∉ ThetaIterateDefs.iterateAvoiders size 4 [1, 3, 2]) := by
  have pattern_indices (word : List ℕ) (hp : Contains [1, 3, 2] [] 3 word) :
      ∃ first middle last : Fin word.length, first < middle ∧ middle < last ∧
        word[first.val] < word[last.val] ∧ word[last.val] < word[middle.val] := by
    obtain ⟨values, hvalues, _, hsub, _⟩ := hp
    change List.Sublist [values 1, values 3, values 2] word at hsub
    obtain ⟨positions, hpositions⟩ :=
      List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    have hfirst : word[(positions ⟨0, by simp⟩).val] = values 1 := by
      simpa using (hpositions ⟨0, by simp⟩).symm
    have hmiddle : word[(positions ⟨1, by simp⟩).val] = values 3 := by
      simpa using (hpositions ⟨1, by simp⟩).symm
    have hlast : word[(positions ⟨2, by simp⟩).val] = values 2 := by
      simpa using (hpositions ⟨2, by simp⟩).symm
    refine ⟨positions ⟨0, by simp⟩, positions ⟨1, by simp⟩,
      positions ⟨2, by simp⟩, positions.strictMono (by simp),
      positions.strictMono (by simp), ?_, ?_⟩
    · simpa only [hfirst, hlast] using hvalues 1 (by omega) (by omega)
    · simpa only [hlast, hmiddle] using hvalues 2 (by omega) (by omega)
  let stem := List.range' 2 (size - 1) ++ [1]
  let parameter := stem ++ [size + 1]
  let successor := size :: List.range' 1 (size - 1)
  have hlen : stem.length = size := by simp [stem]; omega
  have hplen : parameter.length = size + 1 := by simp [parameter, hlen]
  have hslen : successor.length = size := by simp [successor]; omega
  have hperm : stem.Perm (List.range' 1 size) := by
    have hrange : List.range' 1 size = 1 :: List.range' 2 (size - 1) := by
      simpa only [show size - 1 + 1 = size by omega] using
        (List.range'_succ (s := 1) (n := size - 1))
    rw [hrange]
    exact List.perm_append_singleton 1 (List.range' 2 (size - 1))
  have hparameter : parameter.Perm (List.range' 1 parameter.length) := by
    rw [hplen, show List.range' 1 (size + 1) =
      List.range' 1 size ++ [size + 1] by
        simpa only [one_mul, Nat.add_comm] using
          (List.range'_concat (s := 1) (n := size) (step := 1))]
    exact hperm.append (List.Perm.refl _)
  have hget (index : ℕ) (hi : index < size) :
      stem.getD index 0 = if index < size - 1 then index + 2 else 1 := by
    by_cases hlow : index < size - 1
    · rw [if_pos hlow]
      change (List.range' 2 (size - 1) ++ [1]).getD index 0 = index + 2
      rw [List.getD_append _ _ _ _ (by simp only [List.length_range']; omega)]
      rw [List.getD_eq_getElem _ 0 (by simp only [List.length_range']; omega)]
      simp only [List.getElem_range'_1]
      omega
    · rw [if_neg hlow]
      have heq : index = size - 1 := by omega
      simp [stem, heq]
  have himage (value : ℕ) (hv : 1 ≤ value) (hbound : value ≤ size) :
      image stem value = if value < size then value + 1 else 1 := by
    unfold image
    rw [hget (value - 1) (by omega)]
    split_ifs <;> omega
  have horbit (power : ℕ) (hp : power ≤ size) :
      (image stem)^[power] size = if power = 0 then size else power := by
    induction power with
    | zero => simp
    | succ power ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      by_cases hz : power = 0
      · subst power
        rw [if_pos rfl, himage size (by omega) (by omega), if_neg (by omega)]
        simp
      · rw [if_neg hz, himage power (by omega) (by omega), if_pos (by omega)]
        simp
  have hcycle : cycleFrom stem size = successor := by
    let orbit := (List.range size).map (fun power => (image stem)^[power + 1] size)
    have holength : orbit.length = size := by simp [orbit]
    have hhit : orbit[size - 1]'(by omega) = size := by
      simp only [orbit, List.getElem_map, List.getElem_range]
      rw [horbit _ (by omega), if_neg (by omega)]
      omega
    have hgood : ∀ value ∈ orbit.take (size - 1), decide (value ≠ size) = true := by
      intro value hv
      obtain ⟨index, hi, heq⟩ := List.mem_iff_getElem.mp hv
      have hib : index < size - 1 := by simpa [holength] using hi
      rw [← heq]
      simp only [List.getElem_take, orbit, List.getElem_map, List.getElem_range]
      rw [horbit _ (by omega), if_neg (by omega), decide_eq_true_eq]
      omega
    have htake : orbit.takeWhile (· ≠ size) = orbit.take (size - 1) := by
      conv_lhs => rw [← List.take_append_drop (size - 1) orbit]
      rw [List.takeWhile_append_of_pos hgood,
        List.drop_eq_getElem_cons (by omega : size - 1 < orbit.length), hhit]
      simp
    unfold cycleFrom
    rw [hlen]
    change size :: orbit.takeWhile (· ≠ size) = successor
    rw [htake]
    congr 1
    apply List.ext_getElem
    · simp [holength]
    · intro index hi hj
      have hib : index < size - 1 := by simpa using hj
      simp only [List.getElem_take, orbit, List.getElem_map, List.getElem_range,
        List.getElem_range'_1]
      rw [horbit _ (by omega), if_neg (by omega)]
      omega
  have hleaders (value : ℕ) (hv : value ∈ List.range' 1 size) :
      IsLeader stem value ↔ value = size := by
    obtain ⟨offset, ho, heq⟩ := List.mem_range'.mp hv
    have hpositive : 1 ≤ value := by omega
    have hbound : value ≤ size := by omega
    constructor
    · intro hleader
      by_contra hne
      have hlt : value < size := by omega
      have hrun (power : ℕ) (hp : power ≤ size - value) :
          (image stem)^[power] value = value + power := by
        induction power with
        | zero => simp
        | succ power ih =>
          rw [Function.iterate_succ_apply', ih (by omega),
            himage _ (by omega) (by omega), if_pos (by omega)]
          omega
      let orbit := (List.range size).map (fun power => (image stem)^[power + 1] value)
      have hgood : ∀ entry ∈ orbit.take (size - value), decide (entry ≠ value) = true := by
        intro entry he
        obtain ⟨index, hi, heq⟩ := List.mem_iff_getElem.mp he
        have hib : index < size - value := by simpa [orbit] using hi
        rw [← heq]
        simp only [List.getElem_take, orbit, List.getElem_map, List.getElem_range]
        rw [hrun _ (by omega), decide_eq_true_eq]
        omega
      have hmem : size ∈ orbit.take (size - value) := by
        have hi : size - value - 1 < (orbit.take (size - value)).length := by
          simp [orbit]
          omega
        have heq : (orbit.take (size - value))[size - value - 1] = size := by
          simp only [List.getElem_take, orbit, List.getElem_map, List.getElem_range]
          rw [hrun _ (by omega)]
          omega
        exact List.mem_iff_getElem.mpr ⟨size - value - 1, hi, heq⟩
      have hmemcycle : size ∈ cycleFrom stem value := by
        unfold cycleFrom
        rw [hlen]
        change size ∈ value :: orbit.takeWhile (· ≠ value)
        apply List.mem_cons_of_mem
        rw [← List.take_append_drop (size - value) orbit,
          List.takeWhile_append_of_pos hgood]
        exact List.mem_append_left _ hmem
      have := hleader size hmemcycle
      omega
    · rintro rfl
      rw [IsLeader, hcycle]
      intro entry he
      rcases List.mem_cons.mp he with rfl | he
      · omega
      · obtain ⟨index, hi, heq⟩ := List.mem_range'.mp he
        omega
  have htheta : theta stem = successor := by
    unfold theta
    rw [hlen]
    have hfilter : (List.range' 1 size).filter (fun value => decide (IsLeader stem value)) =
        [size] := by
      have heq : (List.range' 1 size).filter (fun value => decide (IsLeader stem value)) =
          (List.range' 1 size).filter (fun value => decide (value = size)) := by
        apply List.filter_congr
        intro value hv
        simp only [hleaders value hv]
      rw [heq, List.filter_eq]
      have hm : size ∈ List.range' 1 size :=
        List.mem_range'.mpr ⟨size - 1, by omega, by omega⟩
      rw [(List.nodup_iff_count_eq_one.mp List.nodup_range') size hm]
      simp
    rw [hfilter]
    simpa using hcycle
  have hparameterGet (index : ℕ) (hi : index < size + 1) :
      parameter.getD index 0 =
        if index < size - 1 then index + 2 else if index = size - 1 then 1 else size + 1 := by
    by_cases hsmall : index < size
    · rw [show parameter.getD index 0 = stem.getD index 0 from
        List.getD_append _ _ _ _ (by omega), hget index hsmall]
      split_ifs <;> omega
    · have heq : index = size := by omega
      simp [parameter, hlen, heq, show ¬ size < size - 1 by omega,
        show size ≠ size - 1 by omega]
  have hidx (value index : ℕ) (hi : index < size + 1)
      (heq : parameter.getD index 0 = value) : parameter.idxOf value = index := by
    have hnd : parameter.Nodup := hparameter.nodup_iff.mpr List.nodup_range'
    rw [List.getD_eq_getElem _ 0 (by omega)] at heq
    rw [← heq]
    exact List.get_idxOf hnd ⟨index, by omega⟩
  have hbget (index : ℕ) (hi : index < size + 1) :
      (b parameter).getD index 0 =
        if index = 0 then size + 2 else if index < size - 1 then index + 3
        else if index = size - 1 then 2 else 1 := by
    rw [b, List.getD_eq_getElem _ 0 (by simp [hplen]; omega), List.getElem_map,
      List.getElem_range'_1]
    rw [Nat.add_comm 1 index]
    by_cases hz : index = 0
    · subst index
      rw [hidx 1 (size - 1) (by omega) (by rw [hparameterGet _ (by omega)]; simp),
        if_pos (by omega), hparameterGet _ (by omega)]
      split_ifs <;> omega
    · by_cases hlow : index < size - 1
      · rw [hidx (index + 1) (index - 1) (by omega) (by
          rw [hparameterGet _ (by omega), if_pos (by omega)]; omega),
          if_pos (by omega), hparameterGet _ (by omega), if_neg hz, if_pos hlow]
        split_ifs <;> omega
      · by_cases hpen : index = size - 1
        · rw [hidx (index + 1) (size - 2) (by omega) (by
            rw [hparameterGet _ (by omega), if_pos (by omega)]; omega),
            if_pos (by omega), hparameterGet _ (by omega), if_neg hz,
            if_neg hlow, if_pos hpen]
          split_ifs <;> omega
        · have heq : index = size := by omega
          rw [hidx (index + 1) size (by omega) (by
            rw [hparameterGet _ (by omega)]; split_ifs <;> omega),
            if_neg (by omega), if_neg hz, if_neg hlow, if_neg hpen]
  have hstemAvoid : ¬ Contains [1, 3, 2] [] 3 stem := by
    intro hp
    obtain ⟨first, middle, last, hfm, hml, hfl, hlm⟩ := pattern_indices _ hp
    have hf : first.val < size := by simpa [hlen] using first.isLt
    have hm : middle.val < size := by simpa [hlen] using middle.isLt
    have hl : last.val < size := by simpa [hlen] using last.isLt
    simp only [← List.getD_eq_getElem _ 0 first.isLt,
      ← List.getD_eq_getElem _ 0 middle.isLt,
      ← List.getD_eq_getElem _ 0 last.isLt, hget _ hf, hget _ hm, hget _ hl] at hfl hlm
    split_ifs at hfl hlm <;> omega
  have hsuccessorAvoid : ¬ Contains [1, 3, 2] [] 3 successor := by
    intro hp
    obtain ⟨first, middle, last, hfm, hml, hfl, hlm⟩ := pattern_indices _ hp
    have hsget (index : ℕ) (hi : index < size) :
        successor.getD index 0 = if index = 0 then size else index := by
      cases index with
      | zero => simp [successor]
      | succ index =>
        simp only [successor, List.getD_cons_succ, Nat.succ_ne_zero, if_false]
        rw [List.getD_eq_getElem _ 0 (by simp; omega)]
        simp only [List.getElem_range'_1]
        omega
    have hf : first.val < size := by simpa [hslen] using first.isLt
    have hm : middle.val < size := by simpa [hslen] using middle.isLt
    have hl : last.val < size := by simpa [hslen] using last.isLt
    simp only [← List.getD_eq_getElem _ 0 first.isLt,
      ← List.getD_eq_getElem _ 0 middle.isLt,
      ← List.getD_eq_getElem _ 0 last.isLt,
      hsget _ hf, hsget _ hm, hsget _ hl] at hfl hlm
    split_ifs at hfl hlm <;> omega
  have happend (word : List ℕ) (hp : word.Perm (List.range' 1 size))
      (ha : ¬ Contains [1, 3, 2] [] 3 word) :
      ¬ Contains [1, 3, 2] [] 3 (word ++ [size + 1]) := by
    rw [ThetaIterateScan.avoids132_append_iff]
    refine ⟨ha, ?_⟩
    intro first middle hfm hm hcross
    have hb : word.getD middle 0 ≤ size := by
      have hv : word.getD middle 0 ∈ word := by
        rw [List.getD_eq_getElem _ 0 hm]
        exact List.getElem_mem hm
      obtain ⟨offset, ho, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hv)
      omega
    omega
  have hsuccessorPerm : successor.Perm (List.range' 1 size) := by
    have heq : List.range' 1 size = List.range' 1 (size - 1) ++ [size] := by
      simpa only [one_mul, show size - 1 + 1 = size by omega,
        show 1 + (size - 1) = size by omega] using
        (List.range'_concat (s := 1) (n := size - 1) (step := 1))
    rw [heq]
    exact (List.perm_append_singleton size (List.range' 1 (size - 1))).symm
  have hthetaParameter : theta parameter = successor ++ [size + 1] := by
    simpa only [hlen, htheta] using
      (ThetaIterateTail.theta_append_max stem (by simpa [hlen] using hperm))
  have hbavoid : ¬ Contains [1, 3, 2] [] 3 (b parameter) := by
    intro hp
    obtain ⟨first, middle, last, hfm, hml, hfl, hlm⟩ := pattern_indices _ hp
    have hblen : (b parameter).length = size + 1 := by simp [b, hplen]
    have hf : first.val < size + 1 := by simpa [hblen] using first.isLt
    have hm : middle.val < size + 1 := by simpa [hblen] using middle.isLt
    have hl : last.val < size + 1 := by simpa [hblen] using last.isLt
    simp only [← List.getD_eq_getElem _ 0 first.isLt,
      ← List.getD_eq_getElem _ 0 middle.isLt,
      ← List.getD_eq_getElem _ 0 last.isLt,
      hbget _ hf, hbget _ hm, hbget _ hl] at hfl hlm
    split_ifs at hfl hlm <;> omega
  have hcross : ∀ first middle, first < middle → middle < parameter.length →
      ¬ ((b parameter).getD first 0 < parameter.getD 0 0 + 1 ∧
        parameter.getD 0 0 + 1 < (b parameter).getD middle 0) := by
    intro first middle hfm hm hc
    have hm' : middle < size + 1 := by omega
    have hf' : first < size + 1 := by omega
    rw [hparameterGet 0 (by omega), if_pos (by omega), hbget first hf',
      hbget middle hm'] at hc
    split_ifs at hc <;> omega
  let inverse := size :: List.range' 2 (size - 2) ++ [1]
  have hilen : inverse.length = size := by simp [inverse]; omega
  have hmiddleRange : List.range' 2 (size - 1) =
      List.range' 2 (size - 2) ++ [size] := by
    simpa only [one_mul, show size - 2 + 1 = size - 1 by omega,
      show 2 + (size - 2) = size by omega] using
        (List.range'_concat (s := 2) (n := size - 2) (step := 1))
  have hinversePerm : inverse.Perm (List.range' 1 size) := by
    have hrange : List.range' 1 size = 1 :: (List.range' 2 (size - 2) ++ [size]) := by
      rw [← hmiddleRange]
      simpa only [show size - 1 + 1 = size by omega] using
        (List.range'_succ (s := 1) (n := size - 1) (step := 1))
    rw [hrange]
    exact (List.perm_append_singleton 1 (size :: List.range' 2 (size - 2))).trans
      (List.Perm.cons 1 (List.perm_append_singleton size (List.range' 2 (size - 2))).symm)
  have hiFirst : image inverse 1 = size := by simp [image, inverse]
  have hiMax : image inverse size = 1 := by
    unfold image
    simp only [inverse, List.cons_append]
    rw [show size - 1 = (size - 2) + 1 by omega, List.getD_cons_succ]
    simp
  have hiFixed (value : ℕ) (hv : 2 ≤ value) (hbound : value < size) :
      image inverse value = value := by
    unfold image
    simp only [inverse, List.cons_append]
    rw [show value - 1 = (value - 2) + 1 by omega, List.getD_cons_succ]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_range']; omega),
      List.getD_eq_getElem _ 0 (by simp only [List.length_range']; omega)]
    simp only [List.getElem_range'_1]
    omega
  have hrangeSplit : List.range size = 0 :: 1 :: List.range' 2 (size - 2) := by
    rw [List.range_eq_range']
    have hfirst : List.range' 0 size = 0 :: List.range' 1 (size - 1) := by
      simpa only [show size - 1 + 1 = size by omega, Nat.zero_add] using
        (List.range'_succ (s := 0) (n := size - 1) (step := 1))
    have hsecond : List.range' 1 (size - 1) = 1 :: List.range' 2 (size - 2) := by
      simpa only [show size - 2 + 1 = size - 1 by omega] using
        (List.range'_succ (s := 1) (n := size - 2) (step := 1))
    rw [hfirst, hsecond]
  have hiCycleMax : cycleFrom inverse size = [size, 1] := by
    unfold cycleFrom
    rw [hilen, hrangeSplit]
    simp only [List.map_cons, Function.iterate_succ_apply', Function.iterate_zero_apply,
      hiMax, hiFirst, List.takeWhile_cons, decide_eq_true_eq]
    simp [show 1 ≠ size by omega]
  have hiCycleOne : cycleFrom inverse 1 = [1, size] := by
    unfold cycleFrom
    rw [hilen, hrangeSplit]
    simp only [List.map_cons, Function.iterate_succ_apply', Function.iterate_zero_apply,
      hiMax, hiFirst, List.takeWhile_cons, decide_eq_true_eq]
    simp [show size ≠ 1 by omega]
  have hiCycleFixed (value : ℕ) (hv : 2 ≤ value) (hbound : value < size) :
      cycleFrom inverse value = [value] := by
    have hiter (power : ℕ) : (image inverse)^[power] value = value := by
      induction power with
      | zero => rfl
      | succ power ih => rw [Function.iterate_succ_apply', ih, hiFixed value hv hbound]
    unfold cycleFrom
    simp_rw [hiter]
    simp
  have hiLeaders (value : ℕ) (hv : value ∈ List.range' 1 size) :
      IsLeader inverse value ↔ value ≠ 1 := by
    obtain ⟨offset, ho, heq⟩ := List.mem_range'.mp hv
    by_cases hone : value = 1
    · rw [hone, IsLeader, hiCycleOne]
      simp [show ¬ size ≤ 1 by omega]
    · by_cases hmax : value = size
      · rw [hmax, IsLeader, hiCycleMax]
        simp [show 1 ≤ size by omega, show size ≠ 1 by omega]
      · rw [IsLeader, hiCycleFixed value (by omega) (by omega)]
        simp [hone]
  have hthetaInverse : theta inverse = stem := by
    unfold theta
    rw [hilen]
    have hfilter : (List.range' 1 size).filter
        (fun value => decide (IsLeader inverse value)) = List.range' 2 (size - 1) := by
      have heq : (List.range' 1 size).filter
          (fun value => decide (IsLeader inverse value)) =
          (List.range' 1 size).filter (fun value => decide (value ≠ 1)) := by
        apply List.filter_congr
        intro value hv
        simp only [hiLeaders value hv]
      rw [heq, show List.range' 1 size = 1 :: List.range' 2 (size - 1) by
        simpa only [show size - 1 + 1 = size by omega] using
          (List.range'_succ (s := 1) (n := size - 1))]
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      apply List.filter_eq_self.mpr
      intro value hv
      obtain ⟨offset, _, heq⟩ := List.mem_range'.mp hv
      simp only [decide_eq_true_eq]
      omega
    rw [hfilter, hmiddleRange, List.flatMap_append]
    have hfixed : (List.range' 2 (size - 2)).flatMap (cycleFrom inverse) =
        List.range' 2 (size - 2) := by
      have heq : (List.range' 2 (size - 2)).flatMap (cycleFrom inverse) =
          (List.range' 2 (size - 2)).flatMap (fun value => [value]) := by
        apply List.flatMap_congr
        intro value hv
        obtain ⟨offset, ho, heq⟩ := List.mem_range'.mp hv
        exact hiCycleFixed value (by omega) (by omega)
      simpa using heq
    rw [hfixed]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hiCycleMax]
    change List.range' 2 (size - 2) ++ [size, 1] = List.range' 2 (size - 1) ++ [1]
    rw [hmiddleRange, List.append_assoc]
    rfl
  have hinverseAvoid : ¬ Contains [1, 3, 2] [] 3 inverse := by
    intro hp
    obtain ⟨first, middle, last, hfm, hml, hfl, hlm⟩ := pattern_indices _ hp
    have hiGet (index : ℕ) (hi : index < size) :
        inverse.getD index 0 =
          if index = 0 then size else if index < size - 1 then index + 1 else 1 := by
      cases index with
      | zero => simp [inverse]
      | succ index =>
        simp only [inverse, List.cons_append, List.getD_cons_succ,
          Nat.succ_ne_zero, if_false]
        by_cases hlow : index < size - 2
        · rw [List.getD_append _ _ _ _ (by simp only [List.length_range']; omega),
            List.getD_eq_getElem _ 0 (by simp only [List.length_range']; omega)]
          simp only [List.getElem_range'_1, if_pos (by omega : index + 1 < size - 1)]
          omega
        · have heq : index = size - 2 := by omega
          simp [heq, show ¬ (size - 2) + 1 < size - 1 by omega]
    have hf : first.val < size := by simpa [hilen] using first.isLt
    have hm : middle.val < size := by simpa [hilen] using middle.isLt
    have hl : last.val < size := by simpa [hilen] using last.isLt
    simp only [← List.getD_eq_getElem _ 0 first.isLt,
      ← List.getD_eq_getElem _ 0 middle.isLt,
      ← List.getD_eq_getElem _ 0 last.isLt,
      hiGet _ hf, hiGet _ hm, hiGet _ hl] at hfl hlm
    split_ifs at hfl hlm <;> omega
  have hinverseMember : inverse ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2] := by
    refine ⟨hinversePerm, ?_⟩
    intro power hp
    have hcases : power = 0 ∨ power = 1 ∨ power = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simpa using hinverseAvoid
    · simpa [hthetaInverse] using hstemAvoid
    · simpa [Function.iterate_succ_apply', hthetaInverse, htheta] using hsuccessorAvoid
  refine ⟨htheta, hthetaInverse, hinverseMember, ?_, ?_⟩
  · have htest := (P_cycle_reduction parameter hparameter (by omega)).2.2.1
    have hmember := htest.mpr ⟨happend stem hperm hstemAvoid, ?_, hbavoid, hcross⟩
    · simpa only [hplen, Nat.add_assoc] using hmember
    · rw [hthetaParameter]
      exact happend successor hsuccessorPerm hsuccessorAvoid
  · intro hfour
    let parameter := List.range' 1 (size - 2)
    let earlier := P parameter
    let reverse := (List.range' 1 size).reverse
    have hparameterLength : parameter.length = size - 2 := by simp [parameter]
    have hparameterPerm : parameter.Perm (List.range' 1 parameter.length) := by
      simp only [hparameterLength]
      exact List.Perm.refl _
    have hshiftMap : parameter.map (· + 1) = List.range' 2 (size - 2) := by
      apply List.ext_getElem
      · simp [parameter]
      · intro index hleft hright
        simp [parameter]
        omega
    have hthetaEarlier : theta earlier = inverse := by
      have hcycle := (P_cycle_reduction parameter hparameterPerm (by omega)).1
      simpa only [hparameterLength, show size - 2 + 2 = size by omega,
        hshiftMap] using hcycle
    have hcanonical : earlier =
        (List.range' 1 inverse.length).map (hat inverse) := by
      change P parameter = _
      unfold P
      rw [hparameterLength, show size - 2 + 2 = size by omega, hshiftMap]
    have hvalidInverse : inverse.Perm (List.range' 1 inverse.length) := by
      simpa only [hilen] using hinversePerm
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
    have hpermEarlier : earlier.Perm (List.range' 1 size) := by
      rw [hcanonical]
      simpa only [hilen] using
        B_perm inverse hvalidInverse
    have hlengthEarlier : earlier.length = size := by
      simpa using hpermEarlier.length_eq
    have himages := (ThetaIterateCycleReduction.P_cycle_reduction parameter hparameterPerm
      (by omega)).2.2.2
    have hearlierGet (index : ℕ) (hindex : index < size) :
        earlier.getD index 0 =
          if index = 0 then size else if index < size - 2 then index + 2
          else if index = size - 2 then 1 else 2 := by
      by_cases hzero : index = 0
      · subst index
        simpa only [hparameterLength, show size - 2 + 2 = size by omega,
          if_pos rfl, ite_true] using himages.1
      · by_cases hfinal : index = size - 1
        · subst index
          have hlast := himages.2.1
          rw [hparameterLength, show size - 2 + 1 = size - 1 by omega] at hlast
          have hhead : parameter.getD 0 0 = 1 := by
            rw [List.getD_eq_getElem _ 0 (by simp [parameter]; omega)]
            simp [parameter]
          simpa only [hhead, show size - 1 ≠ 0 by omega,
            show ¬size - 1 < size - 2 by omega,
            show size - 1 ≠ size - 2 by omega, if_false] using hlast
        · have hmember : index ∈ parameter := by
            exact List.mem_range'.mpr ⟨index - 1, by omega, by omega⟩
          have hidx : parameter.idxOf index = index - 1 := by
            have hnd : parameter.Nodup := by exact List.nodup_range'
            have hvalue : parameter[index - 1]'(by simp [parameter]; omega) = index := by
              simp [parameter]
              omega
            have hlookup := List.get_idxOf hnd ⟨index - 1, by simp [parameter]; omega⟩
            change parameter.idxOf parameter[index - 1] = index - 1 at hlookup
            simpa only [hvalue] using hlookup
          have hedge := himages.2.2 index hmember
          rw [hidx, hparameterLength] at hedge
          by_cases hsmall : index < size - 2
          · rw [if_pos (by omega), List.getD_eq_getElem parameter 0
                (by simp only [hparameterLength]; omega),
              List.getElem_range'_1] at hedge
            rw [if_neg hzero, if_pos hsmall]
            change (P parameter).getD index 0 = index + 2
            omega
          · have hequal : index = size - 2 := by omega
            simpa only [if_neg (by omega : ¬index - 1 + 1 < size - 2),
              if_neg hzero, if_neg hsmall, if_pos hequal] using hedge
    have hearlierAvoid : ¬ Contains [1, 3, 2] [] 3 earlier := by
      intro hcontains
      obtain ⟨first, middle, last, hfirstMiddle, hmiddleLast, hfirstLast, hlastMiddle⟩ :=
        pattern_indices earlier hcontains
      have hf : first.val < size := by simpa only [hlengthEarlier] using first.isLt
      have hm : middle.val < size := by simpa only [hlengthEarlier] using middle.isLt
      have hl : last.val < size := by simpa only [hlengthEarlier] using last.isLt
      simp only [← List.getD_eq_getElem _ 0 first.isLt,
        ← List.getD_eq_getElem _ 0 middle.isLt,
        ← List.getD_eq_getElem _ 0 last.isLt,
        hearlierGet _ hf, hearlierGet _ hm, hearlierGet _ hl] at hfirstLast hlastMiddle
      split_ifs at hfirstLast hlastMiddle <;> omega
    have hreversePerm : reverse.Perm (List.range' 1 size) := List.reverse_perm _
    have hreverseLength : reverse.length = size := by simp [reverse]
    have hreverseFirst : reverse.getD 0 0 = size := by
      rw [List.getD_eq_getElem _ 0 (by simp [reverse]; omega)]
      simp only [reverse, List.getElem_reverse, List.length_range', List.getElem_range'_1]
      omega
    have hreverseLast : reverse.getD (size - 1) 0 = 1 := by
      rw [List.getD_eq_getElem _ 0 (by simp [reverse]; omega)]
      simp only [reverse, List.getElem_reverse, List.length_range', List.getElem_range'_1]
      omega
    have hreverseData := ThetaIterateVFamilies.V_family size (by omega)
    have hreverseMember := (hreverseData.2.2.1 reverse hreversePerm
      hreverseFirst hreverseLast).mpr rfl
    have hreverseValid : reverse.Perm (List.range' 1 reverse.length) := by
      simpa only [hreverseLength] using hreversePerm
    have hreverseTests := (P_cycle_reduction reverse hreverseValid (by omega)).2.2.1.mp
      (by simpa only [hreverseLength] using hreverseMember)
    have hstop : Contains [1, 3, 2] [] 3 (theta (theta reverse)) :=
      hreverseData.2.2.2 hfour
    have hthetaSuccessor : theta successor = reverse :=
      (ThetaIterateUFamilies.U_family size hfour).2.1
    have hearlierMember : earlier ∈ ThetaIterateDefs.iterateAvoiders size 5 [1, 3, 2] := by
      refine ⟨hpermEarlier, ?_⟩
      intro power hpower
      change ¬ Contains [1, 3, 2] [] 3 (theta^[power] earlier)
      have hcases : power = 0 ∨ power = 1 ∨ power = 2 ∨ power = 3 ∨
          power = 4 ∨ power = 5 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa using hearlierAvoid
      · simpa only [Function.iterate_one, hthetaEarlier] using hinverseAvoid
      · rw [Function.iterate_succ_apply, hthetaEarlier]
        simpa only [Function.iterate_one, hthetaInverse] using hstemAvoid
      · rw [Function.iterate_succ_apply, hthetaEarlier,
          Function.iterate_succ_apply, hthetaInverse]
        simpa only [Function.iterate_one, htheta] using hsuccessorAvoid
      · rw [Function.iterate_succ_apply, hthetaEarlier,
          Function.iterate_succ_apply, hthetaInverse, Function.iterate_succ_apply, htheta]
        simpa only [Function.iterate_one, hthetaSuccessor] using hreverseTests.1
      · rw [Function.iterate_succ_apply, hthetaEarlier,
          Function.iterate_succ_apply, hthetaInverse, Function.iterate_succ_apply, htheta,
          Function.iterate_succ_apply, hthetaSuccessor]
        simpa only [Function.iterate_one] using hreverseTests.2.1
    have hinverseHigher : inverse ∈ ThetaIterateDefs.iterateAvoiders size 4 [1, 3, 2] := by
      refine ⟨hinversePerm, ?_⟩
      intro power hpower
      have havoids := hearlierMember.2 (power + 1) (by omega)
      simpa only [Function.iterate_succ_apply, hthetaEarlier] using havoids
    have hstemHigher : stem ∈ ThetaIterateDefs.iterateAvoiders size 3 [1, 3, 2] := by
      refine ⟨hperm, ?_⟩
      intro power hpower
      have havoids := hinverseHigher.2 (power + 1) (by omega)
      simpa only [Function.iterate_succ_apply, hthetaInverse] using havoids
    refine ⟨hthetaEarlier, hearlierMember, ?_, hinverseHigher, ?_, hstemHigher, ?_⟩
    · intro hmember
      have havoids := hmember.2 6 (by omega)
      rw [Function.iterate_succ_apply, hthetaEarlier, Function.iterate_succ_apply,
        hthetaInverse, Function.iterate_succ_apply, htheta,
        Function.iterate_succ_apply, hthetaSuccessor] at havoids
      exact havoids hstop
    · intro hmember
      have havoids := hmember.2 5 (by omega)
      rw [Function.iterate_succ_apply, hthetaInverse, Function.iterate_succ_apply,
        htheta, Function.iterate_succ_apply, hthetaSuccessor] at havoids
      exact havoids hstop
    · intro hmember
      have havoids := hmember.2 4 (by omega)
      rw [Function.iterate_succ_apply, htheta, Function.iterate_succ_apply,
        hthetaSuccessor] at havoids
      exact havoids hstop

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateExceptional
