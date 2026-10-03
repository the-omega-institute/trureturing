/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateTail
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateTail
   mirror-E: none(waiver:fixed-tail-orbit-comparison)
   anchors: [mathlib/module/Mathlib.Dynamics.PeriodicPts.Lemmas]
   utility: none
   digest: Appending the maximum preserves every old cycle and adds one final singleton. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIteratePositionBlocks
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseBlocks
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseGeneral
import Mathlib.Dynamics.PeriodicPts.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateTail

open D5.S3.Combinatorics.ArcherCyclicDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaFixedDefs

theorem theta_append_max (word : List ℕ)
    (hperm : word.Perm (List.range' 1 (List.length word))) :
    theta (word ++ [word.length + 1]) = theta word ++ [word.length + 1] := by
  let extended := word ++ [word.length + 1]
  have hlength : extended.length = word.length + 1 := by simp [extended]
  have hnodup : word.Nodup := hperm.nodup_iff.mpr List.nodup_range'
  have hclosed (value : ℕ) (hpositive : 1 ≤ value) (hbound : value ≤ word.length) :
      1 ≤ image word value ∧ image word value ≤ word.length := by
    have hindex : value - 1 < word.length := by omega
    have hmem : image word value ∈ word := by
      rw [image, List.getD_eq_getElem _ 0 hindex]
      exact List.getElem_mem hindex
    obtain ⟨offset, hbound, hequal⟩ := List.mem_range'.mp (hperm.mem_iff.mp hmem)
    omega
  have hiterBound (value power : ℕ) (hpositive : 1 ≤ value)
      (hbound : value ≤ word.length) :
      1 ≤ (image word)^[power] value ∧ (image word)^[power] value ≤ word.length := by
    induction power with
    | zero => simpa using And.intro hpositive hbound
    | succ power ih =>
      rw [Function.iterate_succ_apply']
      exact hclosed _ ih.1 ih.2
  have hsameImage (value : ℕ) (hpositive : 1 ≤ value) (hbound : value ≤ word.length) :
      image extended value = image word value := by
    exact List.getD_append _ _ _ _ (by omega)
  have hsameIter (value power : ℕ) (hpositive : 1 ≤ value)
      (hbound : value ≤ word.length) :
      (image extended)^[power] value = (image word)^[power] value := by
    induction power with
    | zero => rfl
    | succ power ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      have hb := hiterBound value power hpositive hbound
      exact hsameImage _ hb.1 hb.2
  have hreturn (value : ℕ) (hpositive : 1 ≤ value) (hbound : value ≤ word.length) :
      ∃ period : ℕ, 0 < period ∧ period ≤ word.length ∧
        (image word)^[period] value = value := by
    let successor : Fin word.length → Fin word.length := fun index =>
      ⟨image word (index.val + 1) - 1, by
        have hb := hclosed (index.val + 1) (by omega) (by omega)
        omega⟩
    have hinjective : Function.Injective successor := by
      intro left right hequal
      have hval := congrArg Fin.val hequal
      have hleft := hclosed (left.val + 1) (by omega) (by omega)
      have hright := hclosed (right.val + 1) (by omega) (by omega)
      change image word (left.val + 1) - 1 = image word (right.val + 1) - 1 at hval
      have himages : image word (left.val + 1) = image word (right.val + 1) := by omega
      simp only [image, Nat.add_sub_cancel, List.getD_eq_getElem _ 0 left.isLt,
        List.getD_eq_getElem _ 0 right.isLt] at himages
      exact Fin.ext (hnodup.getElem_inj_iff.mp himages)
    let start : Fin word.length := ⟨value - 1, by omega⟩
    have hlift (power : ℕ) : ((successor^[power]) start).val + 1 =
        (image word)^[power] value := by
      induction power with
      | zero => change value - 1 + 1 = value; omega
      | succ power ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        change image word (((successor^[power]) start).val + 1) - 1 + 1 =
          image word ((image word)^[power] value)
        rw [ih]
        have hb := hiterBound value (power + 1) hpositive hbound
        rw [Function.iterate_succ_apply'] at hb
        omega
    let period := Function.minimalPeriod successor start
    have hperiodPositive : 0 < period :=
      Function.minimalPeriod_pos_of_mem_periodicPts (hinjective.mem_periodicPts start)
    have hperiodBound : period ≤ word.length := by
      simpa using (Function.minimalPeriod_le_card (f := successor) (x := start))
    refine ⟨period, hperiodPositive, hperiodBound, ?_⟩
    have hperiodic : successor^[period] start = start :=
      Function.isPeriodicPt_minimalPeriod successor start
    have heq := hlift period
    rw [hperiodic] at heq
    change value - 1 + 1 = (image word)^[period] value at heq
    omega
  have hcycles (value : ℕ) (hpositive : 1 ≤ value) (hbound : value ≤ word.length) :
      cycleFrom extended value = cycleFrom word value := by
    let oldOrbit := (List.range word.length).map (fun power =>
      (image word)^[power + 1] value)
    obtain ⟨period, hperiodPositive, hperiodBound, hhit⟩ :=
      hreturn value hpositive hbound
    have hmem : value ∈ oldOrbit := by
      apply List.mem_iff_getElem.mpr
      refine ⟨period - 1, by simp [oldOrbit]; omega, ?_⟩
      simp only [oldOrbit, List.getElem_map, List.getElem_range]
      rw [show period - 1 + 1 = period by omega, hhit]
    have hstopped : (oldOrbit.takeWhile (· ≠ value)).length ≠ oldOrbit.length := by
      have stop (orbit : List ℕ) (hmem : value ∈ orbit) :
          (orbit.takeWhile (· ≠ value)).length ≠ orbit.length := by
        induction orbit with
        | nil => simp at hmem
        | cons head rest ih =>
          by_cases hhead : head = value
          · subst head
            simp
          · have htail : value ∈ rest :=
              (List.mem_cons.mp hmem).resolve_left (Ne.symm hhead)
            simpa [hhead] using ih htail
      exact stop oldOrbit hmem
    unfold cycleFrom
    rw [hlength, List.range_succ, List.map_append]
    simp_rw [hsameIter value _ hpositive hbound]
    change value :: (oldOrbit ++ _).takeWhile (· ≠ value) =
      value :: oldOrbit.takeWhile (· ≠ value)
    rw [List.takeWhile_append, if_neg hstopped]
  have hnewImage : image extended (word.length + 1) = word.length + 1 := by
    rw [image, Nat.add_sub_cancel, List.getD_append_right _ _ _ _ (by omega)]
    simp
  have hnewIter (power : ℕ) : (image extended)^[power] (word.length + 1) =
      word.length + 1 := by
    induction power with
    | zero => rfl
    | succ power ih => rw [Function.iterate_succ_apply', ih, hnewImage]
  have hnewCycle : cycleFrom extended (word.length + 1) = [word.length + 1] := by
    unfold cycleFrom
    simp_rw [hnewIter]
    simp
  have hnewLeader : IsLeader extended (word.length + 1) := by
    simp [IsLeader, hnewCycle]
  have hfilter : ((List.range' 1 word.length).filter
        (fun value => decide (IsLeader extended value))) =
      ((List.range' 1 word.length).filter (fun value => decide (IsLeader word value))) := by
    apply List.filter_congr
    intro value hmem
    obtain ⟨offset, hbound, hequal⟩ := List.mem_range'.mp hmem
    have hcycle := hcycles value (by omega) (by omega)
    simp only [IsLeader, hcycle]
  have hflat : ((List.range' 1 word.length).filter
        (fun value => decide (IsLeader word value))).flatMap (cycleFrom extended) =
      ((List.range' 1 word.length).filter
        (fun value => decide (IsLeader word value))).flatMap (cycleFrom word) := by
    apply List.flatMap_congr
    intro value hmem
    obtain ⟨offset, hbound, hequal⟩ := List.mem_range'.mp (List.mem_filter.mp hmem).1
    exact hcycles value (by omega) (by omega)
  have hrange : List.range' 1 (word.length + 1) =
      List.range' 1 word.length ++ [word.length + 1] := by
    simpa [Nat.add_comm] using
      (List.range'_append_1 (s := 1) (m := word.length) (n := 1)).symm
  change theta extended = theta word ++ [word.length + 1]
  unfold theta
  rw [hlength, hrange, List.filter_append, hfilter]
  simp only [List.filter_cons, hnewLeader, decide_true, ↓reduceIte,
    List.filter_nil, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, hnewCycle, hflat]

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateTail
