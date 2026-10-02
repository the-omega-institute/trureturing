/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertionInverse
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertionInverse
   mirror-E: none(waiver:insertion-cycle-contraction)
   anchors: []
   utility: none
   digest: Contracting the three inserted vertices recovers the unique smaller cycle word. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateInsertionCycle
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateLastEndpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateInsertionInverse

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseBlocks
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateInsertion
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateInsertionCycle
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateLastEndpoint

local notation "B" =>
  (fun word : List ℕ => List.map (hat word) (List.range' 1 (List.length word)))

theorem insertion_cycle_inverse (word : List ℕ)
    (hperm : word.Perm (List.range' 1 (List.length word))) (hsize : 5 ≤ word.length)
    (hfirst : word.getD 0 0 = word.length)
    (hone : (B word).getD 0 0 = word.length)
    (htwo : (B word).getD 1 0 = word.length - 1)
    (hpenult : (B word).getD (word.length - 2) 0 = 1)
    (hlast : (B word).getD (word.length - 1) 0 = word.length - 2) :
    ∃ inner : List ℕ, inner.Perm (List.range' 1 (word.length - 3)) ∧
      inner.getD 0 0 = word.length - 3 ∧ inner.getD (inner.length - 1) 0 = 1 ∧
      I (B inner) = B word ∧ (B inner).Perm (List.range' 1 inner.length) ∧
      (B inner).getD 0 0 = inner.length ∧ ThetaFixedDefs.theta (B inner) = inner ∧
      ThetaFixedDefs.cycleFrom (B inner) inner.length = inner ∧
      (¬ Contains [1, 3, 2] [] 3 word → ¬ Contains [1, 3, 2] [] 3 inner) := by
  let size := word.length
  have hnd := hperm.nodup_iff.mpr List.nodup_range'
  have hmem (value : ℕ) (hp : 1 ≤ value) (hb : value ≤ size) : value ∈ word :=
    hperm.mem_iff.mpr (List.mem_range'.mpr
      ⟨value - 1, by dsimp [size] at *; omega, by omega⟩)
  have hidx (index : ℕ) (hi : index < size) : word.idxOf (word.getD index 0) = index := by
    rw [List.getD_eq_getElem _ 0 hi]
    exact List.get_idxOf hnd ⟨index, hi⟩
  have hinverse (index : ℕ) (hi : index < size) :
      (B word).getD index 0 = hat word (index + 1) := by
    rw [List.getD_eq_getElem _ 0 (by simp; exact hi)]
    simp only [List.getElem_map, List.getElem_range'_1, Nat.add_comm]
  have hhatone : hat word 1 = size := by simpa only [hinverse 0 (by omega)] using hone
  have hhattwo : hat word 2 = size - 1 := by
    simpa only [hinverse 1 (by omega)] using htwo
  have hhatpenult : hat word (size - 1) = 1 := by
    change (B word).getD (size - 2) 0 = 1 at hpenult
    simpa only [hinverse (size - 2) (by omega),
      show size - 2 + 1 = size - 1 by omega] using hpenult
  have hhatlast : hat word size = size - 2 := by
    change (B word).getD (size - 1) 0 = size - 2 at hlast
    simpa only [hinverse (size - 1) (by omega),
      show size - 1 + 1 = size by omega] using hlast
  have hnonrecord (index : ℕ) (hp : 0 < index) (hi : index < size) :
      ¬ IsLtrMax word index := by
    intro hrecord
    have hlt := hrecord 0 hp
    have hv : word.getD index 0 ∈ word := by
      rw [List.getD_eq_getElem _ 0 hi]
      exact List.getElem_mem hi
    obtain ⟨offset, ho, heq⟩ := List.mem_range'.mp (hperm.mem_iff.mp hv)
    rw [hfirst] at hlt
    omega
  have hedge (value : ℕ) (hv : value ∈ word) :
      hat word value = if word.idxOf value + 1 < size then
        word.getD (word.idxOf value + 1) 0 else size := by
    have hi := List.idxOf_lt_length_of_mem hv
    have hg : Nat.findGreatest (IsLtrMax word) (word.idxOf value) = 0 := by
      apply Nat.findGreatest_eq_zero_iff.mpr
      intro index hp hb
      exact hnonrecord index hp (by omega)
    unfold hat
    by_cases hn : word.idxOf value + 1 < size
    · rw [if_pos ⟨hn, hnonrecord _ (by omega) hn⟩, if_pos hn]
    · rw [if_neg (fun hc => hn hc.1), if_neg hn, hg, hfirst]
  have hidxmax : word.idxOf size = 0 := by
    simpa only [hfirst] using hidx 0 (by omega)
  have hidxone : word.idxOf 1 = size - 1 := by
    have hm := hmem 1 (by omega) (by omega)
    have hi := List.idxOf_lt_length_of_mem hm
    have he := hedge 1 hm
    rw [hhatone] at he
    by_cases hn : word.idxOf 1 + 1 < size
    · rw [if_pos hn] at he
      have hh := hidx _ hn
      rw [← he, hidxmax] at hh
      omega
    · omega
  have hidxpenult : word.idxOf (size - 1) = size - 2 := by
    have hm := hmem (size - 1) (by omega) (by omega)
    have he := hedge (size - 1) hm
    rw [hhatpenult] at he
    by_cases hn : word.idxOf (size - 1) + 1 < size
    · rw [if_pos hn] at he
      have hh := hidx _ hn
      rw [← he, hidxone] at hh
      omega
    · rw [if_neg hn] at he
      omega
  have hidxsecond : word.idxOf 2 = size - 3 := by
    have hm := hmem 2 (by omega) (by omega)
    have he := hedge 2 hm
    rw [hhattwo] at he
    by_cases hn : word.idxOf 2 + 1 < size
    · rw [if_pos hn] at he
      have hh := hidx _ hn
      rw [← he, hidxpenult] at hh
      omega
    · rw [if_neg hn] at he
      omega
  have hgetone : word.getD (size - 1) 0 = 1 := by
    rw [← hidxone, List.getD_eq_getElem _ 0 (List.idxOf_lt_length_of_mem
      (hmem 1 (by omega) (by omega)))]
    exact List.getElem_idxOf _
  have hgetpenult : word.getD (size - 2) 0 = size - 1 := by
    rw [← hidxpenult, List.getD_eq_getElem _ 0 (List.idxOf_lt_length_of_mem
      (hmem (size - 1) (by omega) (by omega)))]
    exact List.getElem_idxOf _
  have hgetsecond : word.getD (size - 3) 0 = 2 := by
    rw [← hidxsecond, List.getD_eq_getElem _ 0 (List.idxOf_lt_length_of_mem
      (hmem 2 (by omega) (by omega)))]
    exact List.getElem_idxOf _
  have hgetstart : word.getD 1 0 = size - 2 := by
    have he := hedge size (hmem size (by omega) (by omega))
    rw [hidxmax, if_pos (by omega), hhatlast] at he
    exact he.symm
  let middle := (word.drop 1).take (size - 3)
  have hmidlen : middle.length = size - 3 := by
    simp only [middle, List.length_take, List.length_drop]
    dsimp [size]
    omega
  have hsplit : word = [size] ++ middle ++ [size - 1, 1] := by
    apply List.ext_getElem (by simp [hmidlen]; dsimp [size]; omega)
    intro index hi hj
    rw [← List.getD_eq_getElem _ 0 hi]
    cases index with
    | zero => simpa only [List.cons_append, List.nil_append, List.getElem_cons_zero]
        using hfirst
    | succ index =>
      simp only [List.cons_append, List.nil_append, List.getElem_cons_succ]
      by_cases hm : index < middle.length
      · rw [List.getElem_append_left hm, List.getD_eq_getElem _ 0 hi]
        simp only [middle, List.getElem_take, List.getElem_drop]
        congr 1
        omega
      · rw [List.getElem_append_right (by omega)]
        by_cases hp : index = size - 3
        · have heq : index - middle.length = 0 := by omega
          simp only [heq, List.getElem_cons_zero]
          simpa only [show index + 1 = size - 2 by omega] using hgetpenult
        · have heq : index - middle.length = 1 := by omega
          simp only [heq, List.getElem_cons_succ, List.getElem_cons_zero]
          have hh : index + 1 = size - 1 := by change index + 1 < size at hi; omega
          simpa only [hh] using hgetone
  have hrangesplit : List.range' 1 size =
      [1] ++ List.range' 2 (size - 3) ++ [size - 1, size] := by
    have hcore : List.range' 2 (size - 1) =
        List.range' 2 (size - 3) ++ List.range' (size - 1) 2 := by
      have hs : 2 + 1 * (size - 3) = size - 1 := by omega
      have hn : size - 3 + 2 = size - 1 := by omega
      simpa only [hs, hn] using
        (List.range'_append (s := 2) (m := size - 3) (n := 2) (step := 1)).symm
    conv_lhs => rw [show size = (size - 1) + 1 by omega, List.range'_succ]
    rw [hcore]
    simp only [List.range'_succ, List.range'_zero, List.cons_append, List.nil_append,
      show size - 1 + 1 = size by omega]
  have hbase : (List.range' 1 size).Perm
      ([size] ++ List.range' 2 (size - 3) ++ [size - 1, 1]) := by
    rw [hrangesplit]
    apply List.perm_iff_count.mpr
    intro value
    simp only [List.count_append, List.count_cons, List.count_nil]
    omega
  have hmidperm : middle.Perm (List.range' 2 (size - 3)) := by
    have he := hperm.trans hbase
    rw [hsplit] at he
    exact (List.perm_append_right_iff [size - 1, 1]).mp
      ((List.perm_append_left_iff [size]).mp
        (by simpa only [List.append_assoc] using he))
  let inner := middle.map (· - 1)
  have hinnerlen : inner.length = size - 3 := by simp only [inner, List.length_map, hmidlen]
  have hinnerperm : inner.Perm (List.range' 1 inner.length) := by
    have he := hmidperm.map (· - 1)
    have hr : (List.range' 2 (size - 3)).map (· - 1) = List.range' 1 (size - 3) := by
      apply List.ext_getElem (by simp)
      intro index hi hj
      simp only [List.getElem_map, List.getElem_range'_1]
      omega
    simpa only [hr, hinnerlen] using he
  have hrestore : inner.map (· + 1) = middle := by
    dsimp only [inner]
    rw [List.map_map]
    conv_rhs => rw [← List.map_id middle]
    apply List.map_inj_left.mpr
    intro value hv
    obtain ⟨offset, ho, heq⟩ := List.mem_range'.mp (hmidperm.mem_iff.mp hv)
    simp only [Function.comp_def, id_eq]
    omega
  have hinnerfirst : inner.getD 0 0 = inner.length := by
    rw [List.getD_eq_getElem _ 0 (by rw [hinnerlen]; omega)]
    simp only [inner, List.getElem_map, middle, List.getElem_take, List.getElem_drop]
    rw [← List.getD_eq_getElem word 0 (by omega : 1 < word.length), hgetstart, hinnerlen]
    omega
  have hinnerlast : inner.getD (inner.length - 1) 0 = 1 := by
    rw [hinnerlen]
    rw [List.getD_eq_getElem _ 0 (by rw [hinnerlen]; omega)]
    simp only [inner, List.getElem_map, middle, List.getElem_take, List.getElem_drop]
    rw [← List.getD_eq_getElem word 0 (by change 1 + (size - 3 - 1) < size; omega)]
    rw [show 1 + (size - 3 - 1) = size - 3 by omega, hgetsecond]
  have hexpand : [inner.length + 3] ++ inner.map (· + 1) ++ [inner.length + 2, 1] =
      word := by
    rw [hrestore, hinnerlen, show size - 3 + 3 = size by omega,
      show size - 3 + 2 = size - 1 by omega]
    exact hsplit.symm
  have hinsert := insertion_cycle inner hinnerperm (by rw [hinnerlen]; omega)
    hinnerfirst hinnerlast
  have hcanonical : I (B inner) = B word := by
    have he := hinsert.2.2
    rw [hexpand] at he
    exact he.symm
  have htheta := (last_endpoint_cycle inner hinnerperm
    (by rw [hinnerlen]; omega) hinnerfirst).2 hinnerlast
  have hinverseperm : (B inner).Perm (List.range' 1 inner.length) := by
    have hnodup := hinnerperm.nodup_iff.mpr List.nodup_range'
    have hmapnd : (inner.map (hat inner)).Nodup :=
      hnodup.map_on (ThetaBasicInverse.hat_inj_on inner hnodup)
    have hclosed (value : ℕ) (hv : value ∈ inner) : hat inner value ∈ inner := by
      have hi := List.idxOf_lt_length_of_mem hv
      unfold hat
      dsimp only
      split_ifs with hnext
      · rw [List.getD_eq_getElem _ 0 hnext.1]
        exact List.getElem_mem hnext.1
      · have hg := lt_of_le_of_lt (Nat.findGreatest_le (P := IsLtrMax inner) _) hi
        rw [List.getD_eq_getElem _ 0 hg]
        exact List.getElem_mem hg
    have hsubset : (inner.map (hat inner)).toFinset ⊆ inner.toFinset := by
      intro value hv
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
      exact List.mem_toFinset.mpr (hclosed old ho)
    have hcard : (inner.map (hat inner)).toFinset.card = inner.toFinset.card := by
      simp [List.card_toFinset, List.dedup_eq_self.mpr hmapnd,
        List.dedup_eq_self.mpr hnodup]
    have heq := Finset.eq_of_subset_of_card_le hsubset (by omega)
    have hm := List.perm_of_nodup_nodup_toFinset_eq hmapnd hnodup heq
    exact ((hinnerperm.symm.map _).trans hm).trans hinnerperm
  have hcycle : ThetaFixedDefs.cycleFrom (B inner) inner.length = inner := by
    have hrec : IsLtrMax inner 0 := by intro index hi; omega
    have hnr (index : ℕ) (hp : 0 < index) (hi : index < inner.length) :
        ¬ IsLtrMax inner index := by
      intro hrecord
      have hlt := hrecord 0 hp
      have hm : inner.getD index 0 ∈ inner := by
        rw [List.getD_eq_getElem _ 0 hi]
        exact List.getElem_mem hi
      obtain ⟨offset, ho, heq⟩ := List.mem_range'.mp (hinnerperm.mem_iff.mp hm)
      rw [hinnerfirst] at hlt
      omega
    have he := cycleFrom_B_record_block inner hinnerperm 0 inner.length
      (by rw [hinnerlen]; omega) (le_refl _) hrec hnr (Or.inl rfl)
    simpa only [hinnerfirst, List.drop_zero, Nat.sub_zero, List.take_length] using he
  refine ⟨inner, by simpa only [hinnerlen] using hinnerperm,
    hinnerfirst.trans hinnerlen, hinnerlast, hcanonical, hinverseperm,
    htheta.1, htheta.2.1, hcycle, ?_⟩
  intro havoid hcontains
  have hsub : (inner.map (· + 1)).Sublist word := by
    rw [← hexpand]
    simpa only [List.append_assoc] using
      (List.sublist_append_left (inner.map (· + 1)) [inner.length + 2, 1]).trans
        (List.sublist_append_right [inner.length + 3]
          (inner.map (· + 1) ++ [inner.length + 2, 1]))
  obtain ⟨values, hlt, hmemvalues, hpattern, hgaps⟩ := hcontains
  apply havoid
  refine ⟨fun index => values index + 1, ?_, ?_, ?_, by simp⟩
  · intro index hp hi
    have hh := hlt index hp hi
    change values index + 1 < values (index + 1) + 1
    omega
  · intro index hp hi
    exact hsub.subset (List.mem_map.mpr ⟨values index, hmemvalues index hp hi, rfl⟩)
  · have hm := hpattern.map (fun value => value + 1)
    simpa only [List.map_map, Function.comp_def] using hm.trans hsub

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateInsertionInverse
