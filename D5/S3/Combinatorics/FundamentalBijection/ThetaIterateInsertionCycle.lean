/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertionCycle
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertionCycle
   mirror-E: none(waiver:insertion-cycle-edge-construction)
   anchors: []
   utility: none
   digest: Splitting the closing edge constructs the theta word of a one-cycle insertion. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateInsertion
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateInsertionCycle

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateInsertion
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseBlocks
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycle
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycleReduction

set_option maxHeartbeats 1200000 in
theorem insertion_cycle (q : List ℕ) (hq : q.Perm (List.range' 1 q.length))
    (hsize : 2 ≤ q.length) (hfirst : q.getD 0 0 = q.length)
    (hlast : q.getD (q.length - 1) 0 = 1) :
    let parameter := (List.range' 1 q.length).map (hat q)
    ThetaFixedDefs.theta (I parameter) =
        [q.length + 3] ++ q.map (· + 1) ++ [q.length + 2, 1] ∧
      (P (I parameter) ∈ ThetaIterateDefs.iterateAvoiders (q.length + 5) 2 [1, 3, 2] ↔
        P parameter ∈ ThetaIterateDefs.iterateAvoiders (q.length + 2) 2 [1, 3, 2]) ∧
      let word := [q.length + 3] ++ q.map (· + 1) ++ [q.length + 2, 1]
      (List.range' 1 word.length).map (hat word) = I parameter := by
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

  let size := q.length
  let parameter := (List.range' 1 size).map (hat q)
  let word := [size + 3] ++ q.map (· + 1) ++ [size + 2, 1]
  have hplen : parameter.length = size := by simp [parameter]
  have hwlen : word.length = size + 3 := by simp [word, size]
  have hbounds (index : ℕ) (hi : index < size) :
      1 ≤ q.getD index 0 ∧ q.getD index 0 ≤ size := by
    have hmem : q.getD index 0 ∈ q := by
      rw [List.getD_eq_getElem _ 0 hi]
      exact List.getElem_mem hi
    obtain ⟨offset, ho, hv⟩ := List.mem_range'.mp (hq.mem_iff.mp hmem)
    dsimp [size]
    omega
  have hget (index : ℕ) (hi : index < size + 3) :
      word.getD index 0 = if index = 0 then size + 3
        else if index < size + 1 then q.getD (index - 1) 0 + 1
        else if index = size + 1 then size + 2 else 1 := by
    cases index with
    | zero => simp [word]
    | succ index =>
      simp only [word, List.cons_append, List.nil_append, List.getD_cons_succ,
        Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      by_cases hm : index < size
      · rw [List.getD_append _ _ 0 _ (by simp; omega), if_pos (by omega),
          List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_map,
          List.getD_eq_getElem q 0 hm]
      · rw [List.getD_append_right _ _ 0 _ (by simp; omega),
          if_neg (by omega), List.length_map]
        by_cases hp : index = size
        · subst index
          simp [size]
        · have heq : index = size + 1 := by omega
          subst index
          simp [size]
  have hwperm : word.Perm (List.range' 1 word.length) := by
    have hmap : (q.map (· + 1)).Perm (List.range' 2 size) := by
      have heq := hq.map (1 + ·)
      rw [List.map_add_range'] at heq
      simpa only [Nat.add_comm] using heq
    have hrange : List.range' 1 (size + 3) =
        [1] ++ List.range' 2 size ++ [size + 2, size + 3] := by
      rw [show size + 3 = 1 + size + 2 by omega,
        ← List.range'_append_1, ← List.range'_append_1]
      simp [List.range', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    rw [hwlen, hrange]
    change ([size + 3] ++ q.map (· + 1) ++ [size + 2, 1]).Perm _
    apply ((List.Perm.refl [size + 3]).append
      (hmap.append (List.Perm.refl [size + 2, 1]))).trans
    have hswap := List.perm_append_comm (l₁ := [size + 3]) (l₂ := List.range' 2 size)
    have htail : ([size + 3] ++ [size + 2, 1]).Perm
        ([1] ++ [size + 2, size + 3]) :=
      (List.Perm.swap _ _ _).trans
        (((List.Perm.swap _ _ _).cons _).trans (List.Perm.swap _ _ _))
    have hmid := (List.Perm.refl (List.range' 2 size)).append htail
    have hend := (List.perm_append_comm (l₁ := List.range' 2 size)
      (l₂ := [1])).append_right [size + 2, size + 3]
    have hstart : ([size + 3] ++ List.range' 2 size ++ [size + 2, 1]).Perm
        (List.range' 2 size ++ ([size + 3] ++ [size + 2, 1])) := by
      simpa only [List.append_assoc] using hswap.append_right [size + 2, 1]
    simpa only [List.append_assoc] using
      hstart.trans (hmid.trans (by
        simpa only [List.append_assoc] using hend))
  have hwordfirst : word.getD 0 0 = word.length := by
    rw [hget 0 (by omega), if_pos rfl, hwlen]
  have hedges (p : List ℕ) (hp : p.Perm (List.range' 1 p.length))
      (hpositive : 0 < p.length) (hmaximum : p.getD 0 0 = p.length) :
      (∀ index < p.length, hat p (p.getD index 0) =
        if index + 1 < p.length then p.getD (index + 1) 0 else p.getD 0 0) ∧
      (∀ index, 0 < index → index < p.length → ¬ IsLtrMax p index) := by
    have hnodup := hp.nodup_iff.mpr List.nodup_range'
    have hnon (index : ℕ) (hi : 0 < index) (hn : index < p.length) :
        ¬ IsLtrMax p index := by
      intro hrec
      have hlt := hrec 0 hi
      rw [hmaximum] at hlt
      have hmem : p.getD index 0 ∈ p := by
        rw [List.getD_eq_getElem _ 0 hn]
        exact List.getElem_mem hn
      obtain ⟨offset, ho, hv⟩ := List.mem_range'.mp (hp.mem_iff.mp hmem)
      omega
    refine ⟨?_, hnon⟩
    intro index hi
    have hidx : p.idxOf (p.getD index 0) = index := by
      rw [List.getD_eq_getElem _ 0 hi]
      simpa using (List.get_idxOf hnodup ⟨index, hi⟩)
    have hgreatest : Nat.findGreatest (IsLtrMax p) index = 0 := by
      by_contra hne
      have hbound := Nat.findGreatest_le (P := IsLtrMax p) index
      have hrec := Nat.findGreatest_spec (by omega : 0 ≤ index)
        (show IsLtrMax p 0 from by intro earlier he; omega)
      exact hnon _ (by omega) (by omega) hrec
    unfold hat
    rw [hidx]
    by_cases hnext : index + 1 < p.length
    · rw [if_pos ⟨hnext, hnon _ (by omega) hnext⟩, if_pos hnext]
    · rw [if_neg (by tauto), if_neg hnext, hgreatest]
  have hqedges := hedges q hq (by omega) hfirst
  have hwedges := hedges word hwperm (by omega) hwordfirst
  have hqone : hat q 1 = size := by
    have heq := hqedges.1 (size - 1) (by omega)
    rw [hlast, if_neg (by dsimp [size]; omega), hfirst] at heq
    exact heq
  have hparamget (index : ℕ) (hi : index < size) :
      parameter.getD index 0 = hat q (index + 1) := by
    rw [List.getD_eq_getElem _ 0 (by simpa [hplen] using hi)]
    simp [parameter, Nat.add_comm]
  have hinsertget (index : ℕ) (hi : index < size + 3) :
      (I parameter).getD index 0 = if index = 0 then size + 3
        else if index = 1 then size + 2
        else if index < size + 1 then hat q index + 1
        else if index = size + 1 then 1 else size + 1 := by
    cases index with
    | zero => simp [I, hplen]
    | succ index =>
      cases index with
      | zero => simp [I, hplen]
      | succ index =>
        simp only [I, hplen, List.cons_append, List.nil_append,
          List.getD_cons_succ, show index + 1 + 1 ≠ 0 by omega,
          show index + 1 + 1 ≠ 1 by omega, if_false]
        by_cases hm : index < size - 1
        · rw [List.getD_append _ _ 0 _ (by simp [hplen]; omega),
            if_pos (by omega), List.getD_eq_getElem _ 0 (by simp [hplen]; omega),
            List.getElem_map, List.getElem_drop]
          rw [← List.getD_eq_getElem parameter 0 (by omega),
            hparamget _ (by omega)]
          congr 2
          omega
        · rw [List.getD_append_right _ _ 0 _ (by simp [hplen]; omega),
            if_neg (by omega), List.length_map, List.length_drop, hplen]
          by_cases hp : index + 2 = size + 1
          · rw [if_pos (by omega), show index - (size - 1) = 0 by omega]
            rfl
          · rw [if_neg (by omega), show index - (size - 1) = 1 by omega]
            rfl
  have hsplit : (List.range' 1 word.length).map (hat word) = I parameter := by
    apply List.ext_getElem
    · simp [I, hplen, hwlen]; omega
    · intro index hleft hright
      have hi : index < size + 3 := by simpa [hwlen] using hleft
      change _ = (I parameter)[index]
      rw [← List.getD_eq_getElem (I parameter) 0 hright, hinsertget index hi]
      simp only [List.getElem_map, List.getElem_range'_1]
      by_cases hz : index = 0
      · subst index
        have heq := hwedges.1 (size + 2) (by omega)
        rw [hwlen] at heq
        rw [hget _ (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega), hget 0 (by omega), if_pos rfl] at heq
        simpa using heq
      · by_cases hone : index = 1
        · subst index
          have heq := hwedges.1 size (by omega)
          rw [hwlen] at heq
          have hvalue : word.getD size 0 = 2 := by
            rw [hget _ (by omega), if_neg (by omega), if_pos (by omega), hlast]
          have hnextvalue : word.getD (size + 1) 0 = size + 2 := by
            rw [hget _ (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
          rw [hvalue, if_pos (by omega), hnextvalue] at heq
          simpa using heq
        · by_cases hmid : index < size + 1
          · have hmem : index ∈ q := hq.mem_iff.mpr (List.mem_range'.mpr
              ⟨index - 1, by omega, by omega⟩)
            obtain ⟨position, hp, hval⟩ := List.mem_iff_getElem.mp hmem
            have hqval : q.getD position 0 = index := by
              rwa [List.getD_eq_getElem _ 0 hp]
            have hnext : position + 1 < size := by
              by_contra hnot
              have heq : position = size - 1 := by omega
              rw [heq, hlast] at hqval
              omega
            have heq := hwedges.1 (position + 1) (by omega)
            rw [hwlen] at heq
            rw [hget _ (by omega), if_neg (by omega), if_pos (by omega),
              Nat.add_sub_cancel, hqval, if_pos (by omega),
              hget _ (by omega), if_neg (by omega), if_pos (by omega),
              show position + 1 + 1 - 1 = position + 1 by omega] at heq
            have hold := hqedges.1 position hp
            rw [hqval, if_pos hnext] at hold
            simpa [hz, hone, hmid, hold, Nat.add_comm] using heq
          · by_cases hpenult : index = size + 1
            · subst index
              have heq := hwedges.1 (size + 1) (by omega)
              rw [hwlen] at heq
              rw [hget _ (by omega), if_neg (by omega), if_neg (by omega),
                if_pos rfl, if_pos (by omega), hget _ (by omega),
                if_neg (by omega), if_neg (by omega), if_neg (by omega)] at heq
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
                show size ≠ 0 by omega,
                if_neg (by omega : ¬ (size + 1 = 0)),
                if_neg (by omega : ¬ (size + 1 = 1)),
                if_neg (by omega : ¬ (size + 1 < size + 1)), if_pos rfl] using heq
            · have hfinal : index = size + 2 := by omega
              subst index
              have heq := hwedges.1 0 (by omega)
              rw [hwlen] at heq
              rw [hget _ (by omega), if_pos rfl, if_pos (by omega),
                hget _ (by omega), if_neg (by omega), if_pos (by omega),
                show 1 - 1 = 0 by omega, hfirst] at heq
              simpa only [size, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
                if_neg (by omega : ¬ (size + 2 = 0)),
                if_neg (by omega : ¬ (size + 2 = 1)),
                if_neg (by omega : ¬ (size + 2 < size + 1)),
                if_neg (by omega : ¬ (size + 2 = size + 1))] using heq
  have hleft_single (p : List ℕ) (hp : p.Perm (List.range' 1 p.length))
      (hpositive : 0 < p.length) (hmaximum : p.getD 0 0 = p.length) :
      ThetaFixedDefs.theta ((List.range' 1 p.length).map (hat p)) = p := by
    let inverse := (List.range' 1 p.length).map (hat p)
    have hnon := (hedges p hp hpositive hmaximum).2
    have hcycle : ThetaFixedDefs.cycleFrom inverse p.length = p := by
      have heq := cycleFrom_B_record_block p hp 0 p.length
        hpositive (le_refl _) (by intro earlier he; omega) hnon (Or.inl rfl)
      change ThetaFixedDefs.cycleFrom inverse (p.getD 0 0) = _ at heq
      rw [hmaximum] at heq
      simpa using heq
    have hleaders : (List.range' 1 inverse.length).filter
        (fun value => decide (ThetaFixedDefs.IsLeader inverse value)) = [p.length] := by
      have hleader : ThetaFixedDefs.IsLeader inverse p.length := by
        rw [ThetaFixedDefs.IsLeader, hcycle]
        intro value hv
        obtain ⟨offset, ho, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hv)
        omega
      have hilen : inverse.length = p.length := by simp [inverse]
      have hpred (value : ℕ) (hv : value ∈ List.range' 1 p.length) :
          decide (ThetaFixedDefs.IsLeader inverse value) = decide (value = p.length) := by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · intro hl
          by_contra hne
          have hmem : value ∈ p := hp.mem_iff.mpr hv
          have hidx : p.idxOf value < p.length := List.idxOf_lt_length_of_mem hmem
          have hpos : 0 < p.idxOf value := by
            by_contra hn
            have hz : p.idxOf value = 0 := by omega
            have hval := List.getElem_idxOf hidx
            rw [← List.getD_eq_getElem p 0 hidx, hz, hmaximum] at hval
            exact hne hval.symm
          have hn := nonrecord_not_B_leader p hp value hmem (hnon _ hpos hidx)
          exact hn hl
        · rintro rfl
          exact hleader
      rw [hilen, List.filter_congr hpred]
      have hrange : List.range' 1 p.length =
          List.range' 1 (p.length - 1) ++ [p.length] := by
        simpa only [show p.length - 1 + 1 = p.length by omega,
          show 1 + (p.length - 1) = p.length by omega] using
          (List.range'_1_concat (s := 1) (n := p.length - 1))
      have hnil : (List.range' 1 (p.length - 1)).filter
          (fun value => decide (value = p.length)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro value hv
        obtain ⟨offset, ho, heq⟩ := List.mem_range'.mp hv
        simp only [Bool.not_eq_true, decide_eq_false_iff_not]
        omega
      rw [hrange, List.filter_append, hnil]
      simp
    unfold ThetaFixedDefs.theta
    rw [hleaders]
    simpa using hcycle
  have htheta : ThetaFixedDefs.theta (I parameter) = word := by
    rw [← hsplit]
    exact hleft_single word hwperm (by omega) hwordfirst
  have hparamtheta : ThetaFixedDefs.theta parameter = q :=
    hleft_single q hq (by omega) hfirst
  have pattern (values : List ℕ) : Contains [1, 3, 2] [] 3 values ↔
      ∃ first middle last : ℕ, first < middle ∧ middle < last ∧ last < values.length ∧
        values.getD first 0 < values.getD last 0 ∧
        values.getD last 0 < values.getD middle 0 := by
    constructor
    · intro hcontains
      obtain ⟨first, middle, last, hfm, hml, hfl, hlm⟩ :=
        (contains132_iff_indices values).mp hcontains
      refine ⟨first, middle, last, hfm, hml, last.isLt, ?_, ?_⟩
      · simpa only [List.getD_eq_getElem _ 0 first.isLt,
          List.getD_eq_getElem _ 0 last.isLt] using hfl
      · simpa only [List.getD_eq_getElem _ 0 last.isLt,
          List.getD_eq_getElem _ 0 middle.isLt] using hlm
    · rintro ⟨first, middle, last, hfm, hml, hlast, hfl, hlm⟩
      apply (contains132_iff_indices values).mpr
      refine ⟨⟨first, by omega⟩, ⟨middle, by omega⟩,
        ⟨last, hlast⟩, hfm, hml, ?_, ?_⟩
      · simpa only [List.getD_eq_getElem _ 0 (by omega : first < values.length),
          List.getD_eq_getElem _ 0 hlast] using hfl
      · simpa only [List.getD_eq_getElem _ 0 hlast,
          List.getD_eq_getElem _ 0 (by omega : middle < values.length)] using hlm
  have hthetaavoid : (¬ Contains [1, 3, 2] [] 3 word) ↔
      ¬ Contains [1, 3, 2] [] 3 q := by
    constructor
    · intro havoid hcontains
      obtain ⟨first, middle, last, hfm, hml, hl, hfl, hlm⟩ := (pattern q).mp hcontains
      apply havoid
      apply (pattern word).mpr
      refine ⟨first + 1, middle + 1, last + 1, by omega, by omega, by omega, ?_, ?_⟩
      · rw [hget _ (by omega), hget _ (by omega)]
        simp only [show first + 1 ≠ 0 by omega, show last + 1 ≠ 0 by omega,
          if_false, show first + 1 < size + 1 by omega,
          show last + 1 < size + 1 by omega, if_true, Nat.add_sub_cancel]
        omega
      · rw [hget _ (by omega), hget _ (by omega)]
        simp only [show last + 1 ≠ 0 by omega, show middle + 1 ≠ 0 by omega,
          if_false, show last + 1 < size + 1 by omega,
          show middle + 1 < size + 1 by omega, if_true, Nat.add_sub_cancel]
        omega
    · intro havoid hcontains
      obtain ⟨first, middle, last, hfm, hml, hl, hfl, hlm⟩ := (pattern word).mp hcontains
      have hinside : 1 ≤ first ∧ last < size + 1 := by
        rw [hget first (by omega), hget last (by omega)] at hfl
        rw [hget middle (by omega), hget last (by omega)] at hlm
        have hfbound := hbounds (first - 1)
        have hmbound := hbounds (middle - 1)
        have hlbound := hbounds (last - 1)
        split_ifs at hfl hlm <;> try omega
      apply havoid
      apply (pattern q).mpr
      refine ⟨first - 1, middle - 1, last - 1, by omega, by omega, by omega, ?_, ?_⟩
      · rw [hget first (by omega), hget last (by omega)] at hfl
        simpa only [if_neg (by omega : first ≠ 0), if_neg (by omega : last ≠ 0),
          if_pos (by omega : first < size + 1), if_pos hinside.2,
          Nat.add_lt_add_iff_right] using hfl
      · rw [hget last (by omega), hget middle (by omega)] at hlm
        simpa only [if_neg (by omega : last ≠ 0), if_neg (by omega : middle ≠ 0),
          if_pos hinside.2, if_pos (by omega : middle < size + 1),
          Nat.add_lt_add_iff_right] using hlm
  have hparamperm : parameter.Perm (List.range' 1 parameter.length) := by
    have hnodup := hq.nodup_iff.mpr List.nodup_range'
    have hmapnodup : (q.map (hat q)).Nodup :=
      hnodup.map_on (ThetaBasicInverse.hat_inj_on q hnodup)
    have hmem (value : ℕ) (hv : value ∈ q) : hat q value ∈ q := by
      have hi := List.idxOf_lt_length_of_mem hv
      unfold hat
      dsimp only
      split_ifs with hnext
      · rw [List.getD_eq_getElem _ 0 hnext.1]
        exact List.getElem_mem hnext.1
      · have hg := lt_of_le_of_lt (Nat.findGreatest_le (P := IsLtrMax q) _) hi
        rw [List.getD_eq_getElem _ 0 hg]
        exact List.getElem_mem hg
    have hsubset : (q.map (hat q)).toFinset ⊆ q.toFinset := by
      intro value hv
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
      exact List.mem_toFinset.mpr (hmem old ho)
    have hcard : (q.map (hat q)).toFinset.card = q.toFinset.card := by
      simp [List.card_toFinset, List.dedup_eq_self.mpr hmapnodup,
        List.dedup_eq_self.mpr hnodup]
    have heq := Finset.eq_of_subset_of_card_le hsubset (by omega)
    have hmperm := List.perm_of_nodup_nodup_toFinset_eq hmapnodup hnodup heq
    rw [hplen]
    exact ((hq.symm.map _).trans hmperm).trans hq
  have hparamfirst : parameter.getD 0 0 = parameter.length := by
    rw [hparamget _ (by omega), hqone, hplen]
  have hscan := insertion_scan parameter hparamperm (by omega) hparamfirst
  have hilen : (I parameter).length = size + 3 := by simp [I, hplen]; omega
  have hiperm : (I parameter).Perm (List.range' 1 (I parameter).length) := by
    simpa only [hilen, hplen] using hscan.1
  have hifirst : (I parameter).getD 0 0 = (I parameter).length := by
    rw [hinsertget _ (by omega), if_pos rfl, hilen]
  have hnoscross (p : List ℕ) (hp : p.Perm (List.range' 1 p.length))
      (hmaximum : p.getD 0 0 = p.length) :
      ∀ first last, first < last → last < p.length →
        ¬ ((b p).getD first 0 < p.getD 0 0 + 1 ∧
          p.getD 0 0 + 1 < (b p).getD last 0) := by
    intro first last hfl hl hcross
    have hb := b_perm_of_first_max p hp hmaximum
    have hmem : (b p).getD last 0 ∈ b p := by
      rw [List.getD_eq_getElem _ 0 (by simp [b]; omega)]
      exact List.getElem_mem (by simp [b]; omega)
    obtain ⟨offset, ho, heq⟩ := List.mem_range'.mp (hb.mem_iff.mp hmem)
    rw [hmaximum] at hcross
    omega
  have htests := (P_cycle_reduction parameter hparamperm (by omega)).2.2.1
  have hitests := (P_cycle_reduction (I parameter) hiperm (by omega)).2.2.1
  refine ⟨htheta, ?_, hsplit⟩
  constructor
  · intro hm
    have hi := hitests.mp (by
      simpa only [hilen, show size + 3 + 2 = size + 5 by omega] using hm)
    apply (show P parameter ∈
      ThetaIterateDefs.iterateAvoiders (size + 2) 2 [1, 3, 2] ↔ _ from by
        simpa only [hplen] using htests).mpr
    refine ⟨hscan.2.2.1.mp hi.1, ?_, hscan.2.2.2.1.mp hi.2.2.1,
      by simpa only [hplen] using hnoscross parameter hparamperm hparamfirst⟩
    rw [hparamtheta]
    exact hthetaavoid.mp (by simpa only [htheta] using hi.2.1)
  · intro hm
    have hi := htests.mp (by simpa only [hplen] using hm)
    have hθ : ¬ Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta (I parameter)) := by
      rw [htheta]
      exact hthetaavoid.mpr (by simpa only [hparamtheta] using hi.2.1)
    have hiword := hitests.mpr ⟨hscan.2.2.1.mpr hi.1, hθ,
      hscan.2.2.2.1.mpr hi.2.2.1, hnoscross (I parameter) hiperm hifirst⟩
    simpa only [hilen, show size + 3 + 2 = size + 5 by omega] using hiword

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateInsertionCycle
