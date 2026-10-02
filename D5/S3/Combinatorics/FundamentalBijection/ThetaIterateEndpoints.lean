/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateEndpoints
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateEndpoints
   mirror-E: none(waiver:parameter-endpoint-obstructions)
   anchors: []
   utility: none
   digest: Explicit successor witnesses force the endpoint split of the parameter family. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycleReduction
import D5.S3.Combinatorics.FundamentalBijection.ThetaIteratePositionBlocks
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseBlocks
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseGeneral
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateTail
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateLastEndpoint
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateExceptional

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateEndpoints

open D5.S3.Combinatorics.FundamentalBijection
open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycle
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycleReduction
open D5.S3.Combinatorics.FundamentalBijection.ThetaIteratePosition

open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords

local notation "B" =>
  (fun word : List ℕ => List.map (hat word) (List.range' 1 (List.length word)))

set_option maxHeartbeats 1600000 in
theorem parameter_endpoints (parameter : List ℕ)
    (hperm : parameter.Perm (List.range' 1 parameter.length))
    (hsize : 2 ≤ parameter.length)
    (hmember : P parameter ∈
      ThetaIterateDefs.iterateAvoiders (parameter.length + 2) 2 [1, 3, 2]) :
    (parameter.getD 0 0 = parameter.length ∨
      parameter.getD (parameter.length - 1) 0 = parameter.length) ∧
      ¬ (parameter.getD 0 0 = parameter.length ∧
        parameter.getD (parameter.length - 1) 0 = parameter.length) := by
  have theta_record_inverse (p : List ℕ) (hp : p.Perm (List.range' 1 p.length)) :
      (∀ w, w.Perm (List.range' 1 w.length) → ThetaFixedDefs.theta (B w) = w) ∧
      (∀ w, w.Perm (List.range' 1 w.length) → (B w).Perm (List.range' 1 w.length)) ∧
      (ThetaFixedDefs.theta p).Perm (List.range' 1 p.length) ∧
      B (ThetaFixedDefs.theta p) = p := by
    let h := p.length
    let q := ThetaFixedDefs.theta p
    open ThetaBasicInverseGeneral ThetaBasicInverseBlocks in
    have B_leaders_eq_record_values (p : List ℕ)
        (hp : p.Perm (List.range' 1 p.length)) :
        (List.range' 1 p.length).filter (fun x => decide (ThetaFixedDefs.IsLeader (B p) x)) =
          ((List.Ico 0 p.length).filter (IsLtrMax p)).map (fun i => p.getD i 0) := by
      have record_is_B_leader (p : List ℕ)
          (hp : p.Perm (List.range' 1 p.length)) (s : ℕ)
          (hs : s < p.length) (hrec : IsLtrMax p s) :
          ThetaFixedDefs.IsLeader (B p) (p.getD s 0) := by
        have hnext : ∃ e, s < e ∧ e ≤ p.length ∧
            (∀ j, s < j → j < e → ¬ IsLtrMax p j) ∧
            (e = p.length ∨ IsLtrMax p e) := by
          let Q : ℕ → Prop := fun e => s < e ∧ e ≤ p.length ∧
            (e = p.length ∨ IsLtrMax p e)
          have hex : ∃ e, Q e := ⟨p.length, hs, le_refl _, Or.inl rfl⟩
          let e := Nat.find hex
          have he : Q e := Nat.find_spec hex
          refine ⟨e, he.1, he.2.1, ?_, he.2.2⟩
          intro j hsj hje hp
          have hjQ : Q j := ⟨hsj, by omega, Or.inr hp⟩
          have hmin : e ≤ j := Nat.find_min' hex hjQ
          omega
        obtain ⟨e, hse, he, hnon, hboundary⟩ := hnext
        have hcycle := cycleFrom_B_record_block p hp s e hse he hrec hnon hboundary
        rw [ThetaFixedDefs.IsLeader, hcycle]
        intro y hy
        obtain ⟨i, hi, hval⟩ := List.mem_iff_getElem.mp hy
        have hil : i < e - s := by
            simpa [List.length_take, List.length_drop,
              Nat.min_eq_left (by omega : e - s ≤ p.length - s)]
            using hi
        have hsi : s + i < p.length := by omega
        have hget : ((p.drop s).take (e - s))[i] = p.getD (s + i) 0 := by
          rw [List.getElem_take, List.getElem_drop, List.getD_eq_getElem _ 0 hsi]
        rw [← hval, hget]
        have hg : Nat.findGreatest (IsLtrMax p) (s + i) = s := by
          have hle : s ≤ Nat.findGreatest (IsLtrMax p) (s + i) :=
            Nat.le_findGreatest (by omega) hrec
          have hu := Nat.findGreatest_le (P := IsLtrMax p) (s + i)
          by_contra hne
          have hgt : s < Nat.findGreatest (IsLtrMax p) (s + i) := by omega
          exact hnon _ hgt (by omega)
            (Nat.findGreatest_spec (by omega : 0 ≤ s + i) (by
              intro j hj
              omega))
        simpa only [hg] using last_record_bounds_prefix p (s + i) hsi (s + i) (le_refl _)
      let records := (List.Ico 0 p.length).filter (IsLtrMax p)
      have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
      have hleader (x : ℕ) (hx : x ∈ p) :
          ThetaFixedDefs.IsLeader (B p) x ↔ IsLtrMax p (p.idxOf x) := by
        have hidx : p.idxOf x < p.length := List.idxOf_lt_length_of_mem hx
        have hget : p.getD (p.idxOf x) 0 = x := by
          rw [List.getD_eq_getElem _ 0 hidx]
          exact List.getElem_idxOf hidx
        constructor
        · intro hlead
          by_contra hnon
          exact (nonrecord_not_B_leader p hp x hx hnon) hlead
        · intro hrec
          rw [← hget]
          exact record_is_B_leader p hp _ hidx hrec
      have hleft : ((List.range' 1 p.length).filter
          (fun x => decide (ThetaFixedDefs.IsLeader (B p) x))).Pairwise (· < ·) :=
        (List.pairwise_lt_range' 1 (by omega : 0 < (1 : ℕ))).filter _
      have hright : (records.map (fun i => p.getD i 0)).Pairwise (· < ·) := by
        apply List.pairwise_iff_getElem.mpr
        intro i j hi hj hij
        have hi' : i < records.length := by simpa using hi
        have hj' : j < records.length := by simpa using hj
        simp only [List.getElem_map]
        have hix : records[i] < records[j] :=
          (List.pairwise_iff_getElem.mp ((List.Ico.pairwise_lt 0 p.length).filter _))
            i j hi' hj' hij
        have hjmem : records[j] ∈ records := List.getElem_mem hj'
        have hjrec : IsLtrMax p records[j] :=
          decide_eq_true_eq.mp (List.mem_filter.mp hjmem).2
        exact hjrec _ hix
      apply List.Pairwise.eq_of_mem_iff hleft hright
      intro x
      constructor
      · intro hx
        obtain ⟨hxr, hxlead⟩ := List.mem_filter.mp hx
        have hxp : x ∈ p := hp.mem_iff.mpr hxr
        have hrec := (hleader x hxp).mp (decide_eq_true_eq.mp hxlead)
        have hidx : p.idxOf x ∈ records := List.mem_filter.mpr
          ⟨List.Ico.mem.mpr ⟨Nat.zero_le _, List.idxOf_lt_length_of_mem hxp⟩,
            decide_eq_true hrec⟩
        have hget : p.getD (p.idxOf x) 0 = x := by
          rw [List.getD_eq_getElem _ 0 (List.idxOf_lt_length_of_mem hxp)]
          exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hxp)
        exact List.mem_map.mpr ⟨p.idxOf x, hidx, hget⟩
      · intro hx
        obtain ⟨i, hi, hval⟩ := List.mem_map.mp hx
        rw [← hval]
        obtain ⟨hiIco, hirec⟩ := List.mem_filter.mp hi
        have hil : i < p.length := (List.Ico.mem.mp hiIco).2
        have hxp : p.getD i 0 ∈ p := by
          rw [List.getD_eq_getElem _ 0 hil]
          exact List.getElem_mem hil
        have hidx : p.idxOf (p.getD i 0) = i := by
          rw [List.getD_eq_getElem _ 0 hil]
          simpa using (List.get_idxOf hnodup ⟨i, hil⟩)
        apply List.mem_filter.mpr
        refine ⟨hp.mem_iff.mp hxp, ?_⟩
        have hrec : IsLtrMax p (p.idxOf (p.getD i 0)) := by
          rw [hidx]
          exact decide_eq_true_eq.mp hirec
        exact decide_eq_true ((hleader _ hxp).mpr hrec)
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
    have hleft (w : List ℕ) (hw : w.Perm (List.range' 1 w.length)) :
        ThetaFixedDefs.theta (B w) = w := by
      let records := (List.Ico 0 w.length).filter (IsLtrMax w)
      have hcycles : ∀ s ∈ records,
          ThetaFixedDefs.cycleFrom (B w) (w.getD s 0) =
            (w.drop s).take (nextBoundary (IsLtrMax w) w.length s - s) := by
        intro s hs
        obtain ⟨hsIco, hsrec⟩ := List.mem_filter.mp hs
        have hsn : s < w.length := (List.Ico.mem.mp hsIco).2
        let e := nextBoundary (IsLtrMax w) w.length s
        have hb : s < e ∧ e ≤ w.length ∧ (e = w.length ∨ IsLtrMax w e) ∧
            ∀ j, s < j → j < e → ¬ IsLtrMax w j := by
          dsimp [e, nextBoundary]
          simp only [dif_pos hsn]
          let Q : ℕ → Prop := fun e => s < e ∧ e ≤ w.length ∧
            (e = w.length ∨ IsLtrMax w e)
          have hex : ∃ e, Q e := ⟨w.length, hsn, le_refl _, Or.inl rfl⟩
          have hfind : Q (Nat.find hex) := Nat.find_spec hex
          refine ⟨hfind.1, hfind.2.1, hfind.2.2, ?_⟩
          intro j hsj hjb hjP
          have hmin : Nat.find hex ≤ j :=
            Nat.find_min' hex ⟨hsj, by omega, Or.inr hjP⟩
          omega
        exact cycleFrom_B_record_block w hw s e hb.1 hb.2.1
          (decide_eq_true_eq.mp hsrec) hb.2.2.2 hb.2.2.1
      unfold ThetaFixedDefs.theta
      rw [show (B w).length = w.length by simp, B_leaders_eq_record_values w hw]
      change (records.map (fun i => w.getD i 0)).flatMap
        (ThetaFixedDefs.cycleFrom (B w)) = w
      rw [List.flatMap_map]
      have heq := List.flatMap_congr hcycles
      rw [heq]
      have hzero : 0 < w.length → IsLtrMax w 0 := by intro _ j hj; omega
      simpa only [records, List.Ico.zero_bot, Nat.zero_le, List.drop_zero] using
        filter_interval_partition w (IsLtrMax w) 0 (Nat.zero_le _) hzero
    let Words := {w : List ℕ // w.Perm (List.range' 1 h)}
    have hfinite : Set.Finite {w : List ℕ | w.Perm (List.range' 1 h)} := by
      convert (List.permutations (List.range' 1 h)).finite_toSet using 1
      ext w
      exact List.mem_permutations.symm
    have : Finite Words := hfinite
    have hvalid (w : Words) : w.val.Perm (List.range' 1 w.val.length) := by
      have hwlen : w.val.length = h := by simpa using w.property.length_eq
      simpa [hwlen] using w.property
    let f : Words → Words := fun w => ⟨B w.val, by
      have hwlen : w.val.length = h := by simpa using w.property.length_eq
      simpa [hwlen] using B_perm w.val (hvalid w)⟩
    have hinjective : Function.Injective f := by
      intro x y hxy
      have hB : B x.val = B y.val := congrArg Subtype.val hxy
      apply Subtype.ext
      calc
        x.val = ThetaFixedDefs.theta (B x.val) := (hleft x.val (hvalid x)).symm
        _ = ThetaFixedDefs.theta (B y.val) := by rw [hB]
        _ = y.val := hleft y.val (hvalid y)
    obtain ⟨w, hw⟩ := (Finite.surjective_of_injective hinjective) (⟨p, hp⟩ : Words)
    have hB : B w.val = p := congrArg Subtype.val hw
    have htheta : q = w.val := by
      dsimp [q]
      rw [← hB]
      exact hleft w.val (hvalid w)
    refine ⟨hleft, B_perm, ?_, ?_⟩
    · change q.Perm (List.range' 1 h)
      rw [htheta]
      exact w.property
    · change B q = p
      rw [htheta]
      exact hB
  have theta_pair_position (p : List ℕ)
      (hp : p.Perm (List.range' 1 p.length))
      (havoidp : ¬ Contains [1, 3, 2] [] 3 p)
      (havoidθ : ¬ Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta p))
      (hn : 3 ≤ p.length) :
      p.getD 0 0 = p.length ∨
        p.getD (p.length - 1) 0 = p.length ∨
        p = List.range' 2 (p.length - 1) ++ [1] := by
    have hat_one_block (word : List ℕ)
        (hmaximum : ∀ value ∈ word, value ≤ word.getD 0 0)
        (value : ℕ) (hvalue : value ∈ word) :
        hat word value = if word.idxOf value + 1 < word.length then
          word.getD (word.idxOf value + 1) 0 else word.getD 0 0 := by
      have hindex : word.idxOf value < word.length :=
        List.idxOf_lt_length_of_mem hvalue
      have hnonrecord (index : ℕ) (hpositive : 0 < index) (hbound : index < word.length) :
          ¬ IsLtrMax word index := by
        intro hrecord
        have hlt := hrecord 0 hpositive
        have hmember : word.getD index 0 ∈ word := by
          rw [List.getD_eq_getElem _ 0 hbound]
          exact List.getElem_mem hbound
        have hle := hmaximum _ hmember
        omega
      have hgreatest : Nat.findGreatest (IsLtrMax word) (word.idxOf value) = 0 := by
        apply Nat.findGreatest_eq_zero_iff.mpr
        intro index hpositive hbound
        exact hnonrecord index hpositive (by omega)
      unfold hat
      by_cases hnext : word.idxOf value + 1 < word.length
      · rw [if_pos ⟨hnext, hnonrecord _ (by omega) hnext⟩, if_pos hnext]
      · rw [if_neg (fun hcase => hnext hcase.1), if_neg hnext, hgreatest]
    let n := p.length
    let q := ThetaFixedDefs.theta p
    have hθ : q.Perm (List.range' 1 p.length) ∧ B q = p :=
      ⟨(theta_record_inverse p hp).2.2.1, (theta_record_inverse p hp).2.2.2⟩
    have hqLen : q.length = n := by simpa [q, n] using hθ.1.length_eq
    have hq : q.Perm (List.range' 1 q.length) := by
      simpa [hqLen, q, n] using hθ.1
    have hpB : B q = p := hθ.2
    have havoidq : ¬ Contains [1, 3, 2] [] 3 q := havoidθ
    have havoidB : ¬ Contains [1, 3, 2] [] 3 (B q) := by rw [hpB]; exact havoidp
    have hnq : 3 ≤ q.length := by omega
    have hnmem : q.length ∈ q := hq.mem_iff.mpr
      (List.mem_range'.mpr ⟨q.length - 1, by omega, by omega⟩)
    let s := q.idxOf q.length
    have hslen : s < q.length := List.idxOf_lt_length_of_mem hnmem
    have hsmax : q.getD s 0 = q.length := by
      rw [List.getD_eq_getElem _ 0 hslen]
      exact List.getElem_idxOf hslen
    have hsrec : IsLtrMax q s := by
      intro i his
      have hi : i < q.length := by omega
      have hmem : q.getD i 0 ∈ q := by
        rw [List.getD_eq_getElem _ 0 hi]
        exact List.getElem_mem hi
      obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hq.mem_iff.mp hmem)
      have hnd : q.Nodup := hq.nodup_iff.mpr List.nodup_range'
      have hneq : q.getD i 0 ≠ q.getD s 0 := by
        intro heq
        have hval : q[i] = q[s] := by
          simpa only [← List.getD_eq_getElem _ 0 hi,
            ← List.getD_eq_getElem _ 0 hslen] using heq
        have := (hnd.getElem_inj_iff).mp hval
        omega
      omega
    have hnorec (i : ℕ) (hsi : s < i) (hi : i < q.length) :
        ¬ IsLtrMax q i := by
      intro hrec
      have hgt := hrec s hsi
      have hmem : q.getD i 0 ∈ q := by
        rw [List.getD_eq_getElem _ 0 hi]
        exact List.getElem_mem hi
      obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hq.mem_iff.mp hmem)
      omega
    have hnd : q.Nodup := hq.nodup_iff.mpr List.nodup_range'
    have hidxlast : q.idxOf (q.getD (q.length - 1) 0) = q.length - 1 := by
      rw [List.getD_eq_getElem _ 0 (by omega)]
      simpa using List.get_idxOf hnd ⟨q.length - 1, by omega⟩
    have hfinal : hat q (q.getD (q.length - 1) 0) = q.getD s 0 := by
      unfold hat
      rw [hidxlast, if_neg (by intro hh; omega)]
      congr 1
      exact Nat.findGreatest_eq_iff.mpr
        ⟨by omega, fun _ => hsrec, fun j hsj hj => hnorec j hsj (by omega)⟩
    let t := q.getD (q.length - 1) 0
    have htmem : t ∈ q := by
      dsimp [t]
      rw [List.getD_eq_getElem _ 0 (by omega : q.length - 1 < q.length)]
      exact List.getElem_mem (by omega : q.length - 1 < q.length)
    have htpos : 0 < t := by
      obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hq.mem_iff.mp htmem)
      omega
    have htbound : t ≤ q.length := by
      obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hq.mem_iff.mp htmem)
      omega
    have hBget (x : ℕ) (hx0 : 0 < x) (hxn : x ≤ q.length) :
        (B q).getD (x - 1) 0 = hat q x := by
      have hindex : x - 1 < q.length := by omega
      rw [List.getD_eq_getElem _ 0 (by simpa using hindex)]
      simp [List.getElem_range', Nat.add_sub_of_le hx0]
    have hhat_t : hat q t = q.length := by
      simpa [t] using hfinal.trans hsmax
    by_cases htone : t = 1
    · left
      have hBfirst : (B q).getD 0 0 = q.length := by
        simpa [htone] using (hBget t htpos htbound).trans hhat_t
      rw [← hpB]
      simpa only [List.length_map, List.length_range', hqLen] using hBfirst
    have httwo : 1 < t := by omega
    by_cases hslast : s = q.length - 1
    · right
      left
      have htq : t = q.length := by
        dsimp [t]
        rw [← hslast]
        exact hsmax
      have hhatn : hat q q.length = q.length := by simpa [htq] using hhat_t
      have hBlast : (B q).getD (q.length - 1) 0 = q.length := by
        exact (hBget q.length (by omega) (le_refl _)).trans hhatn
      rw [hpB] at hBlast
      simpa only [hqLen] using hBlast
    have hs0 : s = 0 := by
      by_contra hsne
      have htail : s + 1 < q.length := by omega
      have hpre := final_block_predecessor_one q hq havoidq havoidB
        s (by omega) htail hsmax
      exact htone (by simpa [t] using hpre)
    have hfirst : q.getD 0 0 = q.length := by simpa [hs0] using hsmax
    have hsecond : q.getD 1 0 = 1 :=
      one_block_second_one q hq havoidq havoidB hnq hfirst httwo
    let r := q.drop 1
    have hcons : q = q.length :: r := by
      have hzero : q[0] = q.length := by
        simpa only [List.getD_eq_getElem _ 0 (by omega : 0 < q.length)] using hfirst
      simpa only [List.drop_zero, Nat.zero_add, hzero, r] using
        (List.cons_getElem_drop_succ (l := q) (n := 0) (h := by omega)).symm
    have hrperm : r.Perm (List.range' 1 (q.length - 1)) := by
      apply List.Perm.cons_inv (a := q.length)
      rw [← hcons]
      have hrange : List.range' 1 q.length = List.range' 1 (q.length - 1) ++ [q.length] := by
        simpa only [show q.length - 1 + 1 = q.length by omega,
          show 1 + (q.length - 1) = q.length by omega] using
          (List.range'_1_concat (s := 1) (n := q.length - 1))
      exact hq.trans (hrange ▸ List.perm_append_comm)
    have hrpair : r.Pairwise (· < ·) := by
      apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij
      have hil : i + 1 < q.length := by simp [r] at hi; omega
      have hjl : j + 1 < q.length := by simp [r] at hj; omega
      by_cases hi0 : i = 0
      · subst i
        have positive : 1 ≤ r[j] := by
          obtain ⟨offset, _, value⟩ := List.mem_range'.mp
            (hrperm.mem_iff.mp (List.getElem_mem hj))
          omega
        have first_min : r[0] = 1 := by
          simpa only [r, List.getElem_drop, Nat.add_zero,
            List.getD_eq_getElem _ 0 (by omega : 1 < q.length)] using hsecond
        have distinct : r[j] ≠ r[0] := by
          intro equal
          have := ((hrperm.nodup_iff.mpr List.nodup_range').getElem_inj_iff).mp equal
          omega
        omega
      · have increasing := suffix_after_one_increasing q hq havoidq 1
          (i + 1) (j + 1) (by omega) (by omega) hjl hsecond
        simpa only [r, List.getElem_drop, Nat.add_comm, List.getD_eq_getElem _ 0 hil,
          List.getD_eq_getElem _ 0 hjl] using increasing
    have hr : r = List.range' 1 (q.length - 1) :=
      List.Pairwise.eq_of_mem_iff hrpair (List.pairwise_lt_range' 1 (by omega))
        (fun _ => hrperm.mem_iff)
    have hmaxq : ∀ y ∈ q, y ≤ q.getD 0 0 := by
      intro y hy
      obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hq.mem_iff.mp hy)
      omega
    have hqentry (x : ℕ) (hx0 : 0 < x) (hxn : x < q.length) :
        q.getD x 0 = x := by
      have heq : x = (x - 1) + 1 := by omega
      rw [hcons, hr]
      conv_lhs => rw [heq]
      have hrange : x - 1 < (List.range' 1 (q.length - 1)).length := by
        simp
        omega
      rw [List.getD_cons_succ]
      rw [List.getD_eq_getElem _ 0 hrange]
      simp [List.getElem_range']
      omega
    have hhat_low (x : ℕ) (hx0 : 0 < x) (hxn : x < q.length) :
        hat q x = x + 1 := by
      have hidx : q.idxOf x = x := by
        have hget : q.getD x 0 = x := hqentry x hx0 hxn
        rw [List.getD_eq_getElem _ 0 hxn] at hget
        simpa [hget] using (List.get_idxOf hnd ⟨x, hxn⟩)
      have hxmem : x ∈ q := hq.mem_iff.mpr
        (List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩)
      rw [hat_one_block q hmaxq x hxmem, hidx]
      by_cases hnext : x + 1 < q.length
      · rw [if_pos hnext, hqentry (x + 1) (by omega) hnext]
      · have hlast : x + 1 = q.length := by omega
        rw [if_neg hnext, hfirst]
        omega
    have hhat_max : hat q q.length = 1 := by
      have hidx : q.idxOf q.length = 0 := hs0
      rw [hat_one_block q hmaxq q.length hnmem, hidx, if_pos (by omega)]
      exact hsecond
    have hC : B q = List.range' 2 (q.length - 1) ++ [1] := by
      apply List.ext_getElem (by simp; omega)
      intro index left_bound right_bound
      have bound : index < q.length := by simpa using left_bound
      simp only [List.getElem_map, List.getElem_range'_1]
      by_cases last : index = q.length - 1
      · subst index
        simpa only [show 1 + (q.length - 1) = q.length by omega,
          List.getElem_append, List.length_range',
          dif_neg (Nat.lt_irrefl (q.length - 1)), Nat.sub_self,
          List.getElem_cons_zero] using hhat_max
      · have inner : index < q.length - 1 := by omega
        simpa only [List.getElem_append, List.length_range', dif_pos inner,
          List.getElem_range'_1, show 1 + index = index + 1 by omega,
          show 2 + index = index + 1 + 1 by omega] using
          hhat_low (index + 1) (by omega) (by omega)
    right
    right
    simpa [hqLen, n] using hpB.symm.trans hC
  have pattern (word : List ℕ) (first middle last : ℕ)
      (hfirst : first < middle) (hmiddle : middle < last) (hlast : last < word.length)
      (hsmall : word.getD first 0 < word.getD last 0)
      (hlarge : word.getD last 0 < word.getD middle 0) :
      Contains [1, 3, 2] [] 3 word := by
    have hfirstBound : first < word.length := by omega
    have hmiddleBound : middle < word.length := by omega
    let values : ℕ → ℕ := fun index => if index = 1 then word.getD first 0
      else if index = 2 then word.getD last 0 else word.getD middle 0
    have hsub : [word.getD first 0, word.getD middle 0, word.getD last 0].Sublist
        word := by
      let positions : Fin 3 → Fin word.length := fun index =>
        if index.val = 0 then ⟨first, hfirstBound⟩
        else if index.val = 1 then ⟨middle, hmiddleBound⟩ else ⟨last, hlast⟩
      have hmono : StrictMono positions := by
        intro left right hlt
        fin_cases left <;> fin_cases right <;> (simp_all [positions] <;> omega)
      apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
      refine ⟨OrderEmbedding.ofStrictMono positions hmono, ?_⟩
      intro index
      fin_cases index
      · change word.getD first 0 = word[first]
        exact List.getD_eq_getElem _ 0 hfirstBound
      · change word.getD middle 0 = word[middle]
        exact List.getD_eq_getElem _ 0 hmiddleBound
      · change word.getD last 0 = word[last]
        exact List.getD_eq_getElem _ 0 hlast
    refine ⟨values, ?_, ?_, ?_, by simp⟩
    · intro index hpositive hbound
      have hcases : index = 1 ∨ index = 2 := by omega
      rcases hcases with rfl | rfl
      · change word.getD first 0 < word.getD last 0
        exact hsmall
      · change word.getD last 0 < word.getD middle 0
        exact hlarge
    · intro index hpositive hbound
      have hcases : index = 1 ∨ index = 2 ∨ index = 3 := by omega
      rcases hcases with rfl | rfl | rfl
      · change word.getD first 0 ∈ word
        rw [List.getD_eq_getElem _ 0 hfirstBound]
        exact List.getElem_mem hfirstBound
      · change word.getD last 0 ∈ word
        rw [List.getD_eq_getElem _ 0 hlast]
        exact List.getElem_mem hlast
      · change word.getD middle 0 ∈ word
        rw [List.getD_eq_getElem _ 0 hmiddleBound]
        exact List.getElem_mem hmiddleBound
    · simpa [values] using hsub
  have hnodup : parameter.Nodup := hperm.nodup_iff.mpr List.nodup_range'
  have hinjective (left right : ℕ) (hleft : left < parameter.length)
      (hright : right < parameter.length)
      (hequal : parameter.getD left 0 = parameter.getD right 0) : left = right := by
    rw [List.getD_eq_getElem _ 0 hleft, List.getD_eq_getElem _ 0 hright] at hequal
    exact hnodup.getElem_inj_iff.mp hequal
  constructor
  · by_cases hlarge : 3 ≤ parameter.length
    · have htests := (P_cycle_reduction parameter hperm (by omega)).2.2.1.mp hmember
      rcases theta_pair_position parameter hperm htests.1 htests.2.1 hlarge with
        hfirst | hlast | hshift
      · exact Or.inl hfirst
      · exact Or.inr hlast
      · exfalso
        have hget (index : ℕ) (hindex : index < parameter.length - 1) :
            parameter.getD index 0 = 2 + index := by
          rw [hshift, List.getD_append _ _ _ _ (by simp; omega)]
          rw [List.getD_eq_getElem _ 0 (by simp; omega)]
          simp
        have hlast : parameter.getD (parameter.length - 1) 0 = 1 := by
          rw [hshift, List.getD_append_right _ _ _ _ (by simp)]
          simp
        have hidxLast : parameter.idxOf 1 = parameter.length - 1 := by
          calc
            parameter.idxOf 1 = parameter.idxOf
                (parameter.getD (parameter.length - 1) 0) :=
              congrArg (fun value => parameter.idxOf value) hlast.symm
            _ = parameter.length - 1 := by
              rw [List.getD_eq_getElem _ 0 (by omega)]
              exact List.get_idxOf hnodup ⟨parameter.length - 1, by omega⟩
        have hidxTwo : parameter.idxOf 2 = 0 := by
          have hzero : parameter.getD 0 0 = 2 := by simpa using hget 0 (by omega)
          calc
            parameter.idxOf 2 = parameter.idxOf (parameter.getD 0 0) :=
              congrArg (fun value => parameter.idxOf value) hzero.symm
            _ = 0 := by
              rw [List.getD_eq_getElem _ 0 (by omega)]
              exact List.get_idxOf hnodup ⟨0, by omega⟩
        have hone : 1 ∈ parameter := hperm.mem_iff.mpr
          (List.mem_range'.mpr ⟨0, by omega, by omega⟩)
        have htwo : 2 ∈ parameter := hperm.mem_iff.mpr
          (List.mem_range'.mpr ⟨1, by omega, by omega⟩)
        have himages :=
          (ThetaIterateCycleReduction.P_cycle_reduction parameter hperm (by omega)).2.2.2
        have hfirstValue : (P parameter).getD 1 0 = 1 := by
          rw [himages.2.2 1 hone, hidxLast, if_neg (by omega)]
        have hmiddleValue : (P parameter).getD 2 0 = 4 := by
          rw [himages.2.2 2 htwo, hidxTwo, if_pos (by omega), hget 1 (by omega)]
        have hfinalValue : (P parameter).getD (parameter.length + 1) 0 = 3 := by
          rw [himages.2.1, hget 0 (by omega)]
        exact (hmember.2 0 (by omega)) (by
          simpa using pattern (P parameter) 1 2 (parameter.length + 1)
            (by omega) (by omega) (by simp [P])
            (by omega) (by omega))
    · have hlength : parameter.length = 2 := by omega
      have hmax : parameter.length ∈ parameter := hperm.mem_iff.mpr
        (List.mem_range'.mpr ⟨parameter.length - 1, by omega, by omega⟩)
      have hindex : parameter.idxOf parameter.length < parameter.length :=
        List.idxOf_lt_length_of_mem hmax
      have hvalue : parameter.getD (parameter.idxOf parameter.length) 0 =
          parameter.length := by
        rw [List.getD_eq_getElem _ 0 hindex]
        exact List.getElem_idxOf hindex
      have hcases : parameter.idxOf parameter.length = 0 ∨
          parameter.idxOf parameter.length = parameter.length - 1 := by omega
      rcases hcases with hfirst | hlast
      · exact Or.inl (by simpa [hfirst] using hvalue)
      · exact Or.inr (by simpa [hlast] using hvalue)
  · rintro ⟨hfirst, hlast⟩
    have hequal := hinjective 0 (parameter.length - 1) (by omega) (by omega)
      (hfirst.trans hlast.symm)
    omega

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateEndpoints
