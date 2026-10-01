/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateEndpointShape
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateEndpointShape
   mirror-E: none(waiver:last-endpoint-obstructions)
   anchors: []
   utility: none
   digest: Predecessor obstructions reconstruct the surviving final-maximum stems. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycleReduction
import D5.S3.Combinatorics.FundamentalBijection.ThetaIteratePositionBlocks
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseBlocks
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseGeneral
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateTail
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateLastEndpoint
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateExceptional

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateEndpointShape

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
theorem last_endpoint_shape (stem : List ℕ)
    (hperm : stem.Perm (List.range' 1 stem.length)) (hsize : 3 ≤ stem.length) :
    P (stem ++ [stem.length + 1]) ∈
        ThetaIterateDefs.iterateAvoiders (stem.length + 3) 2 [1, 3, 2] ↔
      stem = List.range' 1 stem.length ∨
        stem = List.range' 2 (stem.length - 1) ++ [1] ∨
        (stem.getD 0 0 = stem.length ∧ stem.getD (stem.length - 1) 0 = 1 ∧
          (List.range' 1 stem.length).map (hat stem) ∈
            ThetaIterateDefs.iterateAvoiders stem.length 2 [1, 3, 2]) := by
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
              intro j hj; omega))
        simpa only [hg] using last_record_bounds_prefix p (s + i) hsi (s + i) (le_refl _)
      let records := (List.Ico 0 p.length).filter (IsLtrMax p)
      have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
      have hleader (x : ℕ) (hx : x ∈ p) :
          ThetaFixedDefs.IsLeader (B p) x ↔ IsLtrMax p (p.idxOf x) := by
        have hidx : p.idxOf x < p.length := List.idxOf_lt_length_of_mem hx
        have hget : p.getD (p.idxOf x) 0 = x := by
          rw [List.getD_eq_getElem _ 0 hidx]; exact List.getElem_idxOf hidx
        constructor
        · intro hlead
          by_contra hnon
          exact (nonrecord_not_B_leader p hp x hx hnon) hlead
        · intro hrec
          rw [← hget]; exact record_is_B_leader p hp _ hidx hrec
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
          rw [List.getD_eq_getElem _ 0 hil]; exact List.getElem_mem hil
        have hidx : p.idxOf (p.getD i 0) = i := by
          rw [List.getD_eq_getElem _ 0 hil]; simpa using (List.get_idxOf hnodup ⟨i, hil⟩)
        apply List.mem_filter.mpr
        refine ⟨hp.mem_iff.mp hxp, ?_⟩
        have hrec : IsLtrMax p (p.idxOf (p.getD i 0)) := by
          rw [hidx]; exact decide_eq_true_eq.mp hirec
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
          rw [List.getD_eq_getElem _ 0 hg]; exact List.getElem_mem hg
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
          dsimp [e, nextBoundary]; simp only [dif_pos hsn]
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
    have htheta : q = w.val := by dsimp [q]; rw [← hB]; exact hleft w.val (hvalid w)
    refine ⟨hleft, B_perm, ?_, ?_⟩
    · change q.Perm (List.range' 1 h)
      rw [htheta]; exact w.property
    · change B q = p
      rw [htheta]; exact hB
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
          rw [List.getD_eq_getElem _ 0 hbound]; exact List.getElem_mem hbound
        have hle := hmaximum _ hmember
        omega
      have hgreatest : Nat.findGreatest (IsLtrMax word) (word.idxOf value) = 0 := by
        apply Nat.findGreatest_eq_zero_iff.mpr
        intro index hpositive hbound; exact hnonrecord index hpositive (by omega)
      unfold hat
      by_cases hnext : word.idxOf value + 1 < word.length
      · rw [if_pos ⟨hnext, hnonrecord _ (by omega) hnext⟩, if_pos hnext]
      · rw [if_neg (fun hcase => hnext hcase.1), if_neg hnext, hgreatest]
    let n := p.length
    let q := ThetaFixedDefs.theta p
    have hθ : q.Perm (List.range' 1 p.length) ∧ B q = p :=
      ⟨(theta_record_inverse p hp).2.2.1, (theta_record_inverse p hp).2.2.2⟩
    have hqLen : q.length = n := by simpa [q, n] using hθ.1.length_eq
    have hq : q.Perm (List.range' 1 q.length) := by simpa [hqLen, q, n] using hθ.1
    have hpB : B q = p := hθ.2
    have havoidq : ¬ Contains [1, 3, 2] [] 3 q := havoidθ
    have havoidB : ¬ Contains [1, 3, 2] [] 3 (B q) := by rw [hpB]; exact havoidp
    have hnq : 3 ≤ q.length := by omega
    have hnmem : q.length ∈ q := hq.mem_iff.mpr
      (List.mem_range'.mpr ⟨q.length - 1, by omega, by omega⟩)
    let s := q.idxOf q.length
    have hslen : s < q.length := List.idxOf_lt_length_of_mem hnmem
    have hsmax : q.getD s 0 = q.length := by
      rw [List.getD_eq_getElem _ 0 hslen]; exact List.getElem_idxOf hslen
    have hsrec : IsLtrMax q s := by
      intro i his
      have hi : i < q.length := by omega
      have hmem : q.getD i 0 ∈ q := by rw [List.getD_eq_getElem _ 0 hi]; exact List.getElem_mem hi
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
      have hmem : q.getD i 0 ∈ q := by rw [List.getD_eq_getElem _ 0 hi]; exact List.getElem_mem hi
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
      dsimp [t]; rw [List.getD_eq_getElem _ 0 (by omega : q.length - 1 < q.length)]
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
    have hhat_t : hat q t = q.length := by simpa [t] using hfinal.trans hsmax
    by_cases htone : t = 1
    · left
      have hBfirst : (B q).getD 0 0 = q.length := by
        simpa [htone] using (hBget t htpos htbound).trans hhat_t
      rw [← hpB]; simpa only [List.length_map, List.length_range', hqLen] using hBfirst
    have httwo : 1 < t := by omega
    by_cases hslast : s = q.length - 1
    · right
      left
      have htq : t = q.length := by dsimp [t]; rw [← hslast]; exact hsmax
      have hhatn : hat q q.length = q.length := by simpa [htq] using hhat_t
      have hBlast : (B q).getD (q.length - 1) 0 = q.length := by
        exact (hBget q.length (by omega) (le_refl _)).trans hhatn
      rw [hpB] at hBlast; simpa only [hqLen] using hBlast
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
      have h := (List.cons_getElem_drop_succ (l := q) (n := 0)
        (h := (by omega : 0 < q.length))).symm
      simpa only [List.drop_zero, Nat.zero_add, hzero, r] using h
    have hrlen : r.length = q.length - 1 := by simp [r]
    have hrmem (x : ℕ) : x ∈ r ↔ x ∈ q ∧ x ≠ q.length := by
      have hcontains : q.length ∉ r := by
        intro hx
        have htwo : (q.length :: r).Nodup := by simpa [← hcons] using hnd
        exact (List.nodup_cons.mp htwo).1 hx
      constructor
      · intro hx
        have hxq : x ∈ q := by rw [hcons]; simp [hx]
        have hxne : x ≠ q.length := by
          intro heq
          subst x
          exact hcontains hx
        exact ⟨hxq, hxne⟩
      · rintro ⟨hxq, hxne⟩
        rw [hcons] at hxq
        rcases List.mem_cons.mp hxq with h | h
        · exact (hxne h).elim
        · exact h
    have hrpair : r.Pairwise (· < ·) := by
      apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij
      have hil : i + 1 < q.length := by simp [r] at hi; omega
      have hjl : j + 1 < q.length := by simp [r] at hj; omega
      have hone : q.getD 1 0 = 1 := hsecond
      by_cases hi0 : i = 0
      · subst i
        have hmem : q.getD (j + 1) 0 ∈ q := by
          rw [List.getD_eq_getElem _ 0 hjl]; exact List.getElem_mem hjl
        obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hq.mem_iff.mp hmem)
        have hneq : q.getD (j + 1) 0 ≠ q.getD 1 0 := by
          intro heq
          have hval : q[j + 1] = q[1] := by
            simpa only [← List.getD_eq_getElem _ 0 hjl,
              ← List.getD_eq_getElem _ 0 (by omega : 1 < q.length)] using heq
          have := (hnd.getElem_inj_iff).mp hval
          omega
        have hlt : q.getD 1 0 < q.getD (j + 1) 0 := by omega
        have hlt' : q[1] < q[j + 1] := by
          simpa only [List.getD_eq_getElem _ 0 (by omega : 1 < q.length),
            List.getD_eq_getElem _ 0 hjl] using hlt
        simpa [r, List.getElem_drop] using hlt'
      · have hinc := suffix_after_one_increasing q hq havoidq 1
          (i + 1) (j + 1) (by omega) (by omega) hjl hsecond
        have hinc' : q[i + 1] < q[j + 1] := by
          simpa only [List.getD_eq_getElem _ 0 hil,
            List.getD_eq_getElem _ 0 hjl] using hinc
        simpa [r, List.getElem_drop] using hinc'
    have hrrange : (List.range' 1 (q.length - 1)).Pairwise (· < ·) :=
      List.pairwise_lt_range' 1 (by omega)
    have hr : r = List.range' 1 (q.length - 1) := by
      apply List.Pairwise.eq_of_mem_iff hrpair hrrange
      intro x; rw [hrmem]
      constructor
      · rintro ⟨hxq, hxne⟩
        obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hq.mem_iff.mp hxq)
        apply List.mem_range'.mpr
        refine ⟨x - 1, by omega, ?_⟩
        omega
      · intro hx
        obtain ⟨a, _, ha⟩ := List.mem_range'.mp hx
        refine ⟨hq.mem_iff.mpr (List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩), ?_⟩
        omega
    have hqword : q = q.length :: List.range' 1 (q.length - 1) := by simpa [hr] using hcons
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
      rw [List.getD_cons_succ]; rw [List.getD_eq_getElem _ 0 hrange]
      simp [List.getElem_range']; omega
    have hhat_low (x : ℕ) (hx0 : 0 < x) (hxn : x < q.length) :
        hat q x = x + 1 := by
      have hidx : q.idxOf x = x := by
        have hget : q.getD x 0 = x := hqentry x hx0 hxn
        rw [List.getD_eq_getElem _ 0 hxn] at hget; simpa [hget] using (List.get_idxOf hnd ⟨x, hxn⟩)
      have hxmem : x ∈ q := hq.mem_iff.mpr
        (List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩)
      rw [hat_one_block q hmaxq x hxmem, hidx]
      by_cases hnext : x + 1 < q.length
      · rw [if_pos hnext, hqentry (x + 1) (by omega) hnext]
      · have hlast : x + 1 = q.length := by omega
        rw [if_neg hnext, hfirst]; omega
    have hhat_max : hat q q.length = 1 := by
      have hidx : q.idxOf q.length = 0 := hs0
      rw [hat_one_block q hmaxq q.length hnmem, hidx, if_pos (by omega)]; exact hsecond
    have hC : B q = List.range' 2 (q.length - 1) ++ [1] := by
      have hBlength : (B q).length = q.length := by simp
      have hClength : (List.range' 2 (q.length - 1) ++ [1]).length = q.length := by
        simp
        omega
      apply List.ext_getElem (hBlength.trans hClength.symm)
      intro i hi hi'
      have hiq : i < q.length := by simpa [hBlength] using hi
      by_cases hlast : i = q.length - 1
      · subst i
        have hBval : (B q).getD (q.length - 1) 0 = 1 := by
          simpa using (hBget q.length (by omega) (le_refl _)).trans hhat_max
        have hCval : (List.range' 2 (q.length - 1) ++ [1]).getD
            (q.length - 1) 0 = 1 := by
          rw [List.getD_append_right _ _ _ _ (by simp)]
          simp
        have h := hBval.trans hCval.symm
        simpa only [List.getD_eq_getElem _ 0 (by omega : q.length - 1 < (B q).length),
          List.getD_eq_getElem _ 0 (by omega :
            q.length - 1 < (List.range' 2 (q.length - 1) ++ [1]).length)] using h
      · have hlow : i < q.length - 1 := by omega
        have hBval : (B q).getD i 0 = i + 2 := by
          have h := hBget (i + 1) (by omega) (by omega)
          have h' := h.trans (hhat_low (i + 1) (by omega) (by omega))
          simpa [show i + 1 - 1 = i by omega, show i + 1 + 1 = i + 2 by omega] using h'
        have hCval : (List.range' 2 (q.length - 1) ++ [1]).getD i 0 = i + 2 := by
          rw [List.getD_append _ _ _ _ (by simp; omega)]
          have hrange : i < (List.range' 2 (q.length - 1)).length := by
            simp
            omega
          rw [List.getD_eq_getElem _ 0 hrange]; simp [List.getElem_range']; omega
        have h := hBval.trans hCval.symm
        simpa only [List.getD_eq_getElem _ 0 (by omega : i < (B q).length),
          List.getD_eq_getElem _ 0 (by omega :
            i < (List.range' 2 (q.length - 1) ++ [1]).length)] using h
    right
    right
    simpa [hqLen, n] using hpB.symm.trans hC
  have first_one_identity (p : List ℕ)
      (hp : p.Perm (List.range' 1 p.length))
      (havoid : ¬ Contains [1, 3, 2] [] 3 p)
      (hpos : 0 < p.length) (hfirst : p.getD 0 0 = 1) :
      p = List.range' 1 p.length := by
    have hpair : p.Pairwise (· < ·) := by
      apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij
      have hzero : i = 0 ∨ 0 < i := by omega
      rcases hzero with rfl | hzero
      · have hone : p[0] = 1 := by
          simpa only [List.getD_eq_getElem _ 0 hpos] using hfirst
        have hpositive : 1 < p[j] := by
          have hmem : p[j] ∈ p := List.getElem_mem hj
          obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hp.mem_iff.mp hmem)
          have hne : p[j] ≠ p[0] := by
            intro heq
            have hnd : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
            have := (hnd.getElem_inj_iff).mp heq
            omega
          omega
        simpa only [hone] using hpositive
      · have h := ThetaIteratePosition.suffix_after_one_increasing p hp havoid
          0 i j hzero hij hj hfirst
        simpa only [List.getD_eq_getElem _ 0 hi,
          List.getD_eq_getElem _ 0 hj] using h
    have hrange : (List.range' 1 p.length).Pairwise (· < ·) :=
      List.pairwise_lt_range' 1 (by omega)
    apply List.Pairwise.eq_of_mem_iff hpair hrange
    intro x; exact hp.mem_iff
  refine Iff.intro (fun hmember => ?_) ?_
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
        rw [List.getD_eq_getElem _ 0 hfirstBound]; exact List.getElem_mem hfirstBound
      · change word.getD last 0 ∈ word
        rw [List.getD_eq_getElem _ 0 hlast]; exact List.getElem_mem hlast
      · change word.getD middle 0 ∈ word
        rw [List.getD_eq_getElem _ 0 hmiddleBound]; exact List.getElem_mem hmiddleBound
    · simpa [values] using hsub
  let parameter := stem ++ [stem.length + 1]
  have hlength : parameter.length = stem.length + 1 := by simp [parameter]
  have hparameter : parameter.Perm (List.range' 1 parameter.length) := by
    have hrange : List.range' 1 (stem.length + 1) =
        List.range' 1 stem.length ++ [stem.length + 1] := by
      simpa [Nat.add_comm] using
        (List.range'_append_1 (s := 1) (m := stem.length) (n := 1)).symm
    rw [hlength, hrange]; exact hperm.append (List.Perm.refl _)
  have hmember' : P parameter ∈
      ThetaIterateDefs.iterateAvoiders (parameter.length + 2) 2 [1, 3, 2] := by
    simpa only [hlength, Nat.add_assoc] using hmember
  have havoid : ¬ Contains [1, 3, 2] [] 3 stem := by
    have htests := (P_cycle_reduction parameter hparameter (by omega)).2.2.1.mp hmember'
    rintro ⟨values, hvalues, hmem, hsub, _⟩
    apply htests.1
    refine ⟨values, hvalues, ?_, ?_, by simp⟩
    · intro index hpositive hbound
      exact List.mem_append_left _ (hmem index hpositive hbound)
    · exact hsub.trans (List.sublist_append_left _ _)
  have hnodup : stem.Nodup := hperm.nodup_iff.mpr List.nodup_range'
  have hparameterNodup : parameter.Nodup :=
    hparameter.nodup_iff.mpr List.nodup_range'
  have hvalue (index : ℕ) (hindex : index < stem.length) :
      1 ≤ stem.getD index 0 ∧ stem.getD index 0 ≤ stem.length := by
    have hmem : stem.getD index 0 ∈ stem := by
      rw [List.getD_eq_getElem _ 0 hindex]; exact List.getElem_mem hindex
    obtain ⟨offset, hbound, hequal⟩ := List.mem_range'.mp (hperm.mem_iff.mp hmem)
    omega
  have hinjective (left right : ℕ) (hleft : left < stem.length)
      (hright : right < stem.length)
      (hequal : stem.getD left 0 = stem.getD right 0) : left = right := by
    rw [List.getD_eq_getElem _ 0 hleft, List.getD_eq_getElem _ 0 hright] at hequal
    exact hnodup.getElem_inj_iff.mp hequal
  have hstem (index : ℕ) (hindex : index < stem.length) :
      parameter.getD index 0 = stem.getD index 0 :=
    List.getD_append _ _ _ _ hindex
  have happended : parameter.getD stem.length 0 = stem.length + 1 := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp
  have himages :=
    (ThetaIterateCycleReduction.P_cycle_reduction parameter hparameter (by omega)).2.2.2
  have hsuccessor (index : ℕ) (hindex : index < parameter.length)
      (hnext : index + 1 < parameter.length) :
      (P parameter).getD (parameter.getD index 0) 0 =
        parameter.getD (index + 1) 0 + 1 := by
    have hmem : parameter.getD index 0 ∈ parameter := by
      rw [List.getD_eq_getElem _ 0 hindex]; exact List.getElem_mem hindex
    have hidx : parameter.idxOf (parameter.getD index 0) = index := by
      rw [List.getD_eq_getElem _ 0 hindex]; exact List.get_idxOf hparameterNodup ⟨index, hindex⟩
    rw [himages.2.2 _ hmem, hidx, if_pos hnext]
  have hfinal : (P parameter).getD (stem.length + 2) 0 = stem.getD 0 0 + 1 := by
    simpa only [hlength, hstem 0 (by omega), Nat.add_assoc] using himages.2.1
  have hPavoid : ¬ Contains [1, 3, 2] [] 3 (P parameter) := by simpa using hmember'.2 0 (by omega)
  have honeMem : 1 ∈ stem := hperm.mem_iff.mpr
    (List.mem_range'.mpr ⟨0, by omega, by omega⟩)
  have honeIndex : stem.idxOf 1 < stem.length := List.idxOf_lt_length_of_mem honeMem
  have honeValue : stem.getD (stem.idxOf 1) 0 = 1 := by
    rw [List.getD_eq_getElem _ 0 honeIndex]; exact List.getElem_idxOf honeIndex
  have restrictions :
      (stem.getD (stem.length - 1) 0 = stem.length →
        stem = List.range' 1 stem.length) ∧
      (stem.getD 0 0 = stem.length → stem.getD (stem.length - 1) 0 = 1) := by
    constructor
    · intro hlast
      by_cases hfirst : stem.getD 0 0 = 1
      · exact first_one_identity stem hperm havoid (by omega) hfirst
      · have hfirstBound := hvalue 0 (by omega)
        have honePositive : 0 < stem.idxOf 1 := by
          by_contra hnot
          have hzero : stem.idxOf 1 = 0 := by omega
          exact hfirst (by simpa [hzero] using honeValue)
        let predecessor := stem.getD (stem.idxOf 1 - 1) 0
        have hpredecessorBound := hvalue (stem.idxOf 1 - 1) (by omega)
        have hpredecessorNe : predecessor ≠ stem.length := by
          intro hequal
          have heq := hinjective (stem.idxOf 1 - 1) (stem.length - 1)
            (by omega) (by omega) (hequal.trans hlast.symm)
          omega
        have hpredecessorImage : (P parameter).getD predecessor 0 = 2 := by
          have hstep := hsuccessor (stem.idxOf 1 - 1) (by omega) (by omega)
          rw [hstem _ (by omega), show stem.idxOf 1 - 1 + 1 = stem.idxOf 1 by omega,
            hstem _ honeIndex, honeValue] at hstep
          exact hstep
        have hmaximumImage : (P parameter).getD stem.length 0 = stem.length + 2 := by
          have hstep := hsuccessor (stem.length - 1) (by omega) (by omega)
          rw [hstem _ (by omega), hlast,
            show stem.length - 1 + 1 = stem.length by omega, happended] at hstep
          simpa only [Nat.add_assoc] using hstep
        exact False.elim (hPavoid (pattern (P parameter) predecessor stem.length
          (stem.length + 2) (by dsimp [predecessor] at *; omega) (by omega)
          (by simp [P, hlength]) (by omega) (by omega)))
    · intro hfirst
      exact (ThetaIterateLastEndpoint.last_endpoint_cycle stem hperm (by omega) hfirst).1
        hmember
  have hthetaAvoid : ¬ Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta stem) := by
    have htests := (P_cycle_reduction parameter hparameter (by omega)).2.2.1.mp hmember'
    have hwhole := htests.2.1
    change ¬ Contains [1, 3, 2] [] 3
      (ThetaFixedDefs.theta (stem ++ [stem.length + 1])) at hwhole
    rw [ThetaIterateTail.theta_append_max stem hperm] at hwhole
    rintro ⟨values, hvalues, hmem, hsub, _⟩
    apply hwhole
    refine ⟨values, hvalues, ?_, ?_, by simp⟩
    · intro index hpositive hbound
      exact List.mem_append_left _ (hmem index hpositive hbound)
    · exact hsub.trans (List.sublist_append_left _ _)
  have hposition : stem.getD 0 0 = stem.length ∨
      stem.getD (stem.length - 1) 0 = stem.length ∨
      stem = List.range' 2 (stem.length - 1) ++ [1] := by
    exact theta_pair_position stem hperm havoid hthetaAvoid hsize
  rcases hposition with hfirst | hlast | hcyclic
  · have hcycle := ThetaIterateLastEndpoint.last_endpoint_cycle stem hperm (by omega) hfirst
    have hlast := hcycle.1 hmember
    exact Or.inr (Or.inr ⟨hfirst, hlast, (hcycle.2 hlast).2.2.mp hmember⟩)
  · exact Or.inl (restrictions.1 hlast)
  · exact Or.inr (Or.inl hcyclic)
  · intro hshape
    rcases hshape with hidentity | hcyclic | ⟨hfirst, hlast, hinverse⟩
    · let width := stem.length + 1
      let word := List.range' 1 width
      have hwidth : 4 ≤ width := by dsimp [width]; omega
      have hwordlen : word.length = width := by simp [word]
      have hparameter : stem ++ [stem.length + 1] = word := by
        change stem ++ [stem.length + 1] = List.range' 1 (stem.length + 1)
        calc
          stem ++ [stem.length + 1] =
              List.range' 1 stem.length ++ [stem.length + 1] :=
            congrArg (fun word => word ++ [stem.length + 1]) hidentity
          _ = List.range' 1 (stem.length + 1) := by
            simpa only [one_mul, Nat.add_comm] using
              (List.range'_concat (s := 1) (n := stem.length) (step := 1)).symm
      have hget (index : ℕ) (hi : index < width) : word.getD index 0 = index + 1 := by
        rw [List.getD_eq_getElem _ 0 (by omega)]; simp only [word, List.getElem_range'_1]; omega
      have hcycle (value : ℕ) (hv : value ∈ word) :
          ThetaFixedDefs.cycleFrom word value = [value] := by
        obtain ⟨offset, ho, heq⟩ := List.mem_range'.mp hv
        have himage : D5.S3.Combinatorics.ArcherCyclicDefs.image word value = value := by
          rw [D5.S3.Combinatorics.ArcherCyclicDefs.image, hget (value - 1) (by omega)]; omega
        have hiter (power : ℕ) :
            (D5.S3.Combinatorics.ArcherCyclicDefs.image word)^[power] value = value := by
          induction power with
          | zero => rfl
          | succ power ih => rw [Function.iterate_succ_apply', ih, himage]
        unfold ThetaFixedDefs.cycleFrom
        simp_rw [hiter]
        simp
      have hthetaIdentity : ThetaFixedDefs.theta word = word := by
        unfold ThetaFixedDefs.theta
        rw [hwordlen]
        have hfilter : (List.range' 1 width).filter
            (fun value => decide (ThetaFixedDefs.IsLeader word value)) = word := by
          apply List.filter_eq_self.mpr
          intro value hv; simp [ThetaFixedDefs.IsLeader, hcycle value hv]
        rw [hfilter]
        have hflat : word.flatMap (ThetaFixedDefs.cycleFrom word) =
            word.flatMap (fun value => [value]) := by
          apply List.flatMap_congr
          intro value hv; exact hcycle value hv
        simpa using hflat
      have hindices (values : List ℕ) (hp : Contains [1, 3, 2] [] 3 values) :
          ∃ first middle last : Fin values.length, first < middle ∧ middle < last ∧
            values[first.val] < values[last.val] ∧
              values[last.val] < values[middle.val] := by
        obtain ⟨selected, hselected, _, hsub, _⟩ := hp
        change List.Sublist [selected 1, selected 3, selected 2] values at hsub
        obtain ⟨positions, hpositions⟩ :=
          List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
        have hfirst : values[(positions ⟨0, by simp⟩).val] = selected 1 := by
          simpa using (hpositions ⟨0, by simp⟩).symm
        have hmiddle : values[(positions ⟨1, by simp⟩).val] = selected 3 := by
          simpa using (hpositions ⟨1, by simp⟩).symm
        have hlast : values[(positions ⟨2, by simp⟩).val] = selected 2 := by
          simpa using (hpositions ⟨2, by simp⟩).symm
        refine ⟨positions ⟨0, by simp⟩, positions ⟨1, by simp⟩,
          positions ⟨2, by simp⟩, positions.strictMono (by simp),
          positions.strictMono (by simp), ?_, ?_⟩
        · simpa only [hfirst, hlast] using hselected 1 (by omega) (by omega)
        · simpa only [hlast, hmiddle] using hselected 2 (by omega) (by omega)
      have hwordAvoid : ¬ Contains [1, 3, 2] [] 3 word := by
        intro hp
        obtain ⟨_, middle, last, _, hml, _, hlm⟩ := hindices word hp
        simp only [word, List.getElem_range'_1] at hlm; omega
      have hbget (index : ℕ) (hi : index < width) :
          (b word).getD index 0 = if index + 1 < width then index + 3 else 1 := by
        have hidx : word.idxOf (1 + index) = index := by
          have hval : word[index]'(by omega) = 1 + index := by simp [word]
          rw [← hval]; exact List.get_idxOf (l := word) List.nodup_range' ⟨index, by omega⟩
        rw [b, List.getD_eq_getElem _ 0 (by simp [hwordlen]; omega),
          List.getElem_map, List.getElem_range'_1]
        simp only [hidx, hwordlen]
        by_cases hnext : index + 1 < width
        · simp only [hnext, ↓reduceIte]
          rw [hget _ hnext]
        · simp only [hnext, ↓reduceIte]
      have hbAvoid : ¬ Contains [1, 3, 2] [] 3 (b word) := by
        intro hp
        obtain ⟨first, middle, last, hfm, hml, hfl, hlm⟩ := hindices _ hp
        have hblen : (b word).length = width := by simp [b, hwordlen]
        have hf : first.val < width := by simpa [hblen] using first.isLt
        have hm : middle.val < width := by simpa [hblen] using middle.isLt
        have hl : last.val < width := by simpa [hblen] using last.isLt
        simp only [← List.getD_eq_getElem _ 0 first.isLt,
          ← List.getD_eq_getElem _ 0 middle.isLt,
          ← List.getD_eq_getElem _ 0 last.isLt,
          hbget _ hf, hbget _ hm, hbget _ hl] at hfl hlm
        split_ifs at hfl hlm <;> omega
      have hcross : ∀ first middle, first < middle → middle < word.length →
          ¬ ((b word).getD first 0 < word.getD 0 0 + 1 ∧
            word.getD 0 0 + 1 < (b word).getD middle 0) := by
        intro first middle hfm hm hc
        have hm' : middle < width := by omega
        have hf : first < width := by omega
        rw [hget 0 (by omega), hbget first hf, hbget middle hm'] at hc
        split_ifs at hc <;> omega
      have htest := (P_cycle_reduction word (by simp [word, hwordlen])
        (by omega)).2.2.1
      have hm := htest.mpr ⟨hwordAvoid, by simpa only [hthetaIdentity] using hwordAvoid,
        hbAvoid, hcross⟩
      rw [hparameter]; simpa only [hwordlen, width, Nat.add_assoc] using hm
    · have h := (ThetaIterateExceptional.cyclic_last_endpoint stem.length hsize).2.2.2.1
      have heq : stem ++ [stem.length + 1] =
          (List.range' 2 (stem.length - 1) ++ [1]) ++ [stem.length + 1] := by
        exact congrArg (fun word => word ++ [stem.length + 1]) hcyclic
      rw [heq]; exact h
    · exact ((ThetaIterateLastEndpoint.last_endpoint_cycle stem hperm
        (by omega) hfirst).2 hlast).2.2.mpr hinverse

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateEndpointShape
