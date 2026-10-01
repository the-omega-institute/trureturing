/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateVFamilies
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateVFamilies
   mirror-E: none(waiver:first-endpoint-reflection-family)
   anchors: []
   utility: none
   digest: Reflection cycles certify the descending first-endpoint family at every size. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateUFamilies
import D5.S3.Combinatorics.FundamentalBijection.ThetaIteratePositionBlocks
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseBlocks
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseGeneral

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateVFamilies

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArcherCyclicDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycle
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycleReduction
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords

open D5.S3.Combinatorics.FundamentalBijection
open ThetaBasicInverse ThetaIterateRecords ThetaIteratePosition

local notation "B" =>
  (fun word : List ℕ => List.map (hat word) (List.range' 1 (List.length word)))

set_option maxHeartbeats 1600000 in
theorem V_family (h : ℕ) (hh : 2 ≤ h) :
    let r := (List.range' 1 h).reverse
    ThetaFixedDefs.theta r =
      (if h % 2 = 1 then [h / 2 + 1] else []) ++
        (List.range' (h / 2 + 1 + h % 2) (h / 2)).flatMap (fun x => [x, h + 1 - x]) ∧
      b r = List.range' 1 h ∧
      (∀ p : List ℕ, p.Perm (List.range' 1 h) → p.getD 0 0 = h →
        p.getD (h - 1) 0 = 1 →
        (P p ∈ ThetaIterateDefs.iterateAvoiders (h + 2) 2 [1, 3, 2] ↔ p = r)) ∧
      (4 ≤ h → Contains [1, 3, 2] [] 3
        (ThetaFixedDefs.theta (ThetaFixedDefs.theta r))) := by
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
  have contains132_iff_indices (p : List ℕ) :
      Contains [1, 3, 2] [] 3 p ↔
        ∃ i j k : Fin p.length, i < j ∧ j < k ∧ p[i.val] < p[k.val] ∧
          p[k.val] < p[j.val] := by
    constructor
    · rintro ⟨x, hlt, _, hsub, _⟩
      change List.Sublist [x 1, x 3, x 2] p at hsub
      obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      have h0 : p[(f ⟨0, by simp⟩).val] = x 1 := by simpa using (hf ⟨0, by simp⟩).symm
      have h1 : p[(f ⟨1, by simp⟩).val] = x 3 := by simpa using (hf ⟨1, by simp⟩).symm
      have h2 : p[(f ⟨2, by simp⟩).val] = x 2 := by simpa using (hf ⟨2, by simp⟩).symm
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

  let r := (List.range' 1 h).reverse
  let t := h / 2
  let e := h % 2
  let c := t + 1
  have he : e = 0 ∨ e = 1 := by dsimp [e]; omega
  have hsize : h = 2 * t + e := by dsimp [t, e]; omega
  have hlen : r.length = h := by simp [r]
  have hperm : r.Perm (List.range' 1 h) := List.reverse_perm _
  have hget (i : ℕ) (hi : i < h) : r.getD i 0 = h - i := by
    rw [List.getD_eq_getElem _ 0 (by omega)]
    simp only [r, List.getElem_reverse, List.length_range', List.getElem_range'_1]; omega
  have himage (x : ℕ) (hx : 1 ≤ x) (hxh : x ≤ h) : image r x = h + 1 - x := by
    unfold image
    rw [hget _ (by omega)]; omega
  have hsplit : List.range h = 0 :: 1 :: List.range' 2 (h - 2) := by
    rw [List.range_eq_range', show h = (h - 2 + 1) + 1 by omega,
      List.range'_succ, List.range'_succ]
    rfl
  have hcycle (x : ℕ) (hx : 1 ≤ x) (hxh : x ≤ h) :
      ThetaFixedDefs.cycleFrom r x =
        if h + 1 - x = x then [x] else [x, h + 1 - x] := by
    have hpartner : 1 ≤ h + 1 - x ∧ h + 1 - x ≤ h := by omega
    have hreturn : (image r)^[2] x = x := by
      rw [show 2 = 1 + 1 from rfl, Function.iterate_succ_apply',
        Function.iterate_one, himage x hx hxh,
        himage _ hpartner.1 hpartner.2]
      omega
    unfold ThetaFixedDefs.cycleFrom
    rw [hlen, hsplit]; simp only [List.map_cons, Function.iterate_one, Nat.zero_add,
      himage x hx hxh, hreturn]
    by_cases hfix : h + 1 - x = x
    · simp [hfix]
    · simp [hfix]
  have hleader (x : ℕ) (hx : 1 ≤ x) (hxh : x ≤ h) :
      ThetaFixedDefs.IsLeader r x ↔ c ≤ x := by
    unfold ThetaFixedDefs.IsLeader
    rw [hcycle x hx hxh]
    split_ifs <;> simp only [List.mem_cons, List.not_mem_nil, or_false]
    · constructor <;> intro hcond <;> dsimp [c, t] at * <;> omega
    · constructor
      · intro hcond
        have hle := hcond (h + 1 - x) (Or.inr rfl)
        dsimp [c, t]; omega
      · intro hcond y hy
        rcases hy with rfl | rfl <;> dsimp [c, t] at hcond <;> omega
  have hfilter : (List.range' 1 h).filter
      (fun x => decide (ThetaFixedDefs.IsLeader r x)) = List.range' c (h - t) := by
    have heq : List.range' 1 h = List.range' 1 t ++ List.range' c (h - t) := by
      simpa only [c, Nat.add_comm 1 t, show t + (h - t) = h by omega] using
        (List.range'_append_1 (s := 1) (m := t) (n := h - t)).symm
    rw [heq, List.filter_append]
    have hleft : (List.range' 1 t).filter
        (fun x => decide (ThetaFixedDefs.IsLeader r x)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      obtain ⟨i, hi, heq⟩ := List.mem_range'.mp hx
      have hxpos : 1 ≤ x := by omega
      have hxh : x ≤ h := by dsimp [t] at hi; omega
      simp only [decide_eq_true_eq, hleader x hxpos hxh]
      dsimp [c]; omega
    have hright : (List.range' c (h - t)).filter
        (fun x => decide (ThetaFixedDefs.IsLeader r x)) = List.range' c (h - t) := by
      apply List.filter_eq_self.mpr
      intro x hx
      obtain ⟨i, hi, heq⟩ := List.mem_range'.mp hx
      have hxpos : 1 ≤ x := by dsimp [c] at heq; omega
      have hxh : x ≤ h := by dsimp [c, t] at *; omega
      simp only [hleader x hxpos hxh, decide_eq_true_eq]
      dsimp [c] at *; omega
    rw [hleft, hright, List.nil_append]
  let pairs := fun s k : ℕ => (List.range' s k).flatMap (fun x => [x, h + 1 - x])
  have htheta : ThetaFixedDefs.theta r = (if e = 1 then [c] else []) ++ pairs (c + e) t := by
    unfold ThetaFixedDefs.theta
    rw [hlen, hfilter]
    have hcycles : (List.range' (c + e) t).flatMap (ThetaFixedDefs.cycleFrom r) =
        pairs (c + e) t := by
      apply List.flatMap_congr
      intro x hx
      obtain ⟨i, hi, heq⟩ := List.mem_range'.mp hx
      have hxpos : 1 ≤ x := by dsimp [c] at heq; omega
      have hxh : x ≤ h := by dsimp [c] at heq; omega
      rw [hcycle x hxpos hxh, if_neg (by dsimp [c] at heq; omega)]
    rcases he with he | he
    · rw [he, if_neg (by omega : ¬(0 : ℕ) = 1), List.nil_append]
      have hsub : h - t = t := by omega
      simpa only [he, hsub, Nat.add_zero] using hcycles
    · rw [he, if_pos rfl]
      have hsub : h - t = t + 1 := by omega
      rw [hsub, List.range'_succ, List.flatMap_cons,
        hcycle c (by dsimp [c]; omega) (by dsimp [c]; omega),
        if_pos (by dsimp [c]; omega)]
      rw [he] at hcycles; exact congrArg (fun word : List ℕ => [c] ++ word) hcycles
  have hpairlen (s k : ℕ) : (pairs s k).length = 2 * k := by
    induction k generalizing s with
    | zero => simp [pairs]
    | succ k ih =>
        simp only [pairs, List.range'_succ, List.flatMap_cons, List.length_append,
          List.length_cons, List.length_nil]
        change 2 + (pairs (s + 1) k).length = 2 * (k + 1)
        rw [ih]; omega
  have hpairget (s k i : ℕ) (hi : i < 2 * k) :
      (pairs s k).getD i 0 =
        if i % 2 = 0 then s + i / 2 else h + 1 - (s + i / 2) := by
    induction k generalizing s i with
    | zero => omega
    | succ k ih =>
        have hcons : pairs s (k + 1) = s :: (h + 1 - s) :: pairs (s + 1) k := by
          simp [pairs, List.range'_succ]
        rw [hcons]
        by_cases hiz : i = 0
        · subst i; simp
        · by_cases hio : i = 1
          · subst i; simp
          · have hib : i - 2 < 2 * k := by omega
            rw [show i = (i - 2) + 1 + 1 by omega,
              List.getD_cons_succ, List.getD_cons_succ, ih _ _ hib]
            split_ifs <;> omega
  let q := (if e = 1 then [c] else []) ++ pairs (c + e) t
  have hqlen : q.length = h := by
    dsimp [q]; rw [List.length_append, hpairlen]
    rcases he with he | he <;> simp [he] <;> omega
  have hqget (i : ℕ) (hi : i < h) : q.getD i 0 =
      if i < e then c else if (i - e) % 2 = 0 then c + e + (i - e) / 2
        else h + 1 - (c + e + (i - e) / 2) := by
    rcases he with he | he
    · simp only [q, he, if_neg (by omega : ¬(0 : ℕ) = 1), List.nil_append,
        Nat.add_zero, Nat.sub_zero, if_neg (by omega : ¬i < 0)]
      exact hpairget c t i (by omega)
    · simp only [q, he, if_true, List.singleton_append]
      by_cases hiz : i = 0
      · subst i; simp
      · rw [show i = (i - 1) + 1 by omega, List.getD_cons_succ]
        have hget := hpairget (c + 1) t (i - 1) (by omega)
        simpa only [show ¬i - 1 + 1 < 1 by omega, if_false,
          show i - 1 + 1 - 1 = i - 1 by omega] using hget
  have havtheta : ¬ Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta r) := by
    rw [htheta]
    change ¬ Contains [1, 3, 2] [] 3 q
    intro hc
    obtain ⟨i, j, k, hij, hjk, hik, hkj⟩ := (contains132_iff_indices q).mp hc
    have hi : i.val < h := by simpa [hqlen] using i.isLt
    have hj : j.val < h := by simpa [hqlen] using j.isLt
    have hk : k.val < h := by simpa [hqlen] using k.isLt
    rw [← List.getD_eq_getElem _ 0 i.isLt, ← List.getD_eq_getElem _ 0 k.isLt,
      hqget i hi, hqget k hk] at hik
    rw [← List.getD_eq_getElem _ 0 k.isLt, ← List.getD_eq_getElem _ 0 j.isLt,
      hqget k hk, hqget j hj] at hkj
    dsimp [c] at hik hkj
    split_ifs at hik hkj <;> omega
  have hidx (x : ℕ) (hx : 1 ≤ x) (hxh : x ≤ h) : r.idxOf x = h - x := by
    have hnd : r.Nodup := hperm.nodup_iff.mpr List.nodup_range'
    have hib : h - x < r.length := by omega
    have hval : r[h - x] = x := by rw [← List.getD_eq_getElem _ 0 hib, hget _ (by omega)]; omega
    have hidx := List.get_idxOf hnd ⟨h - x, hib⟩
    change r.idxOf r[h - x] = h - x at hidx
    simpa only [hval] using hidx
  have hbword : b r = List.range' 1 h := by
    apply List.ext_getElem
    · simp [b, hlen]
    · intro i hi hj
      have hib : i < h := by simpa using hj
      rw [← List.getD_eq_getElem _ 0 hi, List.getD_eq_getElem _ 0 hi]
      simp only [b, List.getElem_map, List.getElem_range'_1, hlen]
      rw [hidx _ (by omega) (by omega)]
      by_cases hiz : i = 0
      · subst i
        rw [if_neg (by omega : ¬h - 1 + 1 < h)]
      · rw [if_pos (by omega : h - (1 + i) + 1 < h), hget _ (by omega)]
        omega
  have havr : ¬ Contains [1, 3, 2] [] 3 r := by
    intro hc
    obtain ⟨i, j, k, hij, hjk, hik, hkj⟩ := (contains132_iff_indices r).mp hc
    rw [← List.getD_eq_getElem _ 0 i.isLt, ← List.getD_eq_getElem _ 0 k.isLt,
      hget i (by omega), hget k (by omega)] at hik
    have := i.isLt
    have := k.isLt
    omega
  have havb : ¬ Contains [1, 3, 2] [] 3 (b r) := by
    rw [hbword]
    intro hc
    obtain ⟨i, j, k, hij, hjk, hik, hkj⟩ := (contains132_iff_indices (List.range' 1 h)).mp hc
    simp only [List.getElem_range'_1] at hkj; omega
  have hvalid : r.Perm (List.range' 1 r.length) := by simpa [hlen] using hperm
  have hmember := (P_cycle_reduction r hvalid (by omega)).2.2.1.mpr
    ⟨havr, havtheta, havb, by
      intro i j hij hj hcross
      have hfirst : r.getD 0 0 = h := by rw [hget _ (by omega)]; omega
      have hbig := hcross.2
      rw [hfirst, hbword, List.getD_eq_getElem _ 0 (by simp; omega),
        List.getElem_range'_1] at hbig
      omega⟩
  refine ⟨htheta, hbword, ?_, ?_⟩
  · intro p hp hpfirst hplast
    have hplen : p.length = h := by simpa using hp.length_eq
    have hpvalid : p.Perm (List.range' 1 p.length) := by simpa [hplen] using hp
    constructor
    · intro hpmember
      have htests := (P_cycle_reduction p hpvalid (by omega)).2.2.1.mp
        (by simpa [hplen] using hpmember)
      have heq := ThetaIterateFirstEndpoint.descending_of_last_one_and_b_avoids p hpvalid
        (by omega) (by simpa [hplen] using hpfirst) (by simpa [hplen] using hplast)
        htests.2.2.1
      simpa only [hplen] using heq
    · rintro rfl
      simpa only [hlen] using hmember
  · intro hfour
    classical
    change Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta (ThetaFixedDefs.theta r))
    rw [htheta]
    change Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta q)
    have hqperm : q.Perm (List.range' 1 q.length) := by
      have hpermtheta := (theta_record_inverse r hvalid).2.2.1
      simpa only [htheta, hlen, hqlen] using hpermtheta
    have hqfirst : q.getD 0 0 = c := by
      rw [hqget 0 (by omega)]
      rcases he with he | he <;> simp [he]
    have hqlast : q.getD (h - 1) 0 = 1 := by
      rw [hqget _ (by omega)]
      split_ifs <;> dsimp [c, t, e] at * <;> omega
    by_contra hnot
    have hposition := theta_pair_position q hqperm
      (by simpa only [htheta] using havtheta) hnot (by omega)
    rw [hqlen, hqfirst, hqlast] at hposition
    rcases hposition with hfirst | hlast | hshift
    · dsimp [c, t] at hfirst
      omega
    · omega
    · have hhead := congrArg (fun word : List ℕ => word.getD 0 0) hshift
      rw [hqfirst, List.getD_append _ _ _ _ (by simp; omega),
        List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range'_1] at hhead
      dsimp [c, t] at hhead; omega

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateVFamilies
