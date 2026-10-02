/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateDecomposition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateDecomposition
   mirror-E: none(waiver:second-layer-cycle-counting)
   anchors: []
   utility: none
   digest: Deleting the two outer cycle letters gives the disjoint second-layer decomposition. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateEndpointCount
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateUFamilies
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateTailCount
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateParametrization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateDecomposition

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.FundamentalBijection
open ThetaIterateCycle ThetaFixedDefs
open ThetaBasicInverse ThetaIterateRecords ThetaIteratePosition

local notation "B" =>
  (fun word : List ℕ => List.map (hat word) (List.range' 1 (List.length word)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem second_layer_decomposition (size : ℕ) (hsize : 4 ≤ size) :
  let parameters : Set (List ℕ) := {parameter |
    parameter.Perm (List.range' 1 (size - 2)) ∧
      P parameter ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2]}
  let firstMaximum : Set (List ℕ) := {word |
    word ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2] ∧
      word.getD 0 0 = size}
  let noFinalMaximum : Set (List ℕ) := {word |
    word ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2] ∧
      word.getD (size - 1) 0 ≠ size}
  firstMaximum = insert (size :: List.range' 2 (size - 2) ++ [1]) (P '' parameters) ∧
    firstMaximum.ncard = parameters.ncard + 1 ∧
    noFinalMaximum = insert (List.range' 2 (size - 1) ++ [1]) firstMaximum ∧
    noFinalMaximum.ncard = parameters.ncard + 2 := by
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
  classical
  let parameters : Set (List ℕ) := {parameter |
    parameter.Perm (List.range' 1 (size - 2)) ∧
      P parameter ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2]}
  let firstMaximum : Set (List ℕ) := {word |
    word ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2] ∧ word.getD 0 0 = size}
  let noFinalMaximum : Set (List ℕ) := {word |
    word ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2] ∧
      word.getD (size - 1) 0 ≠ size}
  let shift := List.range' 2 (size - 1) ++ [1]
  let exceptional := size :: List.range' 2 (size - 2) ++ [1]
  have hshiftLength : shift.length = size := by simp [shift]; omega
  have hshiftFirst : shift.getD 0 0 = 2 := by
    rw [List.getD_append _ _ _ _ (by simp; omega)]; rw [List.getD_eq_getElem _ 0 (by simp; omega)]
    simp
  have hshiftLast : shift.getD (size - 1) 0 = 1 := by
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hexceptionalLength : exceptional.length = size := by simp [exceptional]; omega
  have hexceptionalFirst : exceptional.getD 0 0 = size := by simp [exceptional]
  have hexceptionalLast : exceptional.getD (size - 1) 0 = 1 := by
    change (size :: (List.range' 2 (size - 2) ++ [1])).getD (size - 1) 0 = 1
    rw [show size - 1 = (size - 2) + 1 by omega, List.getD_cons_succ]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hchain := ThetaIterateExceptional.cyclic_last_endpoint size (by omega)
  have hexceptionalMember : exceptional ∈
      ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2] := hchain.2.2.1
  have hthetaExceptional : theta exceptional = shift := hchain.2.1
  have hthetaShift : theta shift = size :: List.range' 1 (size - 1) := hchain.1
  have hshiftMember : shift ∈ ThetaIterateDefs.iterateAvoiders size 2 [1, 3, 2] := by
    have hexceptionalPerm : exceptional.Perm (List.range' 1 exceptional.length) := by
      simpa only [hexceptionalLength] using hexceptionalMember.1
    have hshiftPerm := (theta_record_inverse exceptional hexceptionalPerm).2.2.1
    refine ⟨?_, ?_⟩
    · simpa only [hthetaExceptional, hexceptionalLength] using hshiftPerm
    · intro power hpower
      have hcases : power = 0 ∨ power = 1 ∨ power = 2 := by omega
      rcases hcases with rfl | rfl | rfl
      · simpa only [Function.iterate_one, hthetaExceptional, Function.iterate_zero_apply]
          using hexceptionalMember.2 1 (by omega)
      · simpa [Function.iterate_succ_apply', hthetaExceptional]
          using hexceptionalMember.2 2 (by omega)
      · have hreflection := (ThetaIterateUFamilies.U_family size hsize).2.1
        have hthetaTwice : theta (theta shift) = (List.range' 1 size).reverse := by
          rw [hthetaShift]; exact hreflection
        have hreverseAvoid : ¬ Contains [1, 3, 2] [] 3 (List.range' 1 size).reverse := by
          rintro ⟨values, hvalues, _, hsub, _⟩
          change [values 1, values 3, values 2].Sublist (List.range' 1 size).reverse at hsub
          have hdescending : (List.range' 1 size).reverse.Pairwise (fun left right =>
              right < left) := (List.pairwise_lt_range' 1 (by omega : 0 < (1 : ℕ))).reverse
          have hpair := hdescending.sublist hsub
          have hlt : values 3 < values 1 :=
            (List.pairwise_cons.mp hpair).1 (values 3) (by simp)
          have h12 := hvalues 1 (by omega) (by omega)
          have h23 := hvalues 2 (by omega) (by omega)
          change values 1 < values 2 at h12
          change values 2 < values 3 at h23
          omega
        change ¬ Contains [1, 3, 2] [] 3 (theta (theta shift))
        rw [hthetaTwice]; exact hreverseAvoid
  have parameter_length (parameter : List ℕ) (hparameter : parameter ∈ parameters) :
      parameter.length = size - 2 := by simpa using hparameter.1.length_eq
  have hparameterFirst (parameter : List ℕ) (hparameter : parameter ∈ parameters) :
      (P parameter).getD 0 0 = size := by
    have hlength := parameter_length parameter hparameter
    have hperm : parameter.Perm (List.range' 1 parameter.length) := by
      simpa only [hlength] using hparameter.1
    have hfirst :=
      (ThetaIterateCycleReduction.P_cycle_reduction parameter hperm (by omega)).2.2.2.1
    rw [hlength] at hfirst
    convert hfirst using 1 <;> omega
  have hparameterImage (parameter : List ℕ) (hparameter : parameter ∈ parameters) :
      P parameter ∈ firstMaximum := ⟨hparameter.2, hparameterFirst parameter hparameter⟩
  have reconstruct (word : List ℕ) (hword : word ∈ firstMaximum) :
      word = exceptional ∨ word ∈ P '' parameters := by
    have hwordLength : word.length = size := by simpa using hword.1.1.length_eq
    have hwordPerm : word.Perm (List.range' 1 word.length) := by
      simpa only [hwordLength] using hword.1.1
    have hinverse := theta_record_inverse word hwordPerm
    let cycle := theta word
    have hcyclePerm : cycle.Perm (List.range' 1 size) := by
      simpa only [cycle, hwordLength] using hinverse.2.2.1
    have hcycleLength : cycle.length = size := by simpa using hcyclePerm.length_eq
    have hcyclePerm' : cycle.Perm (List.range' 1 cycle.length) := by
      simpa only [hcycleLength] using hcyclePerm
    have hcanonical : B cycle = word := hinverse.2.2.2
    have hcycleLast : cycle.getD (size - 1) 0 = 1 := by
      have hlast := ThetaBasicInverseTail.B_first_max_forces_last_one cycle hcyclePerm'
        (by omega) (by rw [hcanonical, hcycleLength]; exact hword.2)
      simpa only [hcycleLength] using hlast
    have hcycleAvoid : ¬ Contains [1, 3, 2] [] 3 cycle := by
      simpa [cycle] using hword.1.2 1 (by omega)
    have hnextAvoid : ¬ Contains [1, 3, 2] [] 3 (theta cycle) := by
      simpa [cycle, Function.iterate_succ_apply'] using hword.1.2 2 (by omega)
    rcases theta_pair_position cycle hcyclePerm'
      hcycleAvoid hnextAvoid (by omega) with hfirst | hfinal | hshift
    · right
      rw [hcycleLength] at hfirst
      let middle := (cycle.drop 1).take (size - 2)
      have hmiddleLength : middle.length = size - 2 := by simp [middle, hcycleLength]; omega
      have hhead : cycle = size :: cycle.drop 1 := by
        cases hequal : cycle with
        | nil => rw [hequal] at hcycleLength; simp at hcycleLength; omega
        | cons maximum tail => rw [hequal] at hfirst; simpa using hfirst
      have htail : cycle.drop 1 = middle ++ [1] := by
        apply List.ext_getElem (by simp [hcycleLength, hmiddleLength]; omega)
        intro index hindex hother; rw [List.getElem_drop]
        by_cases hin : index < middle.length
        · rw [List.getElem_append_left hin]
          simp [middle, List.getElem_take, Nat.add_comm]
        · rw [List.getElem_append_right (by omega)]
          have hindexLast : index = size - 2 := by
            simp only [List.length_drop, hcycleLength] at hindex; omega
          have hzero : index - middle.length = 0 := by omega
          simp only [hzero, List.getElem_cons_zero]; rw [← List.getD_eq_getElem cycle 0
            (by rw [hcycleLength, hindexLast]; omega : 1 + index < cycle.length)]
          simpa only [show 1 + index = size - 1 by omega] using hcycleLast
      have hsplit : cycle = [size] ++ middle ++ [1] := by rw [hhead, htail]; rfl
      have hrange : List.range' 1 size =
          [1] ++ List.range' 2 (size - 2) ++ [size] := by
        have hcons := List.range'_succ (s := 1) (n := size - 1) (step := 1)
        have hconcat := List.range'_1_concat (s := 2) (n := size - 2)
        have hcons' : List.range' 1 size = 1 :: List.range' 2 (size - 1) := by
          simpa only [show size - 1 + 1 = size by omega] using hcons
        have hconcat' : List.range' 2 (size - 1) =
            List.range' 2 (size - 2) ++ [size] := by
          simpa only [show size - 2 + 1 = size - 1 by omega,
            show 2 + (size - 2) = size by omega] using hconcat
        rw [hcons', hconcat']
        rfl
      have hbase : (List.range' 1 size).Perm
          ([size] ++ List.range' 2 (size - 2) ++ [1]) := by
        rw [hrange]
        apply List.perm_iff_count.mpr
        intro value; simp only [List.count_append, List.count_cons, List.count_nil]; omega
      have hmiddlePerm : middle.Perm (List.range' 2 (size - 2)) := by
        have hequal := hcyclePerm.trans hbase
        rw [hsplit] at hequal; exact (List.perm_append_right_iff [1]).mp
          ((List.perm_append_left_iff [size]).mp
            (by simpa only [List.append_assoc] using hequal))
      let parameter := middle.map (· - 1)
      have hparameterLength : parameter.length = size - 2 := by simp [parameter, hmiddleLength]
      have hparameterPerm : parameter.Perm (List.range' 1 (size - 2)) := by
        have hequal := hmiddlePerm.map (· - 1)
        have hrangeMap : (List.range' 2 (size - 2)).map (· - 1) =
            List.range' 1 (size - 2) := by
          apply List.ext_getElem (by simp)
          intro index hi hj; simp only [List.getElem_map, List.getElem_range'_1]; omega
        simpa only [hrangeMap] using hequal
      have hrestore : parameter.map (· + 1) = middle := by
        dsimp only [parameter]; rw [List.map_map]
        conv_rhs => rw [← List.map_id middle]
        apply List.map_inj_left.mpr
        intro value hvalue
        obtain ⟨offset, hoffset, hequal⟩ :=
          List.mem_range'.mp (hmiddlePerm.mem_iff.mp hvalue)
        simp only [Function.comp_def, id_eq]; omega
      have hP : P parameter = word := by
        unfold P
        rw [hparameterLength, hrestore, show size - 2 + 2 = size by omega]
        change B ((size :: middle) ++ [1]) = word
        rw [show (size :: middle) ++ [1] = cycle by simpa using hsplit.symm]; exact hcanonical
      refine ⟨parameter, ⟨hparameterPerm, ?_⟩, hP⟩
      rw [hP]; exact hword.1
    · rw [hcycleLength] at hfinal
      omega
    · left
      rw [hcycleLength] at hshift
      have hexceptionalPerm : exceptional.Perm (List.range' 1 exceptional.length) := by
        simpa only [hexceptionalLength] using hexceptionalMember.1
      have hBexceptional := (theta_record_inverse exceptional hexceptionalPerm).2.2.2
      have hthetaEq : theta exceptional = cycle := by rw [hthetaExceptional]; exact hshift.symm
      rw [hthetaEq] at hBexceptional; exact hcanonical.symm.trans hBexceptional
  have hexceptionalNotImage : exceptional ∉ P '' parameters := by
    rintro ⟨parameter, hparameter, hequal⟩
    have hlength := parameter_length parameter hparameter
    have hperm : parameter.Perm (List.range' 1 parameter.length) := by
      simpa only [hlength] using hparameter.1
    have htheta := (ThetaIterateCycleReduction.P_cycle_reduction
      parameter hperm (by omega)).1
    rw [hequal, hthetaExceptional] at htheta
    have hfirst := congrArg (fun word : List ℕ => word.getD 0 0) htheta
    rw [hshiftFirst] at hfirst; simp only [List.cons_append, List.getD_cons_zero] at hfirst; omega
  have hfirstSet : firstMaximum = insert exceptional (P '' parameters) := by
    ext word
    constructor
    · intro hword
      exact Set.mem_insert_iff.mpr (reconstruct word hword)
    · intro hword
      rcases Set.mem_insert_iff.mp hword with rfl | ⟨parameter, hparameter, rfl⟩
      · exact ⟨hexceptionalMember, hexceptionalFirst⟩
      · exact hparameterImage parameter hparameter
  have hinjective : Set.InjOn P parameters := by
    intro left hleft right hright hequal
    have hleftLength := parameter_length left hleft
    have hrightLength := parameter_length right hright
    have hleftPerm : left.Perm (List.range' 1 left.length) := by
      simpa only [hleftLength] using hleft.1
    have hrightPerm : right.Perm (List.range' 1 right.length) := by
      simpa only [hrightLength] using hright.1
    have hleftCycle := (ThetaIterateCycleReduction.P_cycle_reduction
      left hleftPerm (by omega)).1
    have hrightCycle := (ThetaIterateCycleReduction.P_cycle_reduction
      right hrightPerm (by omega)).1
    have hcycleEq := congrArg theta hequal
    rw [hleftCycle, hrightCycle, hleftLength, hrightLength] at hcycleEq
    have hmapEq := (List.cons.inj (List.append_cancel_right hcycleEq)).2
    have hinj : Function.Injective (fun value : ℕ => value + 1) := by
      intro first second heq
      change first + 1 = second + 1 at heq
      omega
    exact hinj.list_map hmapEq
  have hfinite : parameters.Finite := by
    have hpermutations : Set.Finite {word : List ℕ |
        word.Perm (List.range' 1 (size - 2))} := by
      convert (List.permutations (List.range' 1 (size - 2))).finite_toSet using 1
      ext word
      exact List.mem_permutations.symm
    exact hpermutations.subset (fun word hword => hword.1)
  have hfirstCount : firstMaximum.ncard = parameters.ncard + 1 := by
    rw [hfirstSet, Set.ncard_insert_of_notMem hexceptionalNotImage (hfinite.image P),
      hinjective.ncard_image]
  have hfirstNotFinal (word : List ℕ) (hword : word ∈ firstMaximum) :
      word.getD (size - 1) 0 ≠ size := by
    have hlength : word.length = size := by simpa using hword.1.1.length_eq
    have hnodup := hword.1.1.nodup_iff.mpr List.nodup_range'
    intro hlast
    have hequal : word.getD 0 0 = word.getD (size - 1) 0 := hword.2.trans hlast.symm
    rw [List.getD_eq_getElem word 0 (by omega : 0 < word.length),
      List.getD_eq_getElem word 0 (by omega : size - 1 < word.length)] at hequal
    have := hnodup.getElem_inj_iff.mp hequal
    omega
  have hshiftNotFirst : shift ∉ firstMaximum := by
    intro hmember
    have hfirst : shift.getD 0 0 = size := hmember.2
    rw [hshiftFirst] at hfirst; omega
  have hnoFinalSet : noFinalMaximum = insert shift firstMaximum := by
    ext word
    constructor
    · intro hword
      have hlength : word.length = size := by simpa using hword.1.1.length_eq
      have hperm : word.Perm (List.range' 1 word.length) := by simpa only [hlength] using hword.1.1
      have havoid : ¬ Contains [1, 3, 2] [] 3 word := by simpa using hword.1.2 0 (by omega)
      have hthetaAvoid : ¬ Contains [1, 3, 2] [] 3 (theta word) := by
        simpa using hword.1.2 1 (by omega)
      rcases theta_pair_position word hperm havoid hthetaAvoid
        (by omega) with hfirst | hlast | hshift
      · exact Set.mem_insert_iff.mpr (Or.inr ⟨hword.1, by simpa only [hlength] using hfirst⟩)
      · exact False.elim (hword.2 (by simpa only [hlength] using hlast))
      · exact Set.mem_insert_iff.mpr (Or.inl (by simpa only [hlength] using hshift))
    · intro hword
      rcases Set.mem_insert_iff.mp hword with rfl | hword
      · exact ⟨hshiftMember, by rw [hshiftLast]; omega⟩
      · exact ⟨hword.1, hfirstNotFinal word hword⟩
  have hfirstFinite : firstMaximum.Finite := by
    rw [hfirstSet]; exact (hfinite.image P).insert exceptional
  have hnoFinalCount : noFinalMaximum.ncard = parameters.ncard + 2 := by
    rw [hnoFinalSet, Set.ncard_insert_of_notMem hshiftNotFirst hfirstFinite, hfirstCount]
  exact ⟨hfirstSet, hfirstCount, hnoFinalSet, hnoFinalCount⟩

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateDecomposition
