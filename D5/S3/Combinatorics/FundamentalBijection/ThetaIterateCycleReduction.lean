/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycleReduction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateCycleReduction
   mirror-E: none(waiver:long-cycle-iterate-reduction)
   anchors: []
   utility: none
   digest: Shifting record cuts and adjoining the outer transposition compute two theta iterates. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycle
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateDefs
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseBlocks
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseGeneral

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycleReduction

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArcherCyclicDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseBlocks
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseGeneral
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycle
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateScan
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords

local notation "B" =>
  (fun p : List ℕ => List.map (hat p) (List.range' 1 (List.length p)))

open D5.S3.Combinatorics.FundamentalBijection
open ThetaBasicInverse ThetaIterateRecords ThetaIteratePosition

set_option maxHeartbeats 1600000 in
theorem P_cycle_reduction (r : List ℕ) (hr : r.Perm (List.range' 1 r.length))
    (hne : 0 < r.length) :
    ThetaFixedDefs.theta (P r) = ((r.length + 2) :: r.map (· + 1)) ++ [1] ∧
      ThetaFixedDefs.theta (ThetaFixedDefs.theta (P r)) =
        (ThetaFixedDefs.theta r).map (· + 1) ++ [r.length + 2, 1] ∧
      ((P r) ∈ ThetaIterateDefs.iterateAvoiders (r.length + 2) 2 [1, 3, 2] ↔
        ¬ Contains [1, 3, 2] [] 3 r ∧
        ¬ Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta r) ∧
        ¬ Contains [1, 3, 2] [] 3 (b r) ∧
        ∀ i j, i < j → j < r.length →
          ¬ ((b r).getD i 0 < r.getD 0 0 + 1 ∧
            r.getD 0 0 + 1 < (b r).getD j 0)) ∧
    (P r).getD 0 0 = r.length + 2 ∧
      (P r).getD (r.length + 1) 0 = r.getD 0 0 + 1 ∧
      ∀ x ∈ r, (P r).getD x 0 =
        if r.idxOf x + 1 < r.length then
          r.getD (r.idxOf x + 1) 0 + 1 else 1 := by
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
  have P_images (r : List ℕ)
      (hr : r.Perm (List.range' 1 r.length)) (hne : 0 < r.length) :
      (P r).getD 0 0 = r.length + 2 ∧
        (P r).getD (r.length + 1) 0 = r.getD 0 0 + 1 ∧
        ∀ x ∈ r, (P r).getD x 0 =
          if r.idxOf x + 1 < r.length then
            r.getD (r.idxOf x + 1) 0 + 1 else 1 := by
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
    let h := r.length
    let N := h + 2
    let q := (N :: r.map (· + 1)) ++ [1]
    have hlen : q.length = N := by simp [q, N, h]
    have hfirst : q.getD 0 0 = N := by simp [q]
    have hlast : q.getD (N - 1) 0 = 1 := by
      have hq : q = (N :: r.map (· + 1)) ++ [1] := rfl
      rw [hq, List.getD_append_right _ [1] 0 (N - 1) (by simp [N, h])]; simp [N, h]
    have hmax : ∀ y ∈ q, y ≤ q.getD 0 0 := by
      intro y hy; rw [hfirst]
      rcases List.mem_append.mp hy with hy | hy
      · rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
          obtain ⟨i, hi, hxi⟩ := List.mem_range'.mp (hr.mem_iff.mp hx)
          dsimp [N, h]; omega
      · simp only [List.mem_singleton] at hy
        subst y
        omega
    have hnodup : q.Nodup := by
      have hrnd : r.Nodup := hr.nodup_iff.mpr List.nodup_range'
      have hmapnd : (r.map (· + 1)).Nodup :=
        hrnd.map (by intro x y heq; dsimp at heq; omega)
      have hcons : (N :: r.map (· + 1)).Nodup := by
        apply List.nodup_cons.mpr
        constructor
        · intro hm
          obtain ⟨x, hx, heq⟩ := List.mem_map.mp hm
          obtain ⟨i, hi, hxi⟩ := List.mem_range'.mp (hr.mem_iff.mp hx)
          dsimp [N, h] at heq; omega
        · exact hmapnd
      apply List.nodup_append.mpr
      refine ⟨hcons, by simp, ?_⟩
      intro a ha b hb
      have hb1 : b = 1 := by simpa using hb
      subst b
      rcases List.mem_cons.mp ha with rfl | ha
      · dsimp [N, h]
        omega
      · obtain ⟨x, hx, heq⟩ := List.mem_map.mp ha
        obtain ⟨i, hi, hxi⟩ := List.mem_range'.mp (hr.mem_iff.mp hx)
        omega
    have hidx1 : q.idxOf 1 = N - 1 := by
      have hidx := (List.get_idxOf hnodup ⟨N - 1, by omega⟩)
      have hval : q[N - 1] = 1 := by
        simpa only [← List.getD_eq_getElem _ 0 (by omega : N - 1 < q.length)]
          using hlast
      change q.idxOf q[N - 1] = N - 1 at hidx
      rw [hval] at hidx; exact hidx
    have hidxN : q.idxOf N = 0 := by
      have hidx := (List.get_idxOf hnodup ⟨0, by omega⟩)
      have hval : q[0] = N := by
        simpa only [← List.getD_eq_getElem _ 0 (by omega : 0 < q.length)]
          using hfirst
      change q.idxOf q[0] = 0 at hidx
      rw [hval] at hidx; exact hidx
    have h1mem : 1 ∈ q := by
      apply List.mem_iff_getElem.mpr
      exact ⟨N - 1, by omega, by
        simpa only [← List.getD_eq_getElem _ 0 (by omega : N - 1 < q.length)]
          using hlast⟩
    have hNmem : N ∈ q := by simp [q]
    have hhat1 := hat_one_block q hmax 1 h1mem
    have hhatN := hat_one_block q hmax N hNmem
    have hnext : q.getD 1 0 = r.getD 0 0 + 1 := by
      have h0 : 0 < (r.map (· + 1)).length := by simp [hne]
      simp [q, hne]
    constructor
    · change hat q 1 = N
      rw [hhat1, hidx1, if_neg (by omega)]; exact hfirst
    constructor
    · have hpget : (P r).getD (r.length + 1) 0 = hat q N := by
        simp [P, q, N, h]
        congr 1
        omega
      rw [hpget]; rw [hhatN, hidxN, if_pos (by omega)]; exact hnext
    · intro x hx
      let i := r.idxOf x
      have hi : i < h := List.idxOf_lt_length_of_mem hx
      have hxval : r.getD i 0 = x := by
        rw [List.getD_eq_getElem _ 0 hi]; exact List.getElem_idxOf hi
      have hxbound : x ≤ h := by
        obtain ⟨j, hj, heq⟩ := List.mem_range'.mp (hr.mem_iff.mp hx)
        omega
      have hpget : (P r).getD x 0 = hat q (x + 1) := by
        change (B q).getD x 0 = hat q (x + 1)
        rw [List.getD_eq_getElem _ 0 (by simp [hlen]; omega)]; simp [hlen, Nat.add_comm]
      have hqval : q.getD (i + 1) 0 = x + 1 := by
        change (N :: (r.map (· + 1) ++ [1])).getD (i + 1) 0 = x + 1
        rw [List.getD_cons_succ,
          List.getD_append _ _ _ _ (by simpa [h] using hi),
          List.getD_eq_getElem _ 0 (by simpa [h] using hi), List.getElem_map]
        simpa only [← List.getD_eq_getElem _ 0 hi] using congrArg (· + 1) hxval
      have hidx : q.idxOf (x + 1) = i + 1 := by
        have hqidx := (List.get_idxOf hnodup ⟨i + 1, by omega⟩)
        have hqelem : q[i + 1] = x + 1 := by
          simpa only [← List.getD_eq_getElem _ 0 (by omega : i + 1 < q.length)]
            using hqval
        change q.idxOf q[i + 1] = i + 1 at hqidx
        rw [hqelem] at hqidx; exact hqidx
      have hxmem : x + 1 ∈ q := by
        apply List.mem_iff_getElem.mpr
        exact ⟨i + 1, by omega, by
          simpa only [← List.getD_eq_getElem _ 0 (by omega : i + 1 < q.length)]
            using hqval⟩
      have hhat := hat_one_block q hmax (x + 1) hxmem
      rw [hpget, hhat, hidx, if_pos (by omega)]
      by_cases hstep : i + 1 < h
      · have hqnext : q.getD (i + 2) 0 = r.getD (i + 1) 0 + 1 := by
          change (N :: (r.map (· + 1) ++ [1])).getD (i + 2) 0 =
            r.getD (i + 1) 0 + 1
          rw [show i + 2 = (i + 1) + 1 by omega, List.getD_cons_succ,
            List.getD_append _ _ _ _ (by simpa [h] using hstep),
            List.getD_eq_getElem _ 0 (by simpa [h] using hstep), List.getElem_map]
          simp only [← List.getD_eq_getElem _ 0 hstep]
        rw [hqnext, if_pos (by simpa [i, h] using hstep)]
      · have hieq : i + 1 = h := by omega
        have hqnext : q.getD (i + 2) 0 = 1 := by
          have hindex : i + 2 = N - 1 := by dsimp [N]; omega
          rw [hindex]; exact hlast
        rw [hqnext, if_neg (by simpa [i, h] using hstep)]
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

  let h := r.length
  let N := h + 2
  let q := ThetaFixedDefs.theta r
  let first := (N :: r.map (· + 1)) ++ [1]
  let second := q.map (· + 1) ++ [N, 1]
  have hinv := theta_record_inverse r hr
  have hqperm : q.Perm (List.range' 1 h) := hinv.2.2.1
  have hBq : B q = r := hinv.2.2.2
  have hqlen : q.length = h := by simpa using hqperm.length_eq
  have hmaprange : (List.range' 1 h).map (· + 1) = List.range' 2 h := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_map, List.getElem_range'_1]; omega
  have hwordperm (w : List ℕ) (hw : w.Perm (List.range' 1 h)) :
      ((N :: w.map (· + 1)) ++ [1]).Perm (List.range' 1 N) := by
    have hshift : (w.map (· + 1)).Perm (List.range' 2 h) := by
      have heq := hw.map (fun x : ℕ => x + 1)
      rw [hmaprange] at heq; exact heq
    have hbase := (hshift.cons N).append (List.Perm.refl [1])
    have hswap : (([N] ++ List.range' 2 h) ++ [1]).Perm
        ([1] ++ ([N] ++ List.range' 2 h)) := List.perm_append_comm
    have hswap' : ([1] ++ ([N] ++ List.range' 2 h)).Perm
        ([1] ++ (List.range' 2 h ++ [N])) :=
      (List.Perm.refl [1]).append List.perm_append_comm
    have hsorted := hswap.trans hswap'
    have hrange : List.range' 1 N = 1 :: (List.range' 2 h ++ [N]) := by
      have heq := List.range'_concat (s := 2) (n := h) (step := 1)
      have hcons := List.range'_succ (s := 1) (n := h + 1) (step := 1)
      simpa only [Nat.one_mul, show 1 + 1 = 2 from rfl, N, Nat.add_comm h 2]
        using hcons.trans (congrArg (List.cons 1) heq)
    rw [hrange]
    apply hbase.trans
    simpa only [List.singleton_append, List.append_assoc] using hsorted
  have hfirstperm : first.Perm (List.range' 1 first.length) := by
    have heq : first.length = N := by simp [first, N, h]
    rw [heq]; exact hwordperm r hr
  have hsecondlen : second.length = N := by simp [second, N, hqlen]
  have hsecondperm : second.Perm (List.range' 1 second.length) := by
    rw [hsecondlen]
    have hbase := hwordperm q hqperm
    have hmove : ([N] ++ (q.map (· + 1) ++ [1])).Perm
        ((q.map (· + 1) ++ [N]) ++ [1]) := by
      simpa only [List.append_assoc] using
        ((List.perm_append_comm (l₁ := [N]) (l₂ := q.map (· + 1))).append
          (List.Perm.refl [1]))
    have heq := hmove.symm.trans (by
      simpa only [List.singleton_append, List.append_assoc, List.cons_append,
        List.nil_append] using hbase)
    simpa only [second, List.append_assoc, List.singleton_append] using heq
  have hsecondnd : second.Nodup := hsecondperm.nodup_iff.mpr List.nodup_range'
  have hget (i : ℕ) (hi : i < h) : second.getD i 0 = q.getD i 0 + 1 := by
    rw [List.getD_append _ _ _ _ (by simp; omega),
      List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_map,
      List.getD_eq_getElem _ 0 (by omega)]
  have hgetN : second.getD h 0 = N := by
    rw [List.getD_append_right _ _ 0 h (by simp; omega)]; simp [hqlen]
  have hgetOne : second.getD (h + 1) 0 = 1 := by
    rw [List.getD_append_right _ _ 0 (h + 1) (by simp; omega)]; simp [hqlen]
  have hqbounds (i : ℕ) (hi : i < h) : 1 ≤ q.getD i 0 ∧ q.getD i 0 ≤ h := by
    have hm : q.getD i 0 ∈ q := by
      rw [List.getD_eq_getElem _ 0 (by omega)]; exact List.getElem_mem (by omega)
    obtain ⟨j, hj, heq⟩ := List.mem_range'.mp (hqperm.mem_iff.mp hm)
    omega
  have hrec (i : ℕ) (hi : i < h) : IsLtrMax second i ↔ IsLtrMax q i := by
    constructor
    · intro hr j hji
      have heq := hr j hji
      rw [hget j (by omega), hget i hi] at heq; omega
    · intro hr j hji
      rw [hget j (by omega), hget i hi]
      have heq := hr j hji
      omega
  have hrecN : IsLtrMax second h := by
    intro i hi; rw [hget i hi, hgetN]
    have := hqbounds i hi
    dsimp [N]; omega
  have hidxmap (w : List ℕ) (x : ℕ) :
      (w.map (· + 1)).idxOf (x + 1) = w.idxOf x := by
    induction w with
    | nil => simp
    | cons a w ih =>
        by_cases ha : a = x
        · subst a
          simp
        · simp [ha, ih]
  have hshift (x : ℕ) (hx : x ∈ q) : hat second (x + 1) = hat q x + 1 := by
    let i := q.idxOf x
    have hi : i < h := by simpa [i, hqlen] using List.idxOf_lt_length_of_mem hx
    have hidx : second.idxOf (x + 1) = i := by
      change (q.map (· + 1) ++ [N, 1]).idxOf (x + 1) = i
      have hm : x + 1 ∈ q.map (fun y : ℕ => y + 1) := List.mem_map.mpr ⟨x, hx, rfl⟩
      rw [List.idxOf_append_of_mem hm, hidxmap]
    have hgreatest (j : ℕ) (hj : j < h) :
        Nat.findGreatest (IsLtrMax second) j = Nat.findGreatest (IsLtrMax q) j := by
      induction j with
      | zero => simp
      | succ j ih =>
          rw [Nat.findGreatest_succ, Nat.findGreatest_succ]
          have hjprev : j < h := by omega
          by_cases hr : IsLtrMax q (j + 1)
          · rw [if_pos ((hrec _ hj).2 hr), if_pos hr]
          · rw [if_neg (fun hs => hr ((hrec _ hj).1 hs)), if_neg hr, ih hjprev]
    have hcase : (i + 1 < second.length ∧ ¬ IsLtrMax second (i + 1)) ↔
        (i + 1 < q.length ∧ ¬ IsLtrMax q (i + 1)) := by
      constructor
      · rintro ⟨hn, hnon⟩
        have hlt : i + 1 < h := by
          by_contra hnot
          have heq : i + 1 = h := by omega
          exact hnon (heq ▸ hrecN)
        exact ⟨by omega, fun hr => hnon ((hrec _ hlt).2 hr)⟩
      · rintro ⟨hn, hnon⟩
        exact ⟨by omega, fun hr => hnon ((hrec _ (by omega)).1 hr)⟩
    unfold hat
    dsimp only; rw [hidx]
    by_cases hn : i + 1 < q.length ∧ ¬ IsLtrMax q (i + 1)
    · rw [if_pos (hcase.2 hn), if_pos hn]
      exact hget _ (by omega)
    · rw [if_neg (fun hs => hn (hcase.1 hs)), if_neg hn, hgreatest i hi]
      exact hget _ (lt_of_le_of_lt (Nat.findGreatest_le _) hi)
  have hidx (i : ℕ) (hi : i < second.length) :
      second.idxOf (second.getD i 0) = i := by
    rw [List.getD_eq_getElem _ 0 hi]; simpa using List.get_idxOf hsecondnd ⟨i, hi⟩
  have hhatOne : hat second 1 = N := by
    have hid : second.idxOf 1 = h + 1 := by
      have heq := hidx (h + 1) (by omega)
      rwa [hgetOne] at heq
    unfold hat
    rw [hid, if_neg (by omega : ¬ (h + 1 + 1 < second.length ∧ _))]
    have hgreatest : Nat.findGreatest (IsLtrMax second) (h + 1) = h := by
      apply Nat.findGreatest_eq_iff.mpr
      refine ⟨by omega, fun _ => hrecN, ?_⟩
      intro j hhj hj hrecj
      have heq : j = h + 1 := by omega
      have hlt := hrecj h hhj
      rw [heq, hgetOne, hgetN] at hlt
      dsimp [N] at hlt; omega
    rw [hgreatest, hgetN]
  have hhatN : hat second N = 1 := by
    have hid : second.idxOf N = h := by
      have heq := hidx h (by omega)
      rwa [hgetN] at heq
    have hnon : ¬ IsLtrMax second (h + 1) := by
      intro hr
      have hlt := hr h (by omega)
      rw [hgetN, hgetOne] at hlt
      dsimp [N] at hlt; omega
    unfold hat
    rw [hid, if_pos ⟨by omega, hnon⟩, hgetOne]
  have hBsecond : B second = first := by
    apply List.ext_getElem
    · simp [first, N, h, hsecondlen]
    · intro i hi₁ hi₂
      have hi : i < N := by simpa [hsecondlen] using hi₁
      simp only [List.getElem_map, List.getElem_range'_1]; rw [← List.getD_eq_getElem _ 0 hi₂]
      by_cases hzero : i = 0
      · subst i
        simpa only [first, Nat.add_zero, List.getD_append _ _ _ _ (by simp :
          0 < (N :: r.map (· + 1)).length), List.getD_cons_zero] using hhatOne
      · by_cases hfinal : i = h + 1
        · subst i
          rw [show 1 + (h + 1) = N by dsimp [N]; omega, hhatN]
          rw [List.getD_append_right _ _ 0 (h + 1) (by simp [h])]; simp [h]
        · have hir : i - 1 < h := by omega
          have hxmem : i ∈ q := hqperm.mem_iff.mpr
            (List.mem_range'.mpr ⟨i - 1, by omega, by omega⟩)
          have hhatq : hat q i = r.getD (i - 1) 0 := by
            have heq := congrArg (fun w : List ℕ => w.getD (i - 1) 0) hBq
            rw [List.getD_eq_getElem _ 0 (by simp; omega)] at heq
            simp only [List.getElem_map, List.getElem_range'_1] at heq
            rwa [show 1 + (i - 1) = i by omega] at heq
          rw [show 1 + i = i + 1 by omega, hshift i hxmem, hhatq]
          change _ = ((N :: r.map (· + 1)) ++ [1]).getD i 0
          rw [List.getD_append _ _ _ _ (by simp; omega)]
          have hisucc : i = (i - 1) + 1 := by omega
          rw [hisucc, List.getD_cons_succ]; simp only [Nat.add_sub_cancel]
          have heq : (r.map (· + 1)).getD (i - 1) 0 = r.getD (i - 1) 0 + 1 := by
            rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_map,
              List.getD_eq_getElem _ 0 (by omega)]
          exact heq.symm
  have hfirsttheta : ThetaFixedDefs.theta (P r) = first := by exact hinv.1 first hfirstperm
  have hsecondtheta : ThetaFixedDefs.theta (ThetaFixedDefs.theta (P r)) = second := by
    rw [hfirsttheta, ← hBsecond]; exact hinv.1 second hsecondperm
  have hshiftavoid (w : List ℕ) :
      (¬ Contains [1, 3, 2] [] 3 (w.map (· + 1))) ↔
        ¬ Contains [1, 3, 2] [] 3 w := by
    have heq : Contains [1, 3, 2] [] 3 (w.map (· + 1)) ↔
        Contains [1, 3, 2] [] 3 w := by
      rw [contains132_iff_indices, contains132_iff_indices]; simp only [List.getElem_map]
      constructor
      · rintro ⟨i, j, k, hij, hjk, hik, hkj⟩
        refine ⟨⟨i.val, by simpa only [List.length_map] using i.isLt⟩,
          ⟨j.val, by simpa only [List.length_map] using j.isLt⟩,
          ⟨k.val, by simpa only [List.length_map] using k.isLt⟩, hij, hjk, ?_, ?_⟩
        · change w[i.val] < w[k.val]
          omega
        · change w[k.val] < w[j.val]
          omega
      · rintro ⟨i, j, k, hij, hjk, hik, hkj⟩
        refine ⟨⟨i.val, by simpa only [List.length_map] using i.isLt⟩,
          ⟨j.val, by simpa only [List.length_map] using j.isLt⟩,
          ⟨k.val, by simpa only [List.length_map] using k.isLt⟩, hij, hjk, ?_, ?_⟩
        · change w[i.val] + 1 < w[k.val] + 1
          omega
        · change w[k.val] + 1 < w[j.val] + 1
          omega
    exact not_congr heq
  have hbounds (w : List ℕ) (hw : w.Perm (List.range' 1 h)) (x : ℕ) (hx : x ∈ w) :
      1 ≤ x ∧ x ≤ h := by
    obtain ⟨i, hi, heq⟩ := List.mem_range'.mp (hw.mem_iff.mp hx)
    omega
  have hshiftbounds (w : List ℕ) (hw : w.Perm (List.range' 1 h)) (x : ℕ)
      (hx : x ∈ w.map (· + 1)) : 1 ≤ x ∧ x < N := by
    obtain ⟨y, hy, heq⟩ := List.mem_map.mp hx
    have hb := hbounds w hw y hy
    dsimp [N]; omega
  have hnoone (w : List ℕ) (hpos : ∀ x ∈ w, 1 ≤ x) :
      ∀ i j, i < j → j < w.length → ¬ (w.getD i 0 < 1 ∧ 1 < w.getD j 0) := by
    intro i j hij hj hcross
    have hi : i < w.length := by omega
    have hmem : w.getD i 0 ∈ w := by rw [List.getD_eq_getElem _ 0 hi]; exact List.getElem_mem hi
    have := hpos _ hmem
    omega
  have hfirsttest : (¬ Contains [1, 3, 2] [] 3 first) ↔
      ¬ Contains [1, 3, 2] [] 3 r := by
    have htop : ∀ x ∈ r.map (· + 1) ++ [1], x < N := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (hshiftbounds r hr x hx).2
      · have heq : x = 1 := by simpa using hx
        dsimp [N]; omega
    have htest := avoids132_cons_max_append_iff (r.map (· + 1)) 1 N htop
    change (¬ Contains [1, 3, 2] [] 3 (N :: (r.map (· + 1) ++ [1]))) ↔ _
    rw [htest]
    constructor
    · intro hav
      exact (hshiftavoid r).1 hav.1
    · intro hav
      exact ⟨(hshiftavoid r).2 hav,
        hnoone _ (fun x hx => (hshiftbounds r hr x hx).1)⟩
  have hsecondtest : (¬ Contains [1, 3, 2] [] 3 second) ↔
      ¬ Contains [1, 3, 2] [] 3 q := by
    have htop : ∀ i j, i < j → j < (q.map (· + 1)).length →
        ¬ ((q.map (· + 1)).getD i 0 < N ∧ N < (q.map (· + 1)).getD j 0) := by
      intro i j hij hj hcross
      have hm : (q.map (· + 1)).getD j 0 ∈ q.map (· + 1) := by
        rw [List.getD_eq_getElem _ 0 hj]; exact List.getElem_mem hj
      have hb := hshiftbounds q hqperm _ hm
      omega
    have hpos : ∀ x ∈ q.map (· + 1) ++ [N], 1 ≤ x := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (hshiftbounds q hqperm x hx).1
      · have heq : x = N := by simpa using hx
        dsimp [N] at heq; omega
    have htestN := avoids132_append_iff (q.map (· + 1)) N
    have htestOne := avoids132_append_iff (q.map (· + 1) ++ [N]) 1
    change (¬ Contains [1, 3, 2] [] 3 (q.map (· + 1) ++ [N, 1])) ↔ _
    rw [show q.map (· + 1) ++ [N, 1] = (q.map (· + 1) ++ [N]) ++ [1] by
      simp only [List.append_assoc]; rfl, htestOne]
    constructor
    · intro hav
      exact (hshiftavoid q).1 (htestN.1 hav.1).1
    · intro hav
      exact ⟨htestN.2 ⟨(hshiftavoid q).2 hav, htop⟩, hnoone _ hpos⟩
  have hPword : P r = N :: (b r ++ [r.getD 0 0 + 1]) := by
    have himages := P_images r hr hne
    have hblen : (b r).length = h := by simp [b, h]
    apply List.ext_getElem
    · simp [P, hblen, N, h]
    · intro i hi₁ hi₂
      have hPlen : (P r).length = h + 2 := by simp [P, h]
      have hi : i < h + 2 := by omega
      rw [← List.getD_eq_getElem _ 0 hi₁, ← List.getD_eq_getElem _ 0 hi₂]
      by_cases hzero : i = 0
      · subst i
        simpa only [List.getD_cons_zero] using himages.1
      · have hisucc : i = (i - 1) + 1 := by omega
        rw [hisucc, List.getD_cons_succ]
        by_cases hfinal : i - 1 = h
        · have hindex : i - 1 + 1 = h + 1 := by omega
          rw [hindex]; rw [show h + 1 = r.length + 1 from rfl, himages.2.1]
          rw [List.getD_append_right _ _ 0 (i - 1) (by omega)]
          have hz : i - 1 - (b r).length = 0 := by omega
          simp [hz]
        · have hilt : i - 1 < h := by omega
          rw [List.getD_append _ _ _ _ (by omega)]
          have hxmem : i - 1 + 1 ∈ r := hr.mem_iff.mpr
            (List.mem_range'.mpr ⟨i - 1, by omega, by omega⟩)
          rw [himages.2.2 _ hxmem]
          have hbget : (b r).getD (i - 1) 0 =
              if r.idxOf (i - 1 + 1) + 1 < r.length then
                r.getD (r.idxOf (i - 1 + 1) + 1) 0 + 1 else 1 := by
            rw [List.getD_eq_getElem _ 0 (by omega)]
            simp only [b, List.getElem_map, List.getElem_range'_1]
            rw [show 1 + (i - 1) = i - 1 + 1 by omega]
          exact hbget.symm
  have hPtop : ∀ x ∈ b r ++ [r.getD 0 0 + 1], x < N := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, heq⟩ := List.mem_map.mp hx
      by_cases hnext : r.idxOf y + 1 < h
      · rw [if_pos hnext] at heq
        have hm : r.getD (r.idxOf y + 1) 0 ∈ r := by
          rw [List.getD_eq_getElem _ 0 hnext]; exact List.getElem_mem hnext
        have hb := hbounds r hr _ hm
        dsimp [N]; omega
      · rw [if_neg hnext] at heq
        dsimp [N]; omega
    · have heq : x = r.getD 0 0 + 1 := by simpa using hx
      have hm : r.getD 0 0 ∈ r := by rw [List.getD_eq_getElem _ 0 hne]; exact List.getElem_mem hne
      have hb := hbounds r hr _ hm
      dsimp [N]; omega
  have hPtest := avoids132_cons_max_append_iff (b r) (r.getD 0 0 + 1) N hPtop
  have hPperm : (P r).Perm (List.range' 1 N) := by
    have heq := hinv.2.1 first hfirstperm
    have hfirstlen : first.length = N := by simp [first, N, h]
    rw [hfirstlen] at heq; exact heq
  refine ⟨hfirsttheta, hsecondtheta, ?_, P_images r hr hne⟩
  change ((P r).Perm (List.range' 1 N) ∧
    ∀ i ≤ 2, ¬ Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta^[i] (P r))) ↔ _
  constructor
  · rintro ⟨_, hav⟩
    have hav0 := hav 0 (by omega)
    have hav1 := hav 1 (by omega)
    have hav2 := hav 2 (by omega)
    simp only [Function.iterate_zero, id_eq] at hav0
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq,
      hfirsttheta] at hav1
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq,
      hsecondtheta] at hav2
    rw [hPword] at hav0
    have hpair := hPtest.1 hav0
    exact ⟨hfirsttest.1 hav1, hsecondtest.1 hav2, hpair.1, by
      simpa only [b, List.length_map, List.length_range'] using hpair.2⟩
  · rintro ⟨hrav, hqav, hbav, hpair⟩
    refine ⟨hPperm, ?_⟩
    intro i hi
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp only [Function.iterate_zero, id_eq]
      rw [hPword]
      apply hPtest.2
      exact ⟨hbav, by simpa only [b, List.length_map, List.length_range'] using hpair⟩
    · simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq, hfirsttheta]
      exact hfirsttest.2 hrav
    · simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq, hsecondtheta]
      exact hsecondtest.2 hqav

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycleReduction
