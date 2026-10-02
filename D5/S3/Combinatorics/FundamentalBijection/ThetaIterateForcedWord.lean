/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateForcedWord
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateForcedWord
   mirror-E: none(waiver:forced-first-endpoint-family)
   anchors: []
   utility: none
   digest: First-endpoint avoiders have increasing, descending, or one-cycle insertion shape. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycleScan
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateShortCycle
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateUFamilies
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateInsertion
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateInsertionInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateForcedWord

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArcherCyclicDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycle
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateHighScan
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycleScan
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateShortCycle

local notation "B" =>
  (fun p : List ℕ => List.map (hat p) (List.range' 1 (List.length p)))

def W (h : ℕ) : List ℕ :=
  (List.range' ((h + 1) / 2 + 1) (h - (h + 1) / 2)).reverse ++
    (List.range' 1 ((h + 1) / 2 - 1)).reverse ++ [(h + 1) / 2]

theorem first_endpoint_classification (r : List ℕ) (v : ℕ)
    (hr : r.Perm (List.range' 1 r.length)) (hsize : 4 ≤ r.length)
    (hfirst : r.getD 0 0 = r.length)
    (hlast : r.getD (r.length - 1) 0 = v)
    (hravoid : ¬ Contains [1, 3, 2] [] 3 r)
    (hbavoid : ¬ Contains [1, 3, 2] [] 3 (b r))
    (hθavoid : ¬ Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta r)) :
    r = ThetaIterateUFamilies.U r.length ∨ r = (List.range' 1 r.length).reverse ∨
      (r.getD 1 0 = r.length - 1 ∧ r.getD (r.length - 2) 0 = 1 ∧
        2 ≤ v ∧ v ≤ r.length - 2 ∧
        ThetaFixedDefs.cycleFrom r r.length = ThetaFixedDefs.theta r ∧
        (v < r.length - 2 → r = W r.length) ∧
        (v = r.length - 2 → 5 ≤ r.length →
          ∃! seed : List ℕ, seed.Perm (List.range' 1 (r.length - 3)) ∧
            seed.getD 0 0 = r.length - 3 ∧ ThetaIterateInsertion.I seed = r ∧
            P seed ∈ ThetaIterateDefs.iterateAvoiders (r.length - 1) 2 [1, 3, 2] ∧
            ThetaFixedDefs.cycleFrom seed seed.length = ThetaFixedDefs.theta seed)) := by
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

  by_cases hsmallsecond : r.getD 1 0 ≤ r.length - 2
  · left
    have hmember : P r ∈ ThetaIterateDefs.iterateAvoiders
        (r.length + 2) 2 [1, 3, 2] := by
      apply (ThetaIterateCycleReduction.P_cycle_reduction r hr (by omega)).2.2.1.mpr
      refine ⟨hravoid, hθavoid, hbavoid, ?_⟩
      intro i j hij hj hcross
      have hbperm := b_perm_of_first_max r hr hfirst
      have hmem : (b r).getD j 0 ∈ b r := by
        rw [List.getD_eq_getElem _ 0 (by simp [b]; omega)]
        exact List.getElem_mem (by simp [b]; omega)
      obtain ⟨offset, hoffset, heq⟩ := List.mem_range'.mp (hbperm.mem_iff.mp hmem)
      rw [hfirst] at hcross
      omega
    exact ((ThetaIterateUFamilies.U_family r.length hsize).2.2.2.1
      r hr hfirst hsmallsecond).mp hmember
  by_cases hlastone : v = 1
  · right
    left
    exact ThetaIterateFirstEndpoint.descending_of_last_one_and_b_avoids
      r hr (by omega) hfirst (hlast.trans hlastone) hbavoid
  have hrnodup : r.Nodup := hr.nodup_iff.mpr List.nodup_range'
  have hentrybounds (index : ℕ) (hindex : index < r.length) :
      1 ≤ r.getD index 0 ∧ r.getD index 0 ≤ r.length := by
    have hmem : r.getD index 0 ∈ r := by
      rw [List.getD_eq_getElem _ 0 hindex]
      exact List.getElem_mem hindex
    obtain ⟨offset, hoffset, heq⟩ := List.mem_range'.mp (hr.mem_iff.mp hmem)
    omega
  have hindexeq (index other : ℕ) (hindex : index < r.length)
      (hother : other < r.length) (heq : r.getD index 0 = r.getD other 0) :
      index = other := by
    rw [List.getD_eq_getElem _ 0 hindex, List.getD_eq_getElem _ 0 hother] at heq
    exact hrnodup.getElem_inj_iff.mp heq
  have hsecond : r.getD 1 0 = r.length - 1 := by
    have hbound := hentrybounds 1 (by omega)
    have hne : r.getD 1 0 ≠ r.length := by
      intro heq
      have := hindexeq 1 0 (by omega) (by omega) (heq.trans hfirst.symm)
      omega
    omega
  have hv : 2 ≤ v := by
    have hbound := hentrybounds (r.length - 1) (by omega)
    omega
  have hvbound : v ≤ r.length - 2 := by
    have hbound := hentrybounds (r.length - 1) (by omega)
    have hnemax : v ≠ r.length := by
      intro heq
      have := hindexeq (r.length - 1) 0 (by omega) (by omega)
        (hlast.trans (heq.trans hfirst.symm))
      omega
    have hnepen : v ≠ r.length - 1 := by
      intro heq
      have := hindexeq (r.length - 1) 1 (by omega) (by omega)
        (hlast.trans (heq.trans hsecond.symm))
      omega
    omega
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
  let h := r.length
  let q := ThetaFixedDefs.theta r
  have hθ : q.Perm (List.range' 1 h) ∧ B q = r := by
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
          intro j hsj hje hr
          have hjQ : Q j := ⟨hsj, by omega, Or.inr hr⟩
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
    obtain ⟨w, hw⟩ := (Finite.surjective_of_injective hinjective) (⟨r, hr⟩ : Words)
    have hB : B w.val = r := congrArg Subtype.val hw
    have htheta : q = w.val := by
      dsimp [q]
      rw [← hB]
      exact hleft w.val (hvalid w)
    exact ⟨by simpa [htheta] using w.property, by rw [htheta]; exact hB⟩
  have hlen : q.length = r.length := by simpa [h] using hθ.1.length_eq
  have hq : q.Perm (List.range' 1 q.length) := by simpa [hlen, h] using hθ.1
  have hmap (x : ℕ) (hx : 1 ≤ x) (hxh : x ≤ r.length) : hat q x = image r x := by
    have heq := congrArg (fun w : List ℕ => w.getD (x - 1) 0) hθ.2
    change (B q).getD (x - 1) 0 = image r x at heq
    rw [List.getD_eq_getElem _ 0 (by simp; omega)] at heq
    simp only [List.getElem_map, List.getElem_range'_1] at heq
    rwa [show 1 + (x - 1) = x by omega] at heq
  have hqavoid : ¬ Contains [1, 3, 2] [] 3 q := hθavoid
  have hshape := second_to_penultimate_forces_one_block q hq (by omega) hqavoid
    (by rw [hmap 1 (by omega) (by omega)]; simpa [image, hlen] using hfirst)
    (by rw [hmap 2 (by omega) (by omega)]; simpa [image, hlen] using hsecond)
    (by
      rw [hmap q.length (by omega) (by omega)]
      change 1 < r.getD (q.length - 1) 0
      rw [hlen, hlast]
      omega)
  have hcycle : q.getD 0 0 = r.length := hshape.2.trans hlen
  have hpenult : r.getD (r.length - 2) 0 = 1 := by
    have heq := hshape.1
    rw [hmap (q.length - 1) (by omega) (by omega)] at heq
    change r.getD (q.length - 1 - 1) 0 = 1 at heq
    rwa [show q.length - 1 - 1 = r.length - 2 by omega] at heq
  have hwholecycle : ThetaFixedDefs.cycleFrom r r.length = q := by
    have hrecord : IsLtrMax q 0 := by intro index hindex; omega
    have hnonrecord (index : ℕ) (hpositive : 0 < index) (hindex : index < q.length) :
        ¬ IsLtrMax q index := by
      intro hrecord
      have hlt := hrecord 0 hpositive
      have hmem : q.getD index 0 ∈ q := by
        rw [List.getD_eq_getElem _ 0 hindex]
        exact List.getElem_mem hindex
      obtain ⟨offset, hoffset, heq⟩ := List.mem_range'.mp (hq.mem_iff.mp hmem)
      omega
    have heq := ThetaBasicInverseBlocks.cycleFrom_B_record_block q hq 0 q.length
      (by omega) (le_refl _) hrecord hnonrecord (Or.inl rfl)
    simpa only [hθ.2, hcycle, List.drop_zero, Nat.sub_zero, List.take_length] using heq
  have hinsertion (heq : v = r.length - 2) (hlarge : 5 ≤ r.length) :
      ∃! seed : List ℕ, seed.Perm (List.range' 1 (r.length - 3)) ∧
        seed.getD 0 0 = r.length - 3 ∧ ThetaIterateInsertion.I seed = r ∧
        P seed ∈ ThetaIterateDefs.iterateAvoiders (r.length - 1) 2 [1, 3, 2] ∧
        ThetaFixedDefs.cycleFrom seed seed.length = ThetaFixedDefs.theta seed := by
    let smaller := r.length - 3
    let basis := smaller :: List.range' 1 (smaller - 1)
    have hsmaller : 2 ≤ smaller := by dsimp [smaller]; omega
    have hbsize : basis.length = smaller := by
      simp only [basis, List.length_cons, List.length_range']
      omega
    have hbperm : basis.Perm (List.range' 1 basis.length) := by
      have hconcat := List.range'_1_concat (s := 1) (n := smaller - 1)
      have hrange : List.range' 1 smaller = List.range' 1 (smaller - 1) ++ [smaller] := by
        simpa only [show smaller - 1 + 1 = smaller by omega,
          show 1 + (smaller - 1) = smaller by omega] using hconcat
      rw [hbsize, hrange]
      exact (List.perm_append_singleton _ _).symm
    have hbfirst : basis.getD 0 0 = basis.length := by
      simp only [basis, List.getD_cons_zero, hbsize]
    have hbshift : basis.length + 3 = r.length := by rw [hbsize]; dsimp [smaller]; omega
    have hbpenult : basis.length + 1 = r.length - 2 := by omega
    have hblast : basis.length + 2 = r.length - 1 := by omega
    have hscan := ThetaIterateInsertion.insertion_scan basis hbperm
      (by rw [hbsize]; dsimp [smaller]; omega) hbfirst
    obtain ⟨seed, hs, hunique⟩ := hscan.2.2.2.2 r
      (by simpa only [hbshift] using hr)
      (by simpa only [hbshift] using hfirst)
      (by simpa only [hblast] using hsecond)
      (by simpa only [hbpenult] using hpenult)
      (by simpa only [hblast, hbpenult] using hlast.trans heq)
    have hslen : seed.length = basis.length := by
      simpa only [List.length_range'] using hs.1.length_eq
    have hsperm : seed.Perm (List.range' 1 seed.length) := by
      simpa only [hslen] using hs.1
    have hsfirst : seed.getD 0 0 = seed.length := by simpa only [hslen] using hs.2.1
    have hseedscan := ThetaIterateInsertion.insertion_scan seed hsperm
      (by rw [hslen, hbsize]; dsimp [smaller]; omega) hsfirst
    have hsavoid : ¬ Contains [1, 3, 2] [] 3 seed :=
      hseedscan.2.2.1.mp (by simpa only [hs.2.2] using hravoid)
    have hbsavoid : ¬ Contains [1, 3, 2] [] 3 (b seed) :=
      hseedscan.2.2.2.1.mp (by simpa only [hs.2.2] using hbavoid)
    obtain ⟨inner, hi, hifirst, hilast, hirestore, hiperm, hihead, hitheta, hicycle,
        hiavoid⟩ := ThetaIterateInsertionInverse.insertion_cycle_inverse q hq
      (by omega) (by simpa only [hlen] using hcycle)
      (by change (B q).getD 0 0 = q.length; rw [hθ.2, hlen]; exact hfirst)
      (by change (B q).getD 1 0 = q.length - 1; rw [hθ.2, hlen]; exact hsecond)
      (by change (B q).getD (q.length - 2) 0 = 1; rw [hθ.2, hlen]; exact hpenult)
      (by change (B q).getD (q.length - 1) 0 = q.length - 2
          rw [hθ.2, hlen]; exact hlast.trans heq)
    have hilength : inner.length = basis.length := by
      have hh := hi.length_eq
      simp only [List.length_range', hlen] at hh
      rw [hbsize]
      exact hh
    have hirecovered : B inner = seed := by
      apply hunique
      exact ⟨by simpa only [hilength] using hiperm,
        by simpa only [hilength] using hihead, hirestore.trans hθ.2⟩
    have hθseedavoid : ¬ Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta seed) := by
      rw [← hirecovered, hitheta]
      exact hiavoid hqavoid
    have hseedcycle : ThetaFixedDefs.cycleFrom seed seed.length =
        ThetaFixedDefs.theta seed := by
      rw [← hirecovered, hitheta]
      simpa only [List.length_map, List.length_range'] using hicycle
    have hnocross (first last : ℕ) (hfl : first < last) (hl : last < seed.length) :
        ¬ ((b seed).getD first 0 < seed.getD 0 0 + 1 ∧
          seed.getD 0 0 + 1 < (b seed).getD last 0) := by
      intro hcross
      have hb := b_perm_of_first_max seed hsperm hsfirst
      have hm : (b seed).getD last 0 ∈ b seed := by
        rw [List.getD_eq_getElem _ 0 (by simp [b]; exact hl)]
        exact List.getElem_mem (by simp [b]; exact hl)
      obtain ⟨offset, ho, he⟩ := List.mem_range'.mp (hb.mem_iff.mp hm)
      rw [hsfirst] at hcross
      omega
    have hmember := (ThetaIterateCycleReduction.P_cycle_reduction seed hsperm
      (by omega)).2.2.1.mpr
      ⟨hsavoid, hθseedavoid, hbsavoid, hnocross⟩
    have hcountsize : seed.length + 2 = r.length - 1 := by
      rw [hslen, hbsize]
      dsimp [smaller]
      omega
    refine ⟨seed, ⟨by simpa only [hbsize, smaller] using hs.1,
      by simpa only [hbsize, smaller] using hs.2.1, hs.2.2,
      by simpa only [hcountsize] using hmember, hseedcycle⟩, ?_⟩
    intro other ho
    apply hunique other
    exact ⟨by simpa only [hbsize, smaller] using ho.1,
      by simpa only [hbsize, smaller] using ho.2.1, ho.2.2.1⟩
  right
  right
  refine ⟨hsecond, hpenult, hv, hvbound, hwholecycle, ?_, hinsertion⟩
  intro hsmall
  let d := h - v
  have hd : 3 ≤ d := by omega
  have hdv : d ≤ v := by
    have hhalf := terminal_value_at_least_half r q v hr hsize hq hlen hcycle
      hmap hfirst hsecond hpenult hlast hv hravoid hbavoid hqavoid
    omega
  have hrun := high_prefix_descending r v hr hsize hfirst hsecond hpenult hlast
    hv hravoid hbavoid
  have hlow := low_suffix_descending r q v hr hsize hq hlen hcycle hmap
    hfirst hsecond hpenult hlast hv hsmall hravoid hbavoid hqavoid
  have hrnd : r.Nodup := hr.nodup_iff.mpr List.nodup_range'
  have hval (i : ℕ) (hi : i < h) : 1 ≤ r.getD i 0 ∧ r.getD i 0 ≤ h := by
    have hm : r.getD i 0 ∈ r := by
      rw [List.getD_eq_getElem _ 0 hi]
      exact List.getElem_mem hi
    obtain ⟨j, hj, heq⟩ := List.mem_range'.mp (hr.mem_iff.mp hm)
    omega
  have hinj (i j : ℕ) (hi : i < h) (hj : j < h)
      (heq : r.getD i 0 = r.getD j 0) : i = j := by
    rw [List.getD_eq_getElem _ 0 hi, List.getD_eq_getElem _ 0 hj] at heq
    exact hrnd.getElem_inj_iff.mp heq
  have hmiddle (i : ℕ) (hdi : d ≤ i) (hiv : i < v) :
      d ≤ r.getD i 0 ∧ r.getD i 0 < v := by
    have hi : i < h := by omega
    have hbounds := hval i hi
    constructor
    · by_contra hnot
      by_cases hone : r.getD i 0 = 1
      · have := hinj i (h - 2) hi (by omega) (hone.trans hpenult.symm)
        omega
      · let j := h - 1 - r.getD i 0
        have hj : v ≤ j ∧ j < h - 2 := by dsimp [j, d]; omega
        have hjval := hlow j hj.1 hj.2
        have heq : r.getD i 0 = r.getD j 0 := by
          rw [hjval]
          dsimp [j]
          omega
        have := hinj i j hi (by omega) heq
        omega
    · by_contra hnot
      by_cases heqv : r.getD i 0 = v
      · have := hinj i (h - 1) hi (by omega) (heqv.trans hlast.symm)
        omega
      · let j := h - r.getD i 0
        have hj : j < d := by dsimp [j, d]; omega
        have hjval := hrun j hj
        have heq : r.getD i 0 = r.getD j 0 := by
          rw [hjval]
          dsimp [j]
          omega
        have := hinj i j hi (by omega) heq
        omega
  have hidxmiddle (x : ℕ) (hdx : d ≤ x) (hxv : x < v) :
      d ≤ r.idxOf x ∧ r.idxOf x < v := by
    have hxmem : x ∈ r := hr.mem_iff.mpr
      (List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩)
    have hi : r.idxOf x < h := List.idxOf_lt_length_of_mem hxmem
    have hget : r.getD (r.idxOf x) 0 = x := by
      rw [List.getD_eq_getElem _ 0 hi]
      exact List.getElem_idxOf hi
    constructor
    · by_contra hnot
      have heq := hrun (r.idxOf x) (by omega)
      rw [hget] at heq
      omega
    · by_contra hnot
      by_cases hbefore : r.idxOf x < h - 2
      · have heq := hlow (r.idxOf x) (by omega) hbefore
        rw [hget] at heq
        omega
      · have hcases : r.idxOf x = h - 2 ∨ r.idxOf x = h - 1 := by omega
        rcases hcases with heq | heq
        · rw [heq, hpenult] at hget
          omega
        · rw [heq, hlast] at hget
          omega
  have hblen : (b r).length = h := by simp [b, h]
  have hbentry (i : ℕ) (hi : i + 1 < h) :
      (b r).getD (r.getD i 0 - 1) 0 = r.getD (i + 1) 0 + 1 := by
    have hv := hval i (by omega)
    have hri : r.idxOf (r.getD i 0) = i := by
      rw [List.getD_eq_getElem _ 0 (by omega)]
      simpa using List.get_idxOf hrnd ⟨i, by omega⟩
    rw [List.getD_eq_getElem _ 0 (by omega)]
    simp only [b, List.getElem_map, List.getElem_range'_1]
    rw [show 1 + (r.getD i 0 - 1) = r.getD i 0 by omega, hri, if_pos hi]
  have hbtwo : (b r).getD 1 0 = 2 := by
    have hr2 := hlow (h - 3) (by omega) (by omega)
    have hr2val : r.getD (h - 3) 0 = 2 := by omega
    have heq := hbentry (h - 3) (by omega)
    rw [hr2val, show h - 3 + 1 = h - 2 by omega, hpenult] at heq
    exact heq
  have hupper : v ≤ d + 1 := by
    by_contra hnot
    have hgap : d + 1 < v := by omega
    have hbd (x : ℕ) (hdx : d ≤ x) (hxv : x < v) :
        d ≤ (b r).getD (x - 1) 0 := by
      have hxidx := hidxmiddle x hdx hxv
      have hxlen : r.idxOf x < h := by omega
      have hxget : r.getD (r.idxOf x) 0 = x := by
        rw [List.getD_eq_getElem _ 0 hxlen]
        exact List.getElem_idxOf hxlen
      have heq := hbentry (r.idxOf x) (by omega)
      rw [hxget] at heq
      by_cases hlastA : r.idxOf x + 1 = v
      · have hvnext := hlow v (le_refl _) hsmall
        rw [hlastA, hvnext] at heq
        omega
      · have hm := hmiddle (r.idxOf x + 1) (by omega) (by omega)
        omega
    have hbincreasing (x y : ℕ) (hdx : d ≤ x) (hxy : x < y) (hyv : y < v) :
        (b r).getD (x - 1) 0 < (b r).getD (y - 1) 0 := by
      have hbnd : (b r).Nodup :=
        (b_perm_of_first_max r hr hfirst).nodup_iff.mpr List.nodup_range'
      have hne : (b r).getD (x - 1) 0 ≠ (b r).getD (y - 1) 0 := by
        intro heq
        rw [List.getD_eq_getElem _ 0 (by omega),
          List.getD_eq_getElem _ 0 (by omega)] at heq
        have := hbnd.getElem_inj_iff.mp heq
        omega
      by_contra hnot
      have hbdy := hbd y (by omega) hyv
      apply hbavoid
      apply (contains132_iff_indices (b r)).mpr
      refine ⟨⟨1, by omega⟩, ⟨x - 1, by omega⟩, ⟨y - 1, by omega⟩,
        by change 1 < x - 1; omega, by change x - 1 < y - 1; omega, ?_, ?_⟩
      · have hlt : (b r).getD 1 0 < (b r).getD (y - 1) 0 := by
          rw [hbtwo]
          omega
        simpa only [← List.getD_eq_getElem _ 0 (by omega : 1 < (b r).length),
          ← List.getD_eq_getElem _ 0 (by omega : y - 1 < (b r).length)] using hlt
      · have hlt : (b r).getD (y - 1) 0 < (b r).getD (x - 1) 0 := by omega
        simpa only [← List.getD_eq_getElem _ 0 (by omega : y - 1 < (b r).length),
          ← List.getD_eq_getElem _ 0 (by omega : x - 1 < (b r).length)] using hlt
    let lastA := r.getD (v - 1) 0
    have hlastArange : d ≤ lastA ∧ lastA < v := hmiddle (v - 1) (by omega) (by omega)
    have hlastAb : (b r).getD (lastA - 1) 0 = d := by
      have heq := hbentry (v - 1) (by omega)
      have hvnext := hlow v (le_refl _) hsmall
      rw [show v - 1 + 1 = v by omega, hvnext] at heq
      dsimp [d, lastA]
      omega
    have hlastA : lastA = d := by
      by_contra hne
      have heq := hbincreasing d lastA (le_refl _) (by omega) hlastArange.2
      have hbound := hbd d (le_refl _) (by omega)
      rw [hlastAb] at heq
      omega
    have hrvat : image r v = d := hlastA
    have hrd : image r d = v + 1 := by
      change r.getD (d - 1) 0 = v + 1
      have heq := hrun (d - 1) (by omega)
      omega
    have hqnd : q.Nodup := hq.nodup_iff.mpr List.nodup_range'
    have hmem (x : ℕ) (hx : 1 ≤ x) (hxh : x ≤ h) : x ∈ q :=
      hq.mem_iff.mpr (List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩)
    have hmax : ∀ x ∈ q, x ≤ q.getD 0 0 := by
      intro x hx
      obtain ⟨j, hj, heq⟩ := List.mem_range'.mp (hq.mem_iff.mp hx)
      omega
    have hidx (i : ℕ) (hi : i < q.length) : q.idxOf (q.getD i 0) = i := by
      rw [List.getD_eq_getElem _ 0 hi]
      simpa using List.get_idxOf hqnd ⟨i, hi⟩
    have hhidx : q.idxOf h = 0 := by
      have heq := hidx 0 (by omega)
      rwa [hcycle] at heq
    have hqsecond : q.getD 1 0 = v := by
      have heq := hat_one_block q hmax h (hmem h (by omega) (le_refl _))
      rw [hhidx, if_pos (by omega), hmap h (by omega) (le_refl _)] at heq
      change r.getD (h - 1) 0 = q.getD 1 0 at heq
      exact heq.symm.trans hlast
    have hvidx : q.idxOf v = 1 := by
      have heq := hidx 1 (by omega)
      rwa [hqsecond] at heq
    have hqthird : q.getD 2 0 = d := by
      have heq := hat_one_block q hmax v (hmem v (by omega) (by omega))
      rw [hvidx, if_pos (by omega), hmap v (by omega) (by omega), hrvat] at heq
      exact heq.symm
    have hdidx : q.idxOf d = 2 := by
      have heq := hidx 2 (by omega)
      rwa [hqthird] at heq
    have hqfourth : q.getD 3 0 = v + 1 := by
      have heq := hat_one_block q hmax d (hmem d (by omega) (by omega))
      rw [hdidx, if_pos (by omega), hmap d (by omega) (by omega), hrd] at heq
      exact heq.symm
    let k := q.idxOf (d + 1)
    have hklen : k < q.length :=
      List.idxOf_lt_length_of_mem (hmem (d + 1) (by omega) (by omega))
    have hkval : q.getD k 0 = d + 1 := by
      rw [List.getD_eq_getElem _ 0 hklen]
      exact List.getElem_idxOf hklen
    have hkafter : 3 < k := by
      by_contra hnot
      have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases hcases with heq | heq | heq | heq
      · rw [heq, hcycle] at hkval
        omega
      · rw [heq, hqsecond] at hkval
        omega
      · rw [heq, hqthird] at hkval
        omega
      · rw [heq, hqfourth] at hkval
        omega
    apply hqavoid
    apply (contains132_iff_indices q).mpr
    refine ⟨⟨2, by omega⟩, ⟨3, by omega⟩, ⟨k, hklen⟩, by simp, hkafter, ?_, ?_⟩
    · have hlt : q.getD 2 0 < q.getD k 0 := by rw [hqthird, hkval]; omega
      simpa only [← List.getD_eq_getElem _ 0 (by omega : 2 < q.length),
        ← List.getD_eq_getElem _ 0 hklen] using hlt
    · have hlt : q.getD k 0 < q.getD 3 0 := by rw [hkval, hqfourth]; omega
      simpa only [← List.getD_eq_getElem _ 0 hklen,
        ← List.getD_eq_getElem _ 0 (by omega : 3 < q.length)] using hlt
  have hvform : v = (h + 1) / 2 := by omega
  have hmiddlevalue (i : ℕ) (hdi : d ≤ i) (hih : i < h - 1) :
      r.getD i 0 = h - 1 - i := by
    by_cases hiv : i < v
    · have hm := hmiddle i hdi hiv
      omega
    · by_cases hip : i < h - 2
      · exact hlow i (by omega) hip
      · have heq : i = h - 2 := by omega
        rw [heq, hpenult]
        omega
  apply List.ext_getElem
  · simp only [W, List.length_append, List.length_reverse, List.length_range',
      List.length_singleton]
    change h = _
    rw [← hvform]
    omega
  · intro i hi₁ hi₂
    have hi : i < h := hi₁
    rw [← List.getD_eq_getElem _ 0 hi₁]
    change r.getD i 0 = (W h)[i]
    by_cases hid : i < d
    · rw [hrun i hid]
      simp only [W, ← hvform, List.getElem_append, List.length_append,
        List.length_reverse, List.length_range',
        dif_pos (by omega : i < (h - v) + (v - 1)),
        dif_pos (by omega : i < h - v), List.getElem_reverse, List.getElem_range'_1]
      omega
    · by_cases hifinal : i < h - 1
      · rw [hmiddlevalue i (by omega) hifinal]
        simp only [W, ← hvform, List.getElem_append, List.length_append,
          List.length_reverse, List.length_range',
          dif_pos (by omega : i < (h - v) + (v - 1)),
          dif_neg (by omega : ¬ i < h - v), List.getElem_reverse, List.getElem_range'_1]
        omega
      · have heq : i = h - 1 := by omega
        rw [← List.getD_eq_getElem _ 0 hi₂]
        rw [heq, hlast]
        rw [W, ← hvform, List.getD_append_right _ _ 0 (h - 1) (by simp; omega)]
        simp only [List.length_append, List.length_reverse, List.length_range']
        have hz : h - 1 - ((h - v) + (v - 1)) = 0 := by omega
        change v = [v].getD (h - 1 - ((h - v) + (v - 1))) 0
        simp [hz]

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateForcedWord
