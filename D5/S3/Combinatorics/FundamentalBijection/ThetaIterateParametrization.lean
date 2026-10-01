/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateParametrization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateParametrization
   mirror-E: none(waiver:first-endpoint-insertion-bijection)
   anchors: [mathlib/module/Mathlib.Tactic.IntervalCases]
   utility: none
   digest: The insertion inverse and distinct terminal letters count the first-endpoint families. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateWTests
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateVFamilies
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseBlocks
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseGeneral
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateParametrization

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.FundamentalBijection
open ThetaFixedDefs ThetaIterateCycle ThetaIterateInsertion ThetaIterateForcedWord

open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords
open D5.S3.Combinatorics.FundamentalBijection.ThetaIteratePosition

local notation "B" =>
  (fun word : List ℕ => List.map (hat word) (List.range' 1 (List.length word)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem first_endpoint_parametrization (size : ℕ) (hsize : 2 ≤ size) :
    let family : ℕ → Set (List ℕ) := fun dimension => {word |
      word.Perm (List.range' 1 dimension) ∧ word.getD 0 0 = dimension ∧
        P word ∈ ThetaIterateDefs.iterateAvoiders (dimension + 2) 2 [1, 3, 2]}
    (6 ≤ size →
      let seeds : Set (List ℕ) := {word | word ∈ family (size - 3) ∧
        cycleFrom word (size - 3) = theta word}
      family size = insert (ThetaIterateUFamilies.U size)
        (insert (List.range' 1 size).reverse (insert (W size) (I '' seeds))) ∧
        (family size).ncard = seeds.ncard + 3 ∧
        (family size).ncard = (family (size - 3)).ncard + 2) ∧
    (family size).ncard = (2 * size + 1) / 3 := by
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
  let family : ℕ → Set (List ℕ) := fun dimension => {word |
    word.Perm (List.range' 1 dimension) ∧ word.getD 0 0 = dimension ∧
      P word ∈ ThetaIterateDefs.iterateAvoiders (dimension + 2) 2 [1, 3, 2]}
  have hbase (size : ℕ) (hsize : 2 ≤ size) (hsmall : size ≤ 5) :
      (family size).ncard = (2 * size + 1) / 3 := by
    let family : Set (List ℕ) := {word | word.Perm (List.range' 1 size) ∧
      word.getD 0 0 = size ∧
      P word ∈ ThetaIterateDefs.iterateAvoiders (size + 2) 2 [1, 3, 2]}
    have contains132_iff_indices (word : List ℕ) :
        Contains [1, 3, 2] [] 3 word ↔
          ∃ first middle last : Fin word.length, first < middle ∧ middle < last ∧
            word[first.val] < word[last.val] ∧ word[last.val] < word[middle.val] := by
      constructor
      · rintro ⟨values, hlt, _, hsub, _⟩
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
        · simpa only [hfirst, hlast] using hlt 1 (by omega) (by omega)
        · simpa only [hlast, hmiddle] using hlt 2 (by omega) (by omega)
      · rintro ⟨first, middle, last, hfirstMiddle, hmiddleLast, hfirstLast, hlastMiddle⟩
        let values : ℕ → ℕ := fun label =>
          if label = 1 then word[first.val] else if label = 2 then word[last.val]
          else word[middle.val]
        have hsub : List.Sublist [word[first.val], word[middle.val], word[last.val]] word := by
          let positions : Fin 3 → Fin word.length := fun index =>
            if index.val = 0 then first else if index.val = 1 then middle else last
          have hmono : StrictMono positions := by
            intro left right hlt
            fin_cases left <;> fin_cases right <;> simp_all [positions]; omega
          apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
          refine ⟨OrderEmbedding.ofStrictMono positions hmono, ?_⟩
          intro index
          fin_cases index <;> simp [positions]
        refine ⟨values, ?_, ?_, ?_, by simp⟩
        · intro label hlower hupper
          have hcases : label = 1 ∨ label = 2 := by omega
          rcases hcases with rfl | rfl <;> simp [values, hfirstLast, hlastMiddle]
        · intro label hlower hupper
          have hcases : label = 1 ∨ label = 2 ∨ label = 3 := by omega
          rcases hcases with rfl | rfl | rfl <;> simp [values]
        · simpa [values] using hsub
    let avoids : List ℕ → Prop := fun word =>
      ¬ ∃ first middle last : Fin word.length, first < middle ∧ middle < last ∧
        word.getD first.val 0 < word.getD last.val 0 ∧
          word.getD last.val 0 < word.getD middle.val 0
    have avoids_iff (word : List ℕ) : avoids word ↔ ¬ Contains [1, 3, 2] [] 3 word := by
      have hget (index : Fin word.length) : word.getD index.val 0 = word[index.val] :=
        List.getD_eq_getElem _ _ index.isLt
      dsimp only [avoids]
      simp only [hget]
      exact not_congr (contains132_iff_indices word).symm
    let tests : List ℕ → Prop := fun word =>
      avoids word ∧ avoids (theta word) ∧ avoids (b word) ∧
        ∀ first last : Fin word.length, first < last →
          ¬ ((b word).getD first.val 0 < word.getD 0 0 + 1 ∧
            word.getD 0 0 + 1 < (b word).getD last.val 0)
    let candidates := ((List.range' 1 size).permutations.toFinset.filter
      (fun word => word.getD 0 0 = size)).filter tests
    have hset : family = (candidates : Set (List ℕ)) := by
      ext word
      simp only [family, Set.mem_ofPred_eq, candidates, Finset.mem_coe, Finset.mem_filter,
        List.mem_toFinset, List.mem_permutations]
      constructor
      · rintro ⟨hperm, hhead, hmember⟩
        have hlength : word.length = size := by simpa using hperm.length_eq
        have hscan := (ThetaIterateCycleReduction.P_cycle_reduction word
          (by simpa only [hlength] using hperm) (by omega)).2.2.1
        rw [hlength] at hscan
        obtain ⟨hword, htheta, hb, hcross⟩ := hscan.mp hmember
        refine ⟨⟨hperm, hhead⟩, ?_⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact (avoids_iff word).mpr hword
        · exact (avoids_iff (theta word)).mpr htheta
        · exact (avoids_iff (b word)).mpr hb
        · intro first last hlt
          exact hcross first.val last.val hlt (by omega)
      · rintro ⟨⟨hperm, hhead⟩, hword, htheta, hb, hcross⟩
        have hlength : word.length = size := by simpa using hperm.length_eq
        refine ⟨hperm, hhead, ?_⟩
        have hscan := (ThetaIterateCycleReduction.P_cycle_reduction word
          (by simpa only [hlength] using hperm) (by omega)).2.2.1
        rw [hlength] at hscan
        apply hscan.mpr
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact (avoids_iff word).mp hword
        · exact (avoids_iff (theta word)).mp htheta
        · exact (avoids_iff (b word)).mp hb
        · intro first last hlt hlast
          exact hcross ⟨first, by omega⟩ ⟨last, by omega⟩ hlt
    change family.ncard = _
    rw [hset, Set.ncard_coe_finset]
    change (Finset.filter tests
      (Finset.filter (fun word => word.getD 0 0 = size)
        (List.permutations (List.range' 1 size)).toFinset)).card = _
    rw [List.filter_toFinset, List.filter_toFinset, List.card_toFinset]
    dsimp +zetaDelta only [candidates, tests, avoids]
    interval_cases size <;>
      simp only [List.range', List.permutations, List.permutationsAux_cons,
        List.permutationsAux_nil] <;> decide
  have hlarge (size : ℕ) (hsize : 6 ≤ size) :
    let family : ℕ → Set (List ℕ) := fun dimension => {word |
      word.Perm (List.range' 1 dimension) ∧ word.getD 0 0 = dimension ∧
        P word ∈ ThetaIterateDefs.iterateAvoiders (dimension + 2) 2 [1, 3, 2]}
    let seeds : Set (List ℕ) := {word | word ∈ family (size - 3) ∧
      cycleFrom word (size - 3) = theta word}
    family size = insert (ThetaIterateUFamilies.U size)
      (insert (List.range' 1 size).reverse (insert (W size) (I '' seeds))) ∧
      (family size).ncard = seeds.ncard + 3 ∧
      (family size).ncard = (family (size - 3)).ncard + 2 := by
    classical
    let family : ℕ → Set (List ℕ) := fun dimension => {word |
      word.Perm (List.range' 1 dimension) ∧ word.getD 0 0 = dimension ∧
        P word ∈ ThetaIterateDefs.iterateAvoiders (dimension + 2) 2 [1, 3, 2]}
    let seeds : Set (List ℕ) := {word | word ∈ family (size - 3) ∧
      cycleFrom word (size - 3) = theta word}
    let increasing := ThetaIterateUFamilies.U size
    let decreasing := (List.range' 1 size).reverse
    let alternating := W size
    have hincreasingData := ThetaIterateUFamilies.U_family size (by omega)
    have hincreasing : increasing ∈ family size := by
      refine ⟨hincreasingData.1, by simp [increasing, ThetaIterateUFamilies.U], ?_⟩
      apply (hincreasingData.2.2.2.1 increasing hincreasingData.1
        (by simp [increasing, ThetaIterateUFamilies.U]) ?_).mpr rfl
      simp only [increasing, ThetaIterateUFamilies.U, List.getD_cons_succ]
      rw [List.getD_eq_getElem _ 0 (by simp; omega)]
      simp
      omega
    have hdecreasingPerm : decreasing.Perm (List.range' 1 size) := List.reverse_perm _
    have hdecreasingLength : decreasing.length = size := by simp [decreasing]
    have hdecreasingFirst : decreasing.getD 0 0 = size := by
      rw [List.getD_eq_getElem _ 0 (by omega)]
      simp only [decreasing, List.getElem_reverse, List.length_range', List.getElem_range'_1]
      omega
    have hdecreasingLast : decreasing.getD (size - 1) 0 = 1 := by
      rw [List.getD_eq_getElem _ 0 (by omega)]
      simp only [decreasing, List.getElem_reverse, List.length_range', List.getElem_range'_1]
      omega
    have hdecreasing : decreasing ∈ family size := by
      refine ⟨hdecreasingPerm, hdecreasingFirst, ?_⟩
      exact ((ThetaIterateVFamilies.V_family size (by omega)).2.2.1 decreasing
        hdecreasingPerm hdecreasingFirst hdecreasingLast).mpr rfl
    have halternatingData := ThetaIterateWTests.W_tests size (by omega)
    have halternatingLength : alternating.length = size := by
      simpa using halternatingData.1.length_eq
    have hcenter : 2 ≤ (size + 1) / 2 ∧ (size + 1) / 2 < size - 2 := by omega
    have halternatingFirst : alternating.getD 0 0 = size := by
      change (W size).getD 0 0 = size
      unfold W
      rw [List.getD_append _ _ _ _ (by simp; omega)]
      rw [List.getD_append _ _ _ _ (by simp; omega)]
      rw [List.getD_eq_getElem _ 0 (by simp; omega)]
      simp only [List.getElem_reverse, List.length_range', List.getElem_range'_1]
      omega
    have halternatingLast : alternating.getD (size - 1) 0 = (size + 1) / 2 := by
      change (W size).getD (size - 1) 0 = _
      unfold W
      rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_append, List.length_reverse, List.length_range']
      have hzero : size - 1 - (size - (size + 1) / 2 + ((size + 1) / 2 - 1)) = 0 := by
        omega
      simp [hzero]
    have halternating : alternating ∈ family size :=
      ⟨halternatingData.1, halternatingFirst, halternatingData.2.2.2.2⟩
    have hincreasingLength : increasing.length = size := by
      simpa using hincreasing.1.length_eq
    have hincreasingLast : increasing.getD (size - 1) 0 = size - 1 := by
      change (size :: List.range' 1 (size - 1)).getD (size - 1) 0 = size - 1
      rw [show size - 1 = (size - 2) + 1 by omega, List.getD_cons_succ]
      rw [List.getD_eq_getElem _ 0 (by simp), List.getElem_range'_1]
      omega
    have seed_length (seed : List ℕ) (hseed : seed ∈ seeds) : seed.length = size - 3 := by
      simpa using hseed.1.1.length_eq
    have inserted_length (seed : List ℕ) (hseed : seed ∈ seeds) : (I seed).length = size := by
      have hlength := seed_length seed hseed
      simp [I, hlength]
      omega
    have inserted_last (seed : List ℕ) (hseed : seed ∈ seeds) :
        (I seed).getD (size - 1) 0 = size - 2 := by
      have hlength := seed_length seed hseed
      unfold I
      rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
        List.length_drop, hlength]
      have hindex : size - 1 - (2 + (size - 3 - 1)) = 1 := by omega
      simp [hindex]
      omega
    have inserted_member (seed : List ℕ) (hseed : seed ∈ seeds) : I seed ∈ family size := by
      have hlength := seed_length seed hseed
      have hseedPerm : seed.Perm (List.range' 1 seed.length) := by
        simpa only [hlength] using hseed.1.1
      have hseedFirst : seed.getD 0 0 = seed.length := by
        simpa only [hlength] using hseed.1.2.1
      have hinverse := theta_record_inverse seed hseedPerm
      let cycle := theta seed
      have hcyclePerm : cycle.Perm (List.range' 1 seed.length) := hinverse.2.2.1
      have hcycleLength : cycle.length = seed.length := by simpa using hcyclePerm.length_eq
      have hcyclePerm' : cycle.Perm (List.range' 1 cycle.length) := by
        simpa only [hcycleLength] using hcyclePerm
      have hcanonical : B cycle = seed := hinverse.2.2.2
      change (List.range' 1 cycle.length).map (hat cycle) = seed at hcanonical
      have hcycleFirst : cycle.getD 0 0 = cycle.length := by
        change (theta seed).getD 0 0 = cycle.length
        rw [← hseed.2, hcycleLength, ← hlength]
        simp [cycleFrom]
      have hcycleLast : cycle.getD (cycle.length - 1) 0 = 1 := by
        apply ThetaBasicInverseTail.B_first_max_forces_last_one cycle hcyclePerm'
          (by omega)
        change ((List.range' 1 cycle.length).map (hat cycle)).getD 0 0 = cycle.length
        rw [hcanonical, hcycleLength]
        exact hseedFirst
      have hscan := insertion_scan seed hseedPerm (by omega) hseedFirst
      have hinsertion := ThetaIterateInsertionCycle.insertion_cycle cycle hcyclePerm'
        (by omega) hcycleFirst hcycleLast
      have htest := hinsertion.2.1
      rw [hcanonical, hcycleLength, hlength,
        show size - 3 + 5 = size + 2 by omega] at htest
      refine ⟨?_, ?_, htest.mpr hseed.1.2.2⟩
      · simpa only [hlength, show size - 3 + 3 = size by omega] using hscan.1
      · simp [I, hlength]
        omega
    have hsurjective (word : List ℕ) (hword : word ∈ family size) :
        word = increasing ∨ word = decreasing ∨ word = alternating ∨ word ∈ I '' seeds := by
      have hlength : word.length = size := by simpa using hword.1.length_eq
      have hperm : word.Perm (List.range' 1 word.length) := by
        simpa only [hlength] using hword.1
      have htests := (ThetaIterateCycleReduction.P_cycle_reduction word hperm
        (by omega)).2.2.1.mp (by simpa only [hlength] using hword.2.2)
      have hclassification := first_endpoint_classification word
        (word.getD (size - 1) 0) hperm (by omega)
        (by simpa only [hlength] using hword.2.1)
        (by rw [hlength]) htests.1 htests.2.2.1 htests.2.1
      rw [hlength] at hclassification
      rcases hclassification with hU | hV | hother
      · exact Or.inl hU
      · exact Or.inr (Or.inl hV)
      · by_cases hsmall : word.getD (size - 1) 0 < size - 2
        · exact Or.inr (Or.inr (Or.inl (hother.2.2.2.2.2.1 hsmall)))
        · have hlast : word.getD (size - 1) 0 = size - 2 := by
            have hbound := hother.2.2.2.1
            omega
          obtain ⟨seed, hseed, _⟩ := hother.2.2.2.2.2.2 hlast (by omega)
          have hseedLength : seed.length = size - 3 := by simpa using hseed.1.length_eq
          refine Or.inr (Or.inr (Or.inr ⟨seed, ?_, hseed.2.2.1⟩))
          refine ⟨⟨hseed.1, hseed.2.1, ?_⟩, ?_⟩
          · rw [show size - 3 + 2 = size - 1 by omega]
            exact hseed.2.2.2.1
          · simpa only [hseedLength] using hseed.2.2.2.2
    have hinjective : Set.InjOn I seeds := by
      intro left hleft right hright hequal
      have hleftLength := seed_length left hleft
      have hrightLength := seed_length right hright
      change ([left.length + 3, left.length + 2] ++ (left.drop 1).map (· + 1) ++
          [1, left.length + 1]) =
        ([right.length + 3, right.length + 2] ++ (right.drop 1).map (· + 1) ++
          [1, right.length + 1]) at hequal
      rw [hleftLength, hrightLength] at hequal
      have hmapEq := List.append_cancel_left (List.append_cancel_right hequal)
      have hinj : Function.Injective (fun value : ℕ => value + 1) := by
        intro first second heq
        change first + 1 = second + 1 at heq
        omega
      have htailEq := hinj.list_map hmapEq
      have hhead (word : List ℕ) (hword : word ∈ seeds) :
          word = (size - 3) :: word.drop 1 := by
        cases heq : word with
        | nil =>
          have hlength := seed_length word hword
          rw [heq] at hlength
          simp at hlength
          omega
        | cons maximum tail =>
          have hfirst := hword.1.2.1
          rw [heq] at hfirst
          simpa using hfirst
      rw [hhead left hleft, hhead right hright, htailEq]
    have hfinite : seeds.Finite := by
      have hpermutations : Set.Finite {word : List ℕ |
          word.Perm (List.range' 1 (size - 3))} := by
        convert (List.permutations (List.range' 1 (size - 3))).finite_toSet using 1
        ext word
        exact List.mem_permutations.symm
      exact hpermutations.subset (fun word hword => hword.1.1)
    have hfamily : family size = insert increasing
        (insert decreasing (insert alternating (I '' seeds))) := by
      ext word
      constructor
      · intro hword
        simpa only [Set.mem_insert_iff] using hsurjective word hword
      · intro hword
        simp only [Set.mem_insert_iff] at hword
        rcases hword with rfl | rfl | rfl | ⟨seed, hseed, rfl⟩
        · exact hincreasing
        · exact hdecreasing
        · exact halternating
        · exact inserted_member seed hseed
    have halternatingNotImage : alternating ∉ I '' seeds := by
      rintro ⟨seed, hseed, hequal⟩
      have hlast := inserted_last seed hseed
      rw [hequal, halternatingLast] at hlast
      omega
    have hdecreasingNotInsert : decreasing ∉ insert alternating (I '' seeds) := by
      intro hmember
      rcases Set.mem_insert_iff.mp hmember with hequal | ⟨seed, hseed, hequal⟩
      · have hlast := congrArg (fun word : List ℕ => word.getD (size - 1) 0) hequal
        rw [hdecreasingLast, halternatingLast] at hlast
        omega
      · have hlast := inserted_last seed hseed
        rw [hequal, hdecreasingLast] at hlast
        omega
    have hincreasingNotInsert : increasing ∉
        insert decreasing (insert alternating (I '' seeds)) := by
      intro hmember
      rcases Set.mem_insert_iff.mp hmember with hequal | hmember
      · have hlast := congrArg (fun word : List ℕ => word.getD (size - 1) 0) hequal
        rw [hincreasingLast, hdecreasingLast] at hlast
        omega
      · rcases Set.mem_insert_iff.mp hmember with hequal | ⟨seed, hseed, hequal⟩
        · have hlast := congrArg (fun word : List ℕ => word.getD (size - 1) 0) hequal
          rw [hincreasingLast, halternatingLast] at hlast
          omega
        · have hlast := inserted_last seed hseed
          rw [hequal, hincreasingLast] at hlast
          omega
    have hcount : (family size).ncard = seeds.ncard + 3 := by
      rw [hfamily, Set.ncard_insert_of_notMem hincreasingNotInsert
          (((hfinite.image I).insert alternating).insert decreasing),
        Set.ncard_insert_of_notMem hdecreasingNotInsert ((hfinite.image I).insert alternating),
        Set.ncard_insert_of_notMem halternatingNotImage (hfinite.image I), hinjective.ncard_image]
    refine ⟨hfamily, hcount, ?_⟩
    let smaller := size - 3
    let excluded := (List.range' 1 smaller).reverse
    have hsmaller : 3 ≤ smaller := by dsimp [smaller]; omega
    have hexcludedPerm : excluded.Perm (List.range' 1 smaller) := List.reverse_perm _
    have hexcludedLength : excluded.length = smaller := by simp [excluded]
    have hexcludedGet (index : ℕ) (hindex : index < smaller) :
        excluded.getD index 0 = smaller - index := by
      rw [List.getD_eq_getElem _ 0 (by omega)]
      simp only [excluded, List.getElem_reverse, List.length_range', List.getElem_range'_1]
      omega
    have hexcludedMember : excluded ∈ family smaller := by
      have hfirst : excluded.getD 0 0 = smaller := by rw [hexcludedGet 0 (by omega)]; omega
      have hlast : excluded.getD (smaller - 1) 0 = 1 := by
        rw [hexcludedGet _ (by omega)]; omega
      exact ⟨hexcludedPerm, hfirst,
        ((ThetaIterateVFamilies.V_family smaller (by omega)).2.2.1 excluded
          hexcludedPerm hfirst hlast).mpr rfl⟩
    have hexcludedCycle : cycleFrom excluded smaller = [smaller, 1] := by
      have hmaxImage : D5.S3.Combinatorics.ArcherCyclicDefs.image excluded smaller = 1 := by
        unfold D5.S3.Combinatorics.ArcherCyclicDefs.image
        rw [hexcludedGet _ (by omega)]
        omega
      have honeImage : D5.S3.Combinatorics.ArcherCyclicDefs.image excluded 1 = smaller := by
        unfold D5.S3.Combinatorics.ArcherCyclicDefs.image
        rw [hexcludedGet _ (by omega)]
        omega
      have htwo : (D5.S3.Combinatorics.ArcherCyclicDefs.image excluded)^[2] smaller =
          smaller := by
        rw [show 2 = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one,
          hmaxImage, honeImage]
      have hrange : List.range smaller = 0 :: 1 :: List.range' 2 (smaller - 2) := by
        rw [List.range_eq_range', show smaller = (smaller - 2 + 1) + 1 by omega,
          List.range'_succ, List.range'_succ]
        rfl
      unfold cycleFrom
      rw [hexcludedLength, hrange]
      simp only [List.map_cons, Nat.zero_add, Function.iterate_one, hmaxImage, htwo]
      simp [show 1 ≠ smaller by omega]
    have hexcludedNotCycle : cycleFrom excluded smaller ≠ theta excluded := by
      have hperm : excluded.Perm (List.range' 1 excluded.length) := by
        simpa only [hexcludedLength] using hexcludedPerm
      have hthetaLength : (theta excluded).length = smaller := by
        simpa only [hexcludedLength, List.length_range'] using
          (theta_record_inverse excluded hperm).2.2.1.length_eq
      intro hequal
      have hlength := congrArg List.length hequal
      rw [hexcludedCycle, hthetaLength] at hlength
      simp only [List.length_cons, List.length_nil] at hlength
      omega
    have one_cycle (word : List ℕ) (hword : word ∈ family smaller) :
        cycleFrom word smaller = theta word ↔ word ≠ excluded := by
      constructor
      · intro hcycle hequal
        rw [hequal] at hcycle
        exact hexcludedNotCycle hcycle
      · intro hnotExcluded
        by_cases hthree : smaller = 3
        · have hperm : word.Perm [1, 2, 3] := by simpa [hthree, List.range'] using hword.1
          have hfirst : word.getD 0 0 = 3 := by simpa only [hthree] using hword.2.1
          have hsubset : (List.permutations [1, 2, 3]) ⊆
              [[1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]] := by
            simp [List.permutations, List.permutationsAux_cons, List.permutationsAux_nil,
              List.permutationsAux2]
          have hcases := hsubset (List.mem_permutations.mpr hperm)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hcases
          rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
          · norm_num at hfirst
          · norm_num at hfirst
          · norm_num at hfirst
          · norm_num at hfirst
          · rw [hthree]
            decide
          · exact False.elim (hnotExcluded (by simp [excluded, hthree, List.range']))
        have hfour : 4 ≤ smaller := by omega
        have hlength : word.length = smaller := by simpa using hword.1.length_eq
        have hperm : word.Perm (List.range' 1 word.length) := by
          simpa only [hlength] using hword.1
        have htests := (ThetaIterateCycleReduction.P_cycle_reduction word hperm
          (by omega)).2.2.1.mp (by simpa only [hlength] using hword.2.2)
        have hclassification := first_endpoint_classification word
          (word.getD (smaller - 1) 0) hperm (by omega)
          (by simpa only [hlength] using hword.2.1) (by rw [hlength])
          htests.1 htests.2.2.1 htests.2.1
        rw [hlength] at hclassification
        rcases hclassification with hU | hV | hother
        · rw [hU]
          exact (ThetaIterateUFamilies.U_family smaller hfour).2.2.2.2
        · exact False.elim (hnotExcluded hV)
        · exact hother.2.2.2.2.1
    have hseeds : seeds = family smaller \ {excluded} := by
      ext word
      change (word ∈ family smaller ∧ cycleFrom word smaller = theta word) ↔
        word ∈ family smaller ∧ word ∉ ({excluded} : Set (List ℕ))
      constructor
      · intro hword
        exact ⟨hword.1, by simpa using (one_cycle word hword.1).mp hword.2⟩
      · intro hword
        exact ⟨hword.1, (one_cycle word hword.1).mpr (by simpa using hword.2)⟩
    have hsmallerFinite : (family smaller).Finite := by
      have hpermutations : Set.Finite {word : List ℕ |
          word.Perm (List.range' 1 smaller)} := by
        convert (List.permutations (List.range' 1 smaller)).finite_toSet using 1
        ext word
        exact List.mem_permutations.symm
      exact hpermutations.subset (fun word hword => hword.1)
    have hremoved : seeds.ncard + 1 = (family smaller).ncard := by
      rw [hseeds]
      exact Set.ncard_sdiff_singleton_add_one hexcludedMember hsmallerFinite
    change (family size).ncard = (family smaller).ncard + 2
    omega
  refine ⟨hlarge size, ?_⟩
  induction size using Nat.strong_induction_on with
  | h size ih =>
    by_cases hsmall : size ≤ 5
    · exact hbase size hsize hsmall
    · have hstep := (hlarge size (by omega)).2.2
      have hprevious := ih (size - 3) (by omega) (by omega)
      change (family size).ncard = (family (size - 3)).ncard + 2 at hstep
      rw [hstep, hprevious]
      omega

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateParametrization
