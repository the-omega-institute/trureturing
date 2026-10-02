/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateUFamilies
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateUFamilies
   mirror-E: none(waiver:first-endpoint-increasing-family)
   anchors: []
   utility: none
   digest: Descending cycle orbits certify the increasing-tail first-endpoint family. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycleReduction
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateFirstEndpoint
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateFirstScan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateUFamilies

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArcherCyclicDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycle
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycleReduction
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords

def U (h : ℕ) : List ℕ := h :: List.range' 1 (h - 1)

theorem U_family (h : ℕ) (hh : 4 ≤ h) :
    (U h).Perm (List.range' 1 h) ∧
      ThetaFixedDefs.theta (U h) = (List.range' 1 h).reverse ∧
      b (U h) = List.range' 3 (h - 2) ++ [1, 2] ∧
      (∀ p : List ℕ, p.Perm (List.range' 1 h) → p.getD 0 0 = h → p.getD 1 0 ≤ h - 2 →
        (P p ∈ ThetaIterateDefs.iterateAvoiders (h + 2) 2 [1, 3, 2] ↔ p = U h)) ∧
      ThetaFixedDefs.cycleFrom (U h) h = ThetaFixedDefs.theta (U h) := by
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
    intro x
    exact hp.mem_iff
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

  let r := U h
  have hlen : r.length = h := by simp [r, U]; omega
  have hget (i : ℕ) (hi : i < h) : r.getD i 0 = if i = 0 then h else i := by
    cases i with
    | zero => simp [r, U]
    | succ i =>
        simp only [r, U, List.getD_cons_succ, if_neg (by omega : i + 1 ≠ 0)]
        rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range'_1]
        omega
  have hperm : r.Perm (List.range' 1 h) := by
    have heq : List.range' 1 h = List.range' 1 (h - 1) ++ [h] := by
      have hs := List.range'_1_concat (s := 1) (n := h - 1)
      simpa only [show h - 1 + 1 = h by omega, show 1 + (h - 1) = h by omega]
        using hs
    rw [heq]
    simpa only [List.singleton_append, r, U] using
      (List.perm_append_comm (l₁ := [h]) (l₂ := List.range' 1 (h - 1)))
  have himage (x : ℕ) (hx : 1 ≤ x) (hxh : x ≤ h) :
      image r x = if x = 1 then h else x - 1 := by
    unfold image
    rw [hget _ (by omega)]
    split_ifs <;> omega
  have horbit (x i : ℕ) (hx : 1 ≤ x) (hxh : x ≤ h) (hi : i ≤ x) :
      (image r)^[i] x = if i < x then x - i else h := by
    induction i with
    | zero => simp [Nat.ne_of_gt hx]
    | succ i ih =>
        rw [Function.iterate_succ_apply', ih (by omega), if_pos (by omega : i < x),
          himage _ (by omega) (by omega)]
        split_ifs <;> omega
  have hcycle : ThetaFixedDefs.cycleFrom r h = (List.range' 1 h).reverse := by
    let orbit := (List.range h).map (fun i => (image r)^[i + 1] h)
    have holength : orbit.length = h := by simp [orbit]
    have hohit : orbit[h - 1]'(by omega) = h := by
      simp only [orbit, List.getElem_map, List.getElem_range]
      rw [horbit h (h - 1 + 1) (by omega) (by omega) (by omega)]
      simp [show h - 1 + 1 = h by omega]
    have hogood : ∀ y ∈ orbit.take (h - 1), decide (y ≠ h) = true := by
      intro y hy
      obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.mp hy
      have hib : i < h - 1 := by simpa [holength, Nat.min_eq_left (by omega)] using hi
      rw [← hiy]
      simp only [List.getElem_take, orbit, List.getElem_map, List.getElem_range]
      rw [horbit h (i + 1) (by omega) (by omega) (by omega)]
      simp only [if_pos (by omega : i + 1 < h), decide_eq_true_eq]
      omega
    have hotake : orbit.takeWhile (· ≠ h) = orbit.take (h - 1) := by
      conv_lhs => rw [← List.take_append_drop (h - 1) orbit]
      rw [List.takeWhile_append_of_pos hogood,
        List.drop_eq_getElem_cons (by omega : h - 1 < orbit.length), hohit]
      simp
    unfold ThetaFixedDefs.cycleFrom
    simp only [hlen]
    change h :: orbit.takeWhile (· ≠ h) = _
    rw [hotake]
    apply List.ext_getElem
    · simp [holength]; omega
    · intro i hi hj
      have hright : (List.range' 1 h).reverse[i] = h - i := by
        simp only [List.getElem_reverse, List.length_range', List.getElem_range'_1]
        have hib : i < h := by simpa using hj
        omega
      rw [hright, ← List.getD_eq_getElem _ 0 hi]
      by_cases hiz : i = 0
      · subst i
        simp
      · have hib : i < h := by simpa using hj
        rw [show i = (i - 1) + 1 by omega, List.getD_cons_succ,
          List.getD_eq_getElem _ 0 (by simp [holength]; omega)]
        simp only [List.getElem_take, orbit, List.getElem_map, List.getElem_range]
        rw [horbit h _ (by omega) (by omega) (by omega),
          if_pos (by omega : i - 1 + 1 < h)]
  have hleaders (x : ℕ) (hx : x ∈ List.range' 1 h) :
      ThetaFixedDefs.IsLeader r x ↔ x = h := by
    obtain ⟨j, hj, heq⟩ := List.mem_range'.mp hx
    have hxpos : 1 ≤ x := by omega
    have hxle : x ≤ h := by omega
    constructor
    · intro hlead
      by_contra hne
      have hxlt : x < h := by omega
      let orbit := (List.range h).map (fun i => (image r)^[i + 1] x)
      have hogood : ∀ y ∈ orbit.take x, decide (y ≠ x) = true := by
        intro y hy
        obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.mp hy
        have hib : i < x := by simpa [orbit, Nat.min_eq_left (by omega : x ≤ h)] using hi
        rw [← hiy]
        simp only [List.getElem_take, orbit, List.getElem_map, List.getElem_range]
        rw [horbit x (i + 1) hxpos hxle (by omega)]
        split_ifs <;> simp only [decide_eq_true_eq] <;> omega
      have hmem : h ∈ orbit.take x := by
        have hib : x - 1 < (orbit.take x).length := by simp [orbit]; omega
        have hget : (orbit.take x)[x - 1] = h := by
          simp only [List.getElem_take, orbit, List.getElem_map, List.getElem_range]
          rw [horbit x _ hxpos hxle (by omega)]
          simp [show x - 1 + 1 = x by omega]
        rw [← hget]
        exact List.getElem_mem hib
      have hm : h ∈ ThetaFixedDefs.cycleFrom r x := by
        unfold ThetaFixedDefs.cycleFrom
        simp only [hlen]
        change h ∈ x :: orbit.takeWhile (· ≠ x)
        apply List.mem_cons_of_mem
        rw [← List.take_append_drop x orbit, List.takeWhile_append_of_pos hogood]
        exact List.mem_append_left _ hmem
      have := hlead h hm
      omega
    · rintro rfl
      unfold ThetaFixedDefs.IsLeader
      rw [hcycle]
      intro y hy
      obtain ⟨i, hi, heq⟩ := List.mem_range'.mp (List.mem_reverse.mp hy)
      omega
  have htheta : ThetaFixedDefs.theta r = (List.range' 1 h).reverse := by
    unfold ThetaFixedDefs.theta
    rw [hlen]
    have hfilter : (List.range' 1 h).filter
        (fun x => decide (ThetaFixedDefs.IsLeader r x)) = [h] := by
      have heq : (List.range' 1 h).filter
          (fun x => decide (ThetaFixedDefs.IsLeader r x)) =
          (List.range' 1 h).filter (fun x => decide (x = h)) := by
        apply List.filter_congr
        intro x hx
        simp only [hleaders x hx]
      rw [heq, List.filter_eq]
      have hm : h ∈ List.range' 1 h := List.mem_range'.mpr ⟨h - 1, by omega, by omega⟩
      rw [(List.nodup_iff_count_eq_one.mp List.nodup_range') h hm]
      simp
    rw [hfilter]
    simpa using hcycle
  have hidx (x : ℕ) (hx : 1 ≤ x) (hxh : x < h) : r.idxOf x = x := by
    have hnd : r.Nodup := hperm.nodup_iff.mpr List.nodup_range'
    have he : r[x] = x := by
      rw [← List.getD_eq_getElem _ 0 (by omega), hget x hxh, if_neg (by omega)]
    have hi := List.get_idxOf hnd ⟨x, by omega⟩
    change r.idxOf r[x] = x at hi
    rw [he] at hi
    exact hi
  have hidxh : r.idxOf h = 0 := by simp [r, U]
  have hbget (i : ℕ) (hi : i < h) :
      (b r).getD i 0 = if i < h - 2 then i + 3 else if i = h - 2 then 1 else 2 := by
    rw [List.getD_eq_getElem _ 0 (by simp [b, hlen]; omega)]
    simp only [b, List.getElem_map, List.getElem_range'_1, hlen,
      show 1 + i = i + 1 by omega]
    by_cases hil : i + 1 < h
    · rw [hidx _ (by omega) hil]
      by_cases his : i + 1 + 1 < h
      · rw [if_pos his, hget _ his, if_neg (by omega)]
        rw [if_pos (by omega : i < h - 2)]
      · rw [if_neg his, if_neg (by omega : ¬ i < h - 2),
          if_pos (by omega : i = h - 2)]
    · have heq : i + 1 = h := by omega
      rw [heq, hidxh, if_pos (by omega), hget 1 (by omega), if_neg (by omega),
        if_neg (by omega : ¬ i < h - 2), if_neg (by omega : i ≠ h - 2)]
  have hbword : b r = List.range' 3 (h - 2) ++ [1, 2] := by
    apply List.ext_getElem
    · simp [b, hlen]; omega
    · intro i hi hj
      rw [← List.getD_eq_getElem _ 0 hi, hbget i (by simpa [b, hlen] using hi)]
      by_cases hib : i < h - 2
      · rw [List.getElem_append_left (by simpa using hib), if_pos hib]
        simp
        omega
      · rw [List.getElem_append_right (by simpa using hib), if_neg hib]
        simp only [List.length_range']
        by_cases heq : i = h - 2
        · simp [heq]
        · rw [if_neg heq]
          have hi' : i - (h - 2) = 1 := by simp only [List.length_append,
            List.length_range', List.length_cons, List.length_nil] at hj; omega
          simp only [hi', List.getElem_cons_succ, List.getElem_cons_zero]
  have havr : ¬ Contains [1, 3, 2] [] 3 r := by
    intro hc
    obtain ⟨i, j, k, hij, hjk, hik, hkj⟩ := (contains132_iff_indices r).mp hc
    rw [← List.getD_eq_getElem _ 0 i.isLt, ← List.getD_eq_getElem _ 0 k.isLt,
      hget i (by omega), hget k (by omega)] at hik
    rw [← List.getD_eq_getElem _ 0 k.isLt, ← List.getD_eq_getElem _ 0 j.isLt,
      hget k (by omega), hget j (by omega)] at hkj
    have := i.isLt
    have := k.isLt
    split_ifs at hik hkj <;> omega
  have havb : ¬ Contains [1, 3, 2] [] 3 (b r) := by
    intro hc
    obtain ⟨i, j, k, hij, hjk, hik, hkj⟩ := (contains132_iff_indices (b r)).mp hc
    have hblen : (b r).length = h := by simp [b, hlen]
    rw [← List.getD_eq_getElem _ 0 i.isLt, ← List.getD_eq_getElem _ 0 k.isLt,
      hbget i (by omega), hbget k (by omega)] at hik
    rw [← List.getD_eq_getElem _ 0 k.isLt, ← List.getD_eq_getElem _ 0 j.isLt,
      hbget k (by omega), hbget j (by omega)] at hkj
    split_ifs at hik hkj <;> omega
  have havtheta : ¬ Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta r) := by
    rw [htheta]
    intro hc
    obtain ⟨i, j, k, hij, hjk, hik, hkj⟩ :=
      (contains132_iff_indices ((List.range' 1 h).reverse)).mp hc
    simp only [List.getElem_reverse, List.length_range', List.getElem_range'_1] at hik
    have hi := i.isLt
    have hk := k.isLt
    simp only [List.length_reverse, List.length_range'] at hi hk
    omega
  have hvalid : r.Perm (List.range' 1 r.length) := by simpa [hlen] using hperm
  have hmember := (P_cycle_reduction r hvalid (by omega)).2.2.1.mpr
    ⟨havr, havtheta, havb, by
      intro i j hij hj hcross
      have hbperm := b_perm_of_first_max r hvalid (by rw [hget 0 (by omega), hlen]; simp)
      have hm : (b r).getD j 0 ∈ b r := by
        rw [List.getD_eq_getElem _ 0 (by simp [b]; omega)]
        exact List.getElem_mem (by simp [b]; omega)
      obtain ⟨t, ht, heq⟩ := List.mem_range'.mp (hbperm.mem_iff.mp hm)
      have hrfirst : r.getD 0 0 = h := by simp [r, U]
      rw [hrfirst] at hcross
      omega⟩
  refine ⟨hperm, htheta, hbword, ?_, ?_⟩
  swap
  · rw [htheta]
    exact hcycle
  intro p hp hpfirst hpsecond
  have hplen : p.length = h := by simpa using hp.length_eq
  have hpvalid : p.Perm (List.range' 1 p.length) := by simpa [hplen] using hp
  constructor
  · intro hpmember
    have hptests := (P_cycle_reduction p hpvalid (by omega)).2.2.1.mp
      (by simpa [hplen] using hpmember)
    have hpav := hptests.1
    have hpone : p.getD 1 0 = 1 := by
      by_contra hnot
      have hpnd : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
      have hval (i : ℕ) (hi : i < h) : 1 ≤ p.getD i 0 ∧ p.getD i 0 ≤ h := by
        have hm : p.getD i 0 ∈ p := by
          rw [List.getD_eq_getElem _ 0 (by omega)]
          exact List.getElem_mem (by omega)
        obtain ⟨j, hj, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hm)
        omega
      have hinj (i j : ℕ) (hi : i < h) (hj : j < h)
          (heq : p.getD i 0 = p.getD j 0) : i = j := by
        rw [List.getD_eq_getElem _ 0 (by omega),
          List.getD_eq_getElem _ 0 (by omega)] at heq
        exact hpnd.getElem_inj_iff.mp heq
      have hsecondpos : 2 ≤ p.getD 1 0 := by have := hval 1 (by omega); omega
      have hfinal := ThetaIterateFirstScan.small_second_forces_final_pair p hpvalid
        (by omega) (by simpa [hplen] using hpfirst) hsecondpos
        (by simpa [hplen] using hpsecond) hpav hptests.2.2.1
      have hlast : p.getD (h - 1) 0 = h - 1 := by simpa [hplen] using hfinal.1
      have hpen : p.getD (h - 2) 0 = 1 := by simpa [hplen] using hfinal.2
      have hmapone : image p 1 = h := by simpa only [image, Nat.sub_self] using hpfirst
      have hmapmax : image p h = h - 1 := by simpa [image] using hlast
      have hmappen : image p (h - 1) = 1 := by
        simpa only [image, show h - 1 - 1 = h - 2 by omega] using hpen
      have hsplit : List.range h = 0 :: 1 :: 2 :: List.range' 3 (h - 3) := by
        rw [List.range_eq_range', show h = ((h - 3 + 1) + 1) + 1 by omega,
          List.range'_succ, List.range'_succ, List.range'_succ]
        rfl
      have hcyclemax : ThetaFixedDefs.cycleFrom p h = [h, h - 1, 1] := by
        have htwo : (image p)^[2] h = 1 := by
          simp only [show 2 = 1 + 1 from rfl, Function.iterate_succ_apply',
            Function.iterate_zero_apply, hmapmax, hmappen]
        have hthree : (image p)^[3] h = h := by
          rw [show 3 = 2 + 1 from rfl, Function.iterate_succ_apply', htwo, hmapone]
        unfold ThetaFixedDefs.cycleFrom
        rw [hplen, hsplit]
        simp only [List.map_cons, Nat.zero_add, Function.iterate_one,
          hmapmax, htwo, hthree]
        simp [show h - 1 ≠ h by omega, show 1 ≠ h by omega]
      have hcyclepen : ThetaFixedDefs.cycleFrom p (h - 1) = [h - 1, 1, h] := by
        have htwo : (image p)^[2] (h - 1) = h := by
          simp only [show 2 = 1 + 1 from rfl, Function.iterate_succ_apply',
            Function.iterate_zero_apply, hmappen, hmapone]
        have hthree : (image p)^[3] (h - 1) = h - 1 := by
          rw [show 3 = 2 + 1 from rfl, Function.iterate_succ_apply', htwo, hmapmax]
        unfold ThetaFixedDefs.cycleFrom
        rw [hplen, hsplit]
        simp only [List.map_cons, Nat.zero_add, Function.iterate_one,
          hmappen, htwo, hthree]
        simp [show 1 ≠ h - 1 by omega, show h ≠ h - 1 by omega]
      have hmiddle (x : ℕ) (hx : 2 ≤ x) (hxh : x ≤ h - 2) :
          2 ≤ image p x ∧ image p x ≤ h - 2 := by
        have hb := hval (x - 1) (by omega)
        have hneone : image p x ≠ 1 := by
          intro heq
          have hi := hinj (x - 1) (h - 2) (by omega) (by omega)
            (heq.trans hpen.symm)
          omega
        have hnemax : image p x ≠ h := by
          intro heq
          have hi := hinj (x - 1) 0 (by omega) (by omega) (heq.trans hpfirst.symm)
          omega
        have hnepen : image p x ≠ h - 1 := by
          intro heq
          have hi := hinj (x - 1) (h - 1) (by omega) (by omega) (heq.trans hlast.symm)
          omega
        change 2 ≤ p.getD (x - 1) 0 ∧ p.getD (x - 1) 0 ≤ h - 2
        dsimp [image] at hneone hnemax hnepen
        omega
      have hmiditerate (i : ℕ) :
          2 ≤ (image p)^[i] (h - 2) ∧ (image p)^[i] (h - 2) ≤ h - 2 := by
        induction i with
        | zero => simp; omega
        | succ i ih =>
            rw [Function.iterate_succ_apply']
            exact hmiddle _ ih.1 ih.2
      have hmidleader : ThetaFixedDefs.IsLeader p (h - 2) := by
        intro y hy
        unfold ThetaFixedDefs.cycleFrom at hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact le_refl _
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp
            ((List.takeWhile_sublist (fun y => decide (y ≠ h - 2))).subset hy)
          exact (hmiditerate (i + 1)).2
      have hmaxleader : ThetaFixedDefs.IsLeader p h := by
        unfold ThetaFixedDefs.IsLeader
        rw [hcyclemax]
        intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl <;> omega
      have hpenleader : ¬ ThetaFixedDefs.IsLeader p (h - 1) := by
        intro hlead
        have hm : h ∈ ThetaFixedDefs.cycleFrom p (h - 1) := by rw [hcyclepen]; simp
        have := hlead h hm
        omega
      let heads := (List.range' 1 (h - 2)).filter
        (fun x => decide (ThetaFixedDefs.IsLeader p x))
      let earlierCycles := heads.flatMap (ThetaFixedDefs.cycleFrom p)
      have htheta : ThetaFixedDefs.theta p = earlierCycles ++ [h, h - 1, 1] := by
        have hranges : List.range' 1 h = List.range' 1 (h - 2) ++ [h - 1, h] := by
          have hs := (List.range'_append_1 (s := 1) (m := h - 2) (n := 2)).symm
          simpa [show h - 2 + 2 = h by omega, List.range'_succ,
            show 1 + (h - 2) = h - 1 by omega,
            show h - 1 + 1 = h by omega] using hs
        unfold ThetaFixedDefs.theta
        rw [hplen, hranges, List.filter_append]
        simp only [List.filter_cons, hpenleader, decide_false, Bool.false_eq_true, if_false,
          hmaxleader, decide_true, if_true, List.filter_nil, List.flatMap_append,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, hcyclemax]
        rfl
      have hmidmem : h - 2 ∈ earlierCycles := by
        apply List.mem_flatMap.mpr
        refine ⟨h - 2, ?_, ?_⟩
        · apply List.mem_filter.mpr
          refine ⟨List.mem_range'.mpr ⟨h - 3, by omega, by omega⟩, ?_⟩
          exact decide_eq_true hmidleader
        · simp [ThetaFixedDefs.cycleFrom]
      have hpattern : [h - 2, h, h - 1].Sublist (ThetaFixedDefs.theta p) := by
        rw [htheta]
        have hs : [h - 2].Sublist earlierCycles := List.singleton_sublist.mpr hmidmem
        have ht : [h, h - 1].Sublist [h, h - 1, 1] := by simp
        exact hs.append ht
      apply hptests.2.1
      refine ⟨fun i => h - 3 + i, ?_, ?_, ?_, by simp⟩
      · intro i hi hik
        change h - 3 + i < h - 3 + (i + 1)
        omega
      · intro i hi hik
        have hcases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases hcases with rfl | rfl | rfl
        · exact hpattern.subset (by simp [show h - 3 + 1 = h - 2 by omega])
        · exact hpattern.subset (by simp [show h - 3 + 2 = h - 1 by omega])
        · exact hpattern.subset (by simp [show h - 3 + 3 = h by omega])
      · simpa only [List.map_cons, List.map_nil,
          show h - 3 + 1 = h - 2 by omega, show h - 3 + 3 = h by omega,
          show h - 3 + 2 = h - 1 by omega] using hpattern
    cases p with
    | nil => simp at hplen; omega
    | cons maximum tail =>
        simp only [List.getD_cons_zero] at hpfirst
        subst maximum
        have htaillen : tail.length = h - 1 := by simp only [List.length_cons] at hplen; omega
        have htailperm : tail.Perm (List.range' 1 (h - 1)) := by
          have heq := hp.trans hperm.symm
          change (h :: tail).Perm (h :: List.range' 1 (h - 1)) at heq
          exact heq.cons_inv
        have htailav : ¬ Contains [1, 3, 2] [] 3 tail := by
          rintro ⟨values, hvalues, hmem, hsub, harrows⟩
          apply hpav
          refine ⟨values, hvalues, ?_, ?_, by simp⟩
          · intro i hi hik
            exact List.mem_cons_of_mem h (hmem i hi hik)
          · exact hsub.trans (List.sublist_cons_self h tail)
        have hidentity := first_one_identity tail
          (by simpa [htaillen] using htailperm) htailav (by omega)
          (by simpa using hpone)
        change h :: tail = h :: List.range' 1 (h - 1)
        rw [hidentity, htaillen]
  · rintro rfl
    simpa only [r, hlen] using hmember

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateUFamilies
