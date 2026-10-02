/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateWTests
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateWTests
   mirror-E: none(waiver:forced-family-cycle-construction)
   anchors: []
   utility: none
   digest: Alternating reflections construct the avoiding cycle word of every W permutation. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateForcedWord
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycleReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateWTests

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArcherCyclicDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseBlocks
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycle
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateForcedWord
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycleReduction

local notation "B" =>
  (fun p : List ℕ => List.map (hat p) (List.range' 1 (List.length p)))

set_option maxHeartbeats 1200000 in
theorem W_tests (h : ℕ) (hh : 4 ≤ h) :
    (W h).Perm (List.range' 1 h) ∧
      ¬ Contains [1, 3, 2] [] 3 (W h) ∧
      ¬ Contains [1, 3, 2] [] 3 (b (W h)) ∧
      ¬ Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta (W h)) ∧
      P (W h) ∈ ThetaIterateDefs.iterateAvoiders (h + 2) 2 [1, 3, 2] := by
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
  let c := (h + 1) / 2
  let d := h - c
  let r := W h
  have hc : 2 ≤ c ∧ c ≤ h - 2 := by dsimp [c]; omega
  have hd : 2 ≤ d ∧ d ≤ c ∧ c ≤ d + 1 := by dsimp [d, c]; omega
  have hrlength : r.length = h := by
    simp only [r, W, List.length_append, List.length_reverse, List.length_range',
      List.length_singleton]
    omega
  have hrget (i : ℕ) (hi : i < h) :
      r.getD i 0 = if i < d then h - i else if i < h - 1 then h - 1 - i else c := by
    rw [List.getD_eq_getElem _ 0 (by omega)]
    by_cases hid : i < d
    · simp only [r, W, show (h + 1) / 2 = c from rfl, List.getElem_append,
        List.length_append, List.length_reverse, List.length_range', if_pos hid,
        dif_pos (by omega : i < (h - c) + (c - 1)),
        dif_pos (by omega : i < h - c), List.getElem_reverse, List.getElem_range'_1]
      omega
    · by_cases hifinal : i < h - 1
      · simp only [r, W, show (h + 1) / 2 = c from rfl, List.getElem_append,
          List.length_append, List.length_reverse, List.length_range', if_neg hid,
          if_pos hifinal, dif_pos (by omega : i < (h - c) + (c - 1)),
          dif_neg (by omega : ¬ i < h - c), List.getElem_reverse, List.getElem_range'_1]
        omega
      · have heq : i = h - 1 := by omega
        simp only [r, W, show (h + 1) / 2 = c from rfl, List.getElem_append,
          List.length_append, List.length_reverse, List.length_range', if_neg hid,
          if_neg hifinal, dif_neg (by omega : ¬ i < (h - c) + (c - 1))]
        have hz : i - ((h - c) + (c - 1)) = 0 := by omega
        simp only [hz, List.getElem_cons_zero]
  let g : ℕ → ℕ := fun i => if i = 0 then h else
    if i % 2 = h % 2 then c + i / 2 else c - i / 2
  let q := (List.range h).map g
  have hqlength : q.length = h := by simp [q]
  have hqget (i : ℕ) (hi : i < h) : q.getD i 0 = g i := by
    rw [List.getD_eq_getElem _ 0 (by omega)]
    simp [q]
  have hgbound (i : ℕ) (hi : i < h) : 1 ≤ g i ∧ g i ≤ h := by
    dsimp [g]
    split_ifs <;> dsimp [c] at * <;> omega
  have hgsmall (i : ℕ) (hi : 0 < i) (hih : i < h) : g i < h := by
    dsimp [g]
    split_ifs <;> dsimp [c] at * <;> omega
  have hginj : Set.InjOn g {i | i < h} := by
    intro i hi j hj hij
    change i < h at hi
    change j < h at hj
    dsimp [g] at hij
    split_ifs at hij <;> dsimp [c] at * <;> omega
  have hqnd : q.Nodup := by
    apply List.nodup_range.map_on
    intro i hi j hj heq
    exact hginj (List.mem_range.mp hi) (List.mem_range.mp hj) heq
  let pos : ℕ → ℕ := fun x => if x = h then 0 else if h % 2 = 0 then
    if x ≤ c then 2 * (c - x) + 1 else 2 * (x - c)
    else if x < c then 2 * (c - x) else 2 * (x - c) + 1
  have hpos (x : ℕ) (hx : 1 ≤ x) (hxh : x ≤ h) : pos x < h ∧ g (pos x) = x := by
    constructor
    · dsimp [pos]
      split_ifs <;> dsimp [c] at * <;> omega
    · dsimp [g, pos]
      split_ifs <;> dsimp [c] at * <;> omega
  have hqperm : q.Perm (List.range' 1 h) := by
    apply (List.perm_ext_iff_of_nodup hqnd List.nodup_range').mpr
    intro x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hb := hgbound i (List.mem_range.mp hi)
      exact List.mem_range'.mpr ⟨g i - 1, by omega, by omega⟩
    · intro hx
      obtain ⟨i, hi, heq⟩ := List.mem_range'.mp hx
      have hxpos : 1 ≤ x := by omega
      have hxle : x ≤ h := by omega
      exact List.mem_map.mpr ⟨pos x, List.mem_range.mpr (hpos x hxpos hxle).1,
        (hpos x hxpos hxle).2⟩
  have hqidx (x : ℕ) (hx : 1 ≤ x) (hxh : x ≤ h) : q.idxOf x = pos x := by
    have hb := hpos x hx hxh
    have hg := hqget (pos x) hb.1
    have hget : q[pos x] = x := by
      rw [← List.getD_eq_getElem _ 0 (by omega)]
      exact hg.trans hb.2
    have heq := List.get_idxOf hqnd ⟨pos x, by omega⟩
    change q.idxOf q[pos x] = pos x at heq
    rwa [hget] at heq
  have hqfirst : q.getD 0 0 = h := by rw [hqget 0 (by omega)]; simp [g]
  have hqmax : ∀ x ∈ q, x ≤ q.getD 0 0 := by
    intro x hx
    rw [hqfirst]
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact (hgbound i (List.mem_range.mp hi)).2
  have hrhat (x : ℕ) (hx : 1 ≤ x) (hxh : x ≤ h) : image r x = hat q x := by
    have hxmem : x ∈ q := hqperm.mem_iff.mpr
      (List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩)
    rw [hat_one_block q hqmax x hxmem, hqidx x hx hxh, hqlength]
    change r.getD (x - 1) 0 = _
    rw [hrget (x - 1) (by omega)]
    by_cases hnext : pos x + 1 < h
    · rw [if_pos hnext, hqget (pos x + 1) hnext]
      dsimp [g, pos, d] at *
      split_ifs <;> dsimp [c] at * <;> omega
    · rw [if_neg hnext, hqfirst]
      dsimp [pos, d] at *
      split_ifs at * <;> dsimp [c] at * <;> omega
  have hrB : r = B q := by
    apply List.ext_getElem
    · simp [hrlength, hqlength]
    · intro i hi₁ hi₂
      have hi : i < h := by omega
      rw [← List.getD_eq_getElem _ 0 hi₁]
      simp only [List.getElem_map, List.getElem_range'_1]
      have heq := hrhat (1 + i) (by omega) (by omega)
      change r.getD (1 + i - 1) 0 = hat q (1 + i) at heq
      simpa using heq
  have hrperm : r.Perm (List.range' 1 h) := by
    have hreverse := (List.reverse_perm (List.range' (c + 1) d)).append
      ((List.reverse_perm (List.range' 1 (c - 1))).append (List.Perm.refl [c]))
    have hrshape : r =
        (List.range' (c + 1) d).reverse ++ (List.range' 1 (c - 1)).reverse ++ [c] := rfl
    rw [hrshape, List.append_assoc]
    apply hreverse.trans
    have hswap : (List.range' (c + 1) d ++ (List.range' 1 (c - 1) ++ [c])).Perm
        ((List.range' 1 (c - 1) ++ [c]) ++ List.range' (c + 1) d) := List.perm_append_comm
    apply hswap.trans
    have hconcat : List.range' 1 (c - 1) ++ [c] = List.range' 1 c := by
      have heq := List.range'_concat (s := 1) (n := c - 1) (step := 1)
      simpa only [Nat.one_mul, show 1 + (c - 1) = c by omega,
        show c - 1 + 1 = c by omega] using heq.symm
    rw [hconcat]
    have hrange : List.range' 1 c ++ List.range' (c + 1) d = List.range' 1 h := by
      simpa only [Nat.one_mul, Nat.add_comm 1 c, show c + d = h by omega] using
        (List.range'_append (s := 1) (m := c) (n := d) (step := 1))
    rw [hrange]
  have hqcycle : ThetaFixedDefs.cycleFrom (B q) h = q := by
    have hvalid : q.Perm (List.range' 1 q.length) := by simpa [hqlength] using hqperm
    have heq := cycleFrom_B_record_block q hvalid 0 h (by omega) (by omega)
      (by intro i hi; omega)
      (by
        intro i hi hih hrec
        have hgt := hrec 0 hi
        rw [hqfirst, hqget i hih] at hgt
        have := hgbound i hih
        omega) (Or.inl hqlength.symm)
    rw [hqfirst, List.drop_zero, Nat.sub_zero, List.take_of_length_le (by omega)] at heq
    exact heq
  have htheta : ThetaFixedDefs.theta r = q := by
    rw [hrB]
    unfold ThetaFixedDefs.theta
    have hBlen : (B q).length = h := by simp [hqlength]
    rw [hBlen]
    have hleaders (x : ℕ) (hx : x ∈ List.range' 1 h) :
        ThetaFixedDefs.IsLeader (B q) x ↔ x = h := by
      obtain ⟨i, hi, heq⟩ := List.mem_range'.mp hx
      have hxmem : x ∈ q := hqperm.mem_iff.mpr (List.mem_range'.mpr ⟨i, hi, heq⟩)
      constructor
      · intro hlead
        by_contra hnot
        apply nonrecord_not_B_leader q (by simpa [hqlength] using hqperm) x hxmem _ hlead
        intro hrec
        have hidxpos : 0 < q.idxOf x := by
          have hidxbound := List.idxOf_lt_length_of_mem hxmem
          have hxget : q.getD (q.idxOf x) 0 = x := by
            rw [List.getD_eq_getElem _ 0 hidxbound]
            exact List.getElem_idxOf hidxbound
          by_contra hnotpos
          have hzero : q.idxOf x = 0 := by omega
          rw [hzero, hqfirst] at hxget
          omega
        have hlt := hrec 0 hidxpos
        have hidxbound := List.idxOf_lt_length_of_mem hxmem
        have hbound := hgbound (q.idxOf x) (by omega)
        rw [hqfirst, hqget _ (by omega)] at hlt
        omega
      · intro heqx
        rw [heqx, ThetaFixedDefs.IsLeader, hqcycle]
        simpa only [hqfirst] using hqmax
    have hfilter : (List.range' 1 h).filter
        (fun x => decide (ThetaFixedDefs.IsLeader (B q) x)) = [h] := by
      have heq : (List.range' 1 h).filter
          (fun x => decide (ThetaFixedDefs.IsLeader (B q) x)) =
          (List.range' 1 h).filter (fun x => decide (x = h)) := by
        apply List.filter_congr
        intro x hx
        simp only [hleaders x hx]
      rw [heq, List.filter_eq]
      have hhm : h ∈ List.range' 1 h :=
        List.mem_range'.mpr ⟨h - 1, by omega, by omega⟩
      rw [(List.nodup_iff_count_eq_one.mp List.nodup_range') h hhm]
      simp
    rw [hfilter]
    simpa using hqcycle
  have hravoid : ¬ Contains [1, 3, 2] [] 3 r := by
    intro hcontains
    obtain ⟨i, j, k, hij, hjk, hik, hkj⟩ := (contains132_iff_indices r).mp hcontains
    have hi : i.val < h := by omega
    have hj : j.val < h := by omega
    have hk : k.val < h := by omega
    rw [← List.getD_eq_getElem _ 0 i.isLt, ← List.getD_eq_getElem _ 0 k.isLt,
      hrget i.val hi, hrget k.val hk] at hik
    rw [← List.getD_eq_getElem _ 0 k.isLt, ← List.getD_eq_getElem _ 0 j.isLt,
      hrget k.val hk, hrget j.val hj] at hkj
    change i.val < j.val at hij
    change j.val < k.val at hjk
    split_ifs at hik hkj <;> omega
  have hqavoid : ¬ Contains [1, 3, 2] [] 3 q := by
    intro hcontains
    obtain ⟨i, j, k, hij, hjk, hik, hkj⟩ := (contains132_iff_indices q).mp hcontains
    have hi : i.val < h := by omega
    have hj : j.val < h := by omega
    have hk : k.val < h := by omega
    rw [← List.getD_eq_getElem _ 0 i.isLt, ← List.getD_eq_getElem _ 0 k.isLt,
      hqget i.val hi, hqget k.val hk] at hik
    rw [← List.getD_eq_getElem _ 0 k.isLt, ← List.getD_eq_getElem _ 0 j.isLt,
      hqget k.val hk, hqget j.val hj] at hkj
    change i.val < j.val at hij
    change j.val < k.val at hjk
    dsimp [g] at hik hkj
    split_ifs at hik hkj <;> dsimp [c] at * <;> omega
  have hbavoid : ¬ Contains [1, 3, 2] [] 3 (b r) := by
    have hrnd : r.Nodup := hrperm.nodup_iff.mpr List.nodup_range'
    let loc : ℕ → ℕ := fun x => if x = c then h - 1
      else if c < x then h - x else h - 1 - x
    have hloc (x : ℕ) (hx : 1 ≤ x) (hxh : x ≤ h) :
        loc x < h ∧ r.getD (loc x) 0 = x := by
      constructor
      · dsimp [loc]
        split_ifs <;> omega
      · rw [hrget _ (by dsimp [loc]; split_ifs <;> omega)]
        dsimp [loc, d] at *
        split_ifs <;> omega
    have hidx (x : ℕ) (hx : 1 ≤ x) (hxh : x ≤ h) : r.idxOf x = loc x := by
      have hb := hloc x hx hxh
      have hget : r[loc x] = x := by
        rw [← List.getD_eq_getElem _ 0 (by omega)]
        exact hb.2
      have heq := List.get_idxOf hrnd ⟨loc x, by omega⟩
      change r.idxOf r[loc x] = loc x at heq
      rwa [hget] at heq
    have hblength : (b r).length = h := by simp [b, hrlength]
    have hbget (i : ℕ) (hi : i < h) : (b r).getD i 0 =
        if i = 0 then c + 1 else if i = c - 1 then 1 else if i = c then c else i + 1 := by
      rw [List.getD_eq_getElem _ 0 (by omega)]
      simp only [b, List.getElem_map, List.getElem_range'_1]
      rw [hidx (1 + i) (by omega) (by omega), hrlength]
      by_cases hnext : loc (1 + i) + 1 < h
      · rw [if_pos hnext, hrget _ hnext]
        dsimp [loc, d] at hnext ⊢
        split_ifs at hnext ⊢ <;> omega
      · rw [if_neg hnext]
        dsimp [loc] at hnext ⊢
        split_ifs at hnext ⊢ <;> omega
    intro hcontains
    obtain ⟨i, j, k, hij, hjk, hik, hkj⟩ :=
      (contains132_iff_indices (b r)).mp hcontains
    have hi : i.val < h := by omega
    have hj : j.val < h := by omega
    have hk : k.val < h := by omega
    rw [← List.getD_eq_getElem _ 0 i.isLt, ← List.getD_eq_getElem _ 0 k.isLt,
      hbget i.val hi, hbget k.val hk] at hik
    rw [← List.getD_eq_getElem _ 0 k.isLt, ← List.getD_eq_getElem _ 0 j.isLt,
      hbget k.val hk, hbget j.val hj] at hkj
    change i.val < j.val at hij
    change j.val < k.val at hjk
    split_ifs at hik hkj <;> omega
  have hθavoid : ¬ Contains [1, 3, 2] [] 3 (ThetaFixedDefs.theta r) := by
    rw [htheta]
    exact hqavoid
  have hrvalid : r.Perm (List.range' 1 r.length) := by
    simpa only [hrlength] using hrperm
  have hfirst : r.getD 0 0 = r.length := by
    rw [hrget 0 (by omega), if_pos (by omega), hrlength]
    omega
  have hcross : ∀ i j, i < j → j < r.length →
      ¬ ((b r).getD i 0 < r.getD 0 0 + 1 ∧
        r.getD 0 0 + 1 < (b r).getD j 0) := by
    have hbperm := b_perm_of_first_max r hrvalid hfirst
    intro i j hij hj hpair
    have hblength : (b r).length = r.length := by simp [b]
    have hm : (b r).getD j 0 ∈ b r := by
      rw [List.getD_eq_getElem _ 0 (by omega)]
      exact List.getElem_mem (by omega)
    obtain ⟨index, hindex, heq⟩ := List.mem_range'.mp (hbperm.mem_iff.mp hm)
    rw [hfirst] at hpair
    omega
  have hmember := (P_cycle_reduction r hrvalid (by omega)).2.2.1.mpr
    ⟨hravoid, hθavoid, hbavoid, hcross⟩
  refine ⟨hrperm, hravoid, hbavoid, hθavoid, ?_⟩
  simpa only [hrlength] using hmember

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateWTests
