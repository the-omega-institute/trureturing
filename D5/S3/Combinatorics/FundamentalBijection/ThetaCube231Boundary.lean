/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaCube231Boundary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaCube231Boundary
   mirror-E: none(waiver:231-cube-terminal-value)
   anchors: [mathlib/module/Mathlib.Data.List.Sort]
   utility: none
   digest: The terminal value of a large fixed indecomposable 231-avoider is next to maximum. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Pair
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube231ForcedPrefix
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Prefix
import Mathlib.Data.List.Sort
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Middle
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseTail
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicSumIndecomp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Boundary

local notation "B" =>
  (fun p : List ℕ =>
    List.map (D5.S3.Combinatorics.ArrowWilfDefs.hat p)
      (List.range' 1 (List.length p)))

open D5.S3.Combinatorics.ArrowWilfDefs
open ThetaBasicInverse
open ThetaBasicInverseTail
open ThetaBasicSumIndecomp
open ThetaCube231Pair
open ThetaCube231ForcedPrefix
open ThetaCube231Middle

open ThetaBasicInverse ThetaCube231Prefix

theorem terminal_value_next_to_max (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length)) (hn : 3 < p.length)
    (hindecomp : ∀ k, 0 < k → k < p.length →
      ∃ x ∈ p.take k, k < x)
    (havoid : ¬ Contains [2, 3, 1] [] 3 p)
    (hfixed : B (B (B p)) = p) :
    p.getD (p.length - 1) 0 = p.length - 1 ∧
      p.getD 1 0 = 1 := by
  have hat_one_block (p : List ℕ) (hmax : ∀ y ∈ p, y ≤ p.getD 0 0)
      (x : ℕ) (hx : x ∈ p) :
      hat p x = if p.idxOf x + 1 < p.length then p.getD (p.idxOf x + 1) 0
        else p.getD 0 0 := by
    have hnonrecord (i : ℕ) (hi : 0 < i) (hil : i < p.length) :
        ¬ IsLtrMax p i := by
      intro hrecord
      have hmem : p.getD i 0 ∈ p := by
        rw [List.getD_eq_getElem _ 0 hil]
        exact List.getElem_mem hil
      exact (not_lt_of_ge (hmax _ hmem)) (hrecord 0 hi)
    have hgreatest (i : ℕ) (hi : i < p.length) :
        Nat.findGreatest (IsLtrMax p) i = 0 := by
      induction i with
      | zero => rfl
      | succ j ih =>
          rw [Nat.findGreatest_succ, if_neg (hnonrecord (j + 1) (by omega) hi)]
          exact ih (by omega)
    have hidx : p.idxOf x < p.length := List.idxOf_lt_length_of_mem hx
    unfold hat
    dsimp only
    by_cases hnext : p.idxOf x + 1 < p.length
    · rw [if_pos ⟨hnext, hnonrecord _ (by omega) hnext⟩, if_pos hnext]
    · rw [if_neg (fun h => hnext h.1), if_neg hnext, hgreatest _ hidx]
  have B_recordStaircase (n : ℕ) (hn : 1 < n) :
      B (List.range' 2 (n - 1) ++ [1]) =
        n :: (List.range' 2 (n - 2) ++ [1]) := by
    let p := List.range' 2 (n - 1) ++ [1]
    have hlen : p.length = n := by simp [p]; omega
    have hget (i : ℕ) (hi : i < n) :
        p.getD i 0 = if i < n - 1 then i + 2 else 1 := by
      rw [List.getD_eq_getElem _ 0 (by simpa [hlen] using hi)]
      change (List.range' 2 (n - 1) ++ [1])[i] = _
      rw [List.getElem_append]
      by_cases hfirst : i < n - 1
      · simp [hfirst]
        omega
      · have hieq : i = n - 1 := by omega
        simp [hfirst, hieq]
    have hnot : 1 ∉ List.range' 2 (n - 1) := by
      intro h
      obtain ⟨j, _, heq⟩ := List.mem_range'.mp h
      omega
    have hnodup : p.Nodup := by
      apply List.nodup_append.mpr
      refine ⟨List.nodup_range', by simp, ?_⟩
      intro x hx y hy heq
      simp only [List.mem_singleton] at hy
      have hxone : x = 1 := heq.trans hy
      exact hnot (hxone ▸ hx)
    have hrecord (i : ℕ) (hi : i < n - 1) :
        D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p i := by
      intro j hj
      rw [hget j (by omega), hget i (by omega)]
      simp only [if_pos (by omega : j < n - 1), if_pos hi]
      omega
    have hlastNot :
        ¬ D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p (n - 1) := by
      intro hr
      have h := hr 0 (by omega : 0 < n - 1)
      rw [hget 0 (by omega), hget (n - 1) (by omega)] at h
      simp [hn] at h
    have hfgLast : Nat.findGreatest
        (D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p) (n - 1) = n - 2 := by
      have hlo := Nat.le_findGreatest (by omega : n - 2 ≤ n - 1)
        (hrecord (n - 2) (by omega))
      have hhi := Nat.findGreatest_le
        (P := D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p) (n - 1)
      by_contra hne
      have heq : Nat.findGreatest
          (D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p) (n - 1) = n - 1 := by
        omega
      apply hlastNot
      rw [← heq]
      exact Nat.findGreatest_spec (by omega : n - 2 ≤ n - 1)
        (hrecord (n - 2) (by omega))
    apply List.ext_getElem
    · simp [p]
      omega
    · intro i hi hi'
      have hin : i < n := by
        have h := hi
        simp at h
        omega
      have hmem : i + 1 ∈ p := by
        by_cases hz : i = 0
        · subst i
          simp [p]
        · have hr : i + 1 ∈ List.range' 2 (n - 1) :=
            List.mem_range'.mpr ⟨i - 1, by omega, by omega⟩
          simp [p, hr]
      have hidx : p.idxOf (i + 1) = if i = 0 then n - 1 else i - 1 := by
        by_cases hz : i = 0
        · subst i
          rw [if_pos rfl]
          have hpos : n - 1 < p.length := by omega
          have hval : p[n - 1] = 1 := by
            rw [← List.getD_eq_getElem _ 0 hpos, hget (n - 1) (by omega)]
            simp
          have h := hnodup.idxOf_getElem (i := n - 1) hpos
          rw [hval] at h
          simpa using h
        · rw [if_neg hz]
          have hpos : i - 1 < p.length := by omega
          have hval : p[i - 1] = i + 1 := by
            rw [← List.getD_eq_getElem _ 0 hpos, hget (i - 1) (by omega)]
            have : i - 1 < n - 1 := by omega
            simp [this]
            omega
          have h := hnodup.idxOf_getElem (i := i - 1) hpos
          rw [hval] at h
          exact h
      have hleft : (B p)[i] = D5.S3.Combinatorics.ArrowWilfDefs.hat p (i + 1) := by
        simp [Nat.add_comm]
      have hright : (n :: (List.range' 2 (n - 2) ++ [1]))[i] =
          if i = 0 then n else if i + 1 = n then 1 else i + 1 := by
        cases i with
        | zero => simp
        | succ j =>
          simp only [List.getElem_cons_succ]
          rw [List.getElem_append]
          by_cases hlast : j + 2 = n
          · have hieq : j = n - 2 := by omega
            simp [hieq]
            omega
          · have hlt : j < n - 2 := by omega
            have hnot : 1 + (j + 1) ≠ n := by omega
            simp [hlt, hnot, Nat.add_comm, Nat.add_assoc]
            omega
      change (B p)[i] = (n :: (List.range' 2 (n - 2) ++ [1]))[i]
      rw [hleft, hright]
      unfold D5.S3.Combinatorics.ArrowWilfDefs.hat
      rw [hidx]
      by_cases hz : i = 0
      · subst i
        have hnlt : ¬ n - 1 + 1 < p.length := by omega
        simp only [Nat.zero_add, ite_true]
        have hncondition : ¬ (n - 1 + 1 < p.length ∧
            ¬ D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p (n - 1 + 1)) :=
          fun h => hnlt h.1
        rw [if_neg hncondition, hfgLast, hget (n - 2) (by omega)]
        simp [show n - 2 < n - 1 by omega]
        omega
      · simp only [if_neg hz]
        by_cases hlast : i + 1 = n
        · have hieq : i = n - 1 := by omega
          have hnext : i - 1 + 1 < p.length := by omega
          have hnrec : ¬ D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p
              (i - 1 + 1) := by simpa [hieq, show n - 1 - 1 + 1 = n - 1 by omega]
              using hlastNot
          rw [if_pos ⟨hnext, hnrec⟩, hget (i - 1 + 1) (by omega)]
          have hval : i - 1 + 1 = n - 1 := by omega
          simp [hval, hlast]
        · have hnext : i - 1 + 1 < p.length := by omega
          have hrec : D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p
              (i - 1 + 1) := by
            apply hrecord
            omega
          rw [if_neg (by simp [hrec]), Nat.findGreatest_eq
            (hrecord (i - 1) (by omega)), hget (i - 1) (by omega)]
          simp [hlast, show i - 1 < n - 1 by omega]
          omega
  have B_descending (n : ℕ) (hn : 0 < n) :
      B ((List.range' 1 n).reverse) = n :: List.range' 1 (n - 1) := by
    let p := (List.range' 1 n).reverse
    have hlen : p.length = n := by simp [p]
    have hget (i : ℕ) (hi : i < n) : p.getD i 0 = n - i := by
      rw [List.getD_eq_getElem _ 0 (by simpa [p] using hi)]
      change (List.range' 1 n).reverse[i] = n - i
      rw [List.getElem_reverse]
      simp only [List.length_range']
      rw [List.getElem_range'_1]
      omega
    have hmax : ∀ y ∈ p, y ≤ p.getD 0 0 := by
      intro y hy
      have hy' : y ∈ List.range' 1 n := by simpa [p] using hy
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp hy'
      rw [hget 0 hn]
      omega
    have hnodup : p.Nodup := by
      exact List.nodup_reverse.mpr (show (List.range' 1 n).Nodup from List.nodup_range')
    apply List.ext_getElem
    · simp [p]
      omega
    · intro i hi hi'
      have hin : i < n := by simpa [hlen] using hi
      have hidxval : p.getD (n - (i + 1)) 0 = i + 1 := by
        apply (hget (n - (i + 1)) (by omega)).trans
        omega
      have hidx : p.idxOf (i + 1) = n - (i + 1) := by
        have hpos : n - (i + 1) < p.length := by omega
        have hval : p[n - (i + 1)] = i + 1 := by
          simpa only [List.getD_eq_getElem _ 0 hpos] using hidxval
        have h := hnodup.idxOf_getElem (i := n - (i + 1)) hpos
        rw [hval] at h
        exact h
      have hmem : i + 1 ∈ p := by
        have hr : i + 1 ∈ List.range' 1 n :=
          List.mem_range'.mpr ⟨i, hin, by omega⟩
        simpa [p] using hr
      have hleft : (B p)[i] = D5.S3.Combinatorics.ArrowWilfDefs.hat p (i + 1) := by
        simp [Nat.add_comm]
      have hright : (n :: List.range' 1 (n - 1))[i] =
          if i = 0 then n else i := by
        cases i with
        | zero => simp
        | succ j => simp [Nat.add_comm]
      change (B p)[i] = (n :: List.range' 1 (n - 1))[i]
      rw [hleft, hright, hat_one_block p hmax (i + 1) hmem, hidx]
      by_cases hz : i = 0
      · subst i
        have hlast : n - 1 + 1 = n := by omega
        rw [hlast, if_neg (by omega : ¬ n < p.length), if_pos rfl]
        exact hget 0 hn
      · have hnext : n - (i + 1) + 1 < p.length := by omega
        rw [if_pos hnext, if_neg hz]
        have harg : n - (i + 1) + 1 = n - i := by omega
        rw [harg, hget (n - i) (by omega)]
        omega
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
  have B_successorWord (n : ℕ) (hn : 1 < n) :
      B (n :: List.range' 1 (n - 1)) = List.range' 2 (n - 1) ++ [1] := by
    let p := n :: List.range' 1 (n - 1)
    have hlen : p.length = n := by simp [p]; omega
    have hget (i : ℕ) (hi : i < n) : p.getD i 0 = if i = 0 then n else i := by
      cases i with
      | zero => simp [p]
      | succ j =>
          have hj : j < n - 1 := by omega
          rw [List.getD_eq_getElem _ 0 (by simpa [hlen] using hi)]
          simp [p, List.getElem_range'_1, Nat.add_comm]
    have hmax : ∀ y ∈ p, y ≤ p.getD 0 0 := by
      intro y hy
      have hzero : p.getD 0 0 = n := by simpa using hget 0 (by omega)
      rw [hzero]
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · obtain ⟨a, ha, heq⟩ := List.mem_range'.mp hy
        omega
    have hnodup : p.Nodup := by
      have hnnot : n ∉ List.range' 1 (n - 1) := by
        intro h
        obtain ⟨a, ha, heq⟩ := List.mem_range'.mp h
        omega
      exact List.nodup_cons.mpr ⟨hnnot, List.nodup_range'⟩
    apply List.ext_getElem
    · simp [p]
    · intro i hi hi'
      have hin : i < n := by
        have h := hi
        simp at h
        omega
      have hmem : i + 1 ∈ p := by
        by_cases hlast : i + 1 = n
        · simp [p, hlast]
        · have hr : i + 1 ∈ List.range' 1 (n - 1) :=
            List.mem_range'.mpr ⟨i, by omega, by omega⟩
          simp [p, hr]
      have hidx : p.idxOf (i + 1) = if i + 1 = n then 0 else i + 1 := by
        by_cases hlast : i + 1 = n
        · rw [if_pos hlast]
          have hval : p[0] = i + 1 := by simp [p, hlast]
          have h := hnodup.idxOf_getElem (i := 0) (by simp [p])
          rw [hval] at h
          exact h
        · rw [if_neg hlast]
          have hpos : i + 1 < p.length := by omega
          have hval : p[i + 1] = i + 1 := by
            rw [← List.getD_eq_getElem _ 0 hpos, hget (i + 1) (by omega)]
            simp [hlast]
          have h := hnodup.idxOf_getElem (i := i + 1) hpos
          rw [hval] at h
          exact h
      have hleft : (B p)[i] = D5.S3.Combinatorics.ArrowWilfDefs.hat p (i + 1) := by
        simp [Nat.add_comm]
      have hright : (List.range' 2 (n - 1) ++ [1])[i] =
          if i + 1 = n then 1 else i + 2 := by
        rw [List.getElem_append]
        by_cases hlast : i + 1 = n
        · have hieq : i = n - 1 := by omega
          simp [hieq]
          omega
        · have hlt : i < n - 1 := by omega
          simp [hlt, hlast]
          omega
      change (B p)[i] = (List.range' 2 (n - 1) ++ [1])[i]
      rw [hleft, hright, hat_one_block p hmax (i + 1) hmem, hidx]
      by_cases hlast : i + 1 = n
      · simp only [if_pos hlast]
        have hnext : 1 < p.length := by omega
        simp [hnext, hget 1 (by omega)]
        simp [p]
      · simp only [if_neg hlast]
        have hnext : i + 1 + 1 < p.length ∨ i + 1 + 1 = p.length := by omega
        rcases hnext with hnext | hnext
        · rw [if_pos hnext, hget (i + 2) (by omega)]
          simp
        · rw [if_neg (by omega : ¬ i + 1 + 1 < p.length), hget 0 (by omega)]
          simp
          omega
  have avoid231_last_one_descending (p : List ℕ)
      (hp : p.Perm (List.range' 1 p.length)) (hn : 0 < p.length)
      (hlast : p.getD (p.length - 1) 0 = 1)
      (havoid : ¬ D5.S3.Combinatorics.ArrowWilfDefs.Contains [2, 3, 1] [] 3 p) :
      p = (List.range' 1 p.length).reverse := by
    have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
    have h1mem : 1 ∈ p := hp.mem_iff.mpr
      (List.mem_range'.mpr ⟨0, hn, by omega⟩)
    have hidx : p.idxOf 1 = p.length - 1 := by
      have hi : p.idxOf 1 < p.length := List.idxOf_lt_length_of_mem h1mem
      have hlastlt : p.length - 1 < p.length := by omega
      have heq : p[p.idxOf 1] = p[p.length - 1] := by
        rw [List.getElem_idxOf hi]
        simpa only [List.getD_eq_getElem _ 0 hlastlt] using hlast.symm
      exact (hnodup.getElem_inj_iff).mp heq
    have hsorted : p.SortedGT := by
      apply List.sortedGT_iff_getElem_gt_getElem_of_lt.mpr
      intro i j hi hj hji
      by_cases hilast : i = p.length - 1
      · subst i
        have hjgt : 1 < p[j] := by
          have hm : p[j] ∈ p := List.getElem_mem hj
          obtain ⟨t, _, ht⟩ := List.mem_range'.mp (hp.mem_iff.mp hm)
          have hne : p[j] ≠ p[p.length - 1] := by
            intro heq
            have := (hnodup.getElem_inj_iff).mp heq
            omega
          have hlast' : p[p.length - 1] = 1 := by
            exact (List.getD_eq_getElem p 0 (by omega)).symm.trans hlast
          rw [hlast'] at hne
          omega
        have hlast' : p[p.length - 1] = 1 := by
          exact (List.getD_eq_getElem p 0 (by omega)).symm.trans hlast
        rw [hlast']
        exact hjgt
      · have hilt : i < p.idxOf 1 := by omega
        have hdecrease := avoid231_prefix_before_one_decreasing p hp hn havoid j i hji hilt
        simpa only [List.getD_eq_getElem _ 0 hi,
          List.getD_eq_getElem _ 0 hj] using hdecrease
    have hrange : (List.range' 1 p.length).SortedLT :=
      List.sortedLT_range' 1 p.length (s := 1) (by decide)
    exact List.SortedGT.eq_reverse_of_mem_iff_of_sortedLT
      (fun a => hp.mem_iff) hsorted hrange
  let n := p.length
  let q := B p
  let r := B q
  have hfirst : p.getD 0 0 = n :=
    (avoid231_indecomp_iff_first_max p hp (by omega) havoid).mp hindecomp
  have hpnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hqperm : q.Perm (List.range' 1 n) := by
    dsimp [q, n]
    exact B_perm p hp
  have hqlen : q.length = n := by simp [q, n]
  have hqperm' : q.Perm (List.range' 1 q.length) := by
    rw [hqlen]
    exact hqperm
  have hrperm : r.Perm (List.range' 1 n) := by
    dsimp [r]
    simpa [hqlen] using B_perm q hqperm'
  have hrlen : r.length = n := by simp [r, hqlen]
  have hrperm' : r.Perm (List.range' 1 r.length) := by
    rw [hrlen]
    exact hrperm
  have hpr : B r = p := by simpa [r, q] using hfixed
  have hrlast : r.getD (n - 1) 0 = 1 := by
    have hBrfirst : (B r).getD 0 0 = r.length := by
      rw [hpr, hrlen]
      exact hfirst
    have hh := B_first_max_forces_last_one r hrperm' (by rw [hrlen]; omega)
      hBrfirst
    simpa [hrlen] using hh
  let c := p.getD (n - 1) 0
  have hcpos : 0 < c := by
    have hm : c ∈ p := by
      dsimp [c]
      rw [List.getD_eq_getElem _ 0 (by omega : n - 1 < p.length)]
      exact List.getElem_mem (by omega : n - 1 < p.length)
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hm)
    omega
  have hpair := terminal_inverse_edge_forces_pair p hp (by omega) hfirst c
    (by rfl) (by simpa [r, q] using hrlast)
  have hclt : c < n := hpair.1
  obtain ⟨t, ht, htval, htone⟩ := hpair.2
  by_cases hc1 : c = 1
  · have hlastone : p.getD (p.length - 1) 0 = 1 := by simpa [c, n] using hc1
    have hdesc := avoid231_last_one_descending p hp (by omega) hlastone havoid
    have hfixed' : B (B (B ((List.range' 1 n).reverse))) =
        (List.range' 1 n).reverse := by
      have hh := hfixed
      rw [hdesc] at hh
      simpa [n] using hh
    rw [B_descending n (by omega), B_successorWord n (by omega),
      B_recordStaircase n (by omega)] at hfixed'
    have hsecond := congrArg (fun l : List ℕ => l.getD 1 0) hfixed'
    have hleft : (n :: (List.range' 2 (n - 2) ++ [1])).getD 1 0 = 2 := by
      rw [List.getD_eq_getElem _ 0 (by simp)]
      simp [show 0 < n - 2 by omega]
    have hright : ((List.range' 1 n).reverse).getD 1 0 = n - 1 := by
      rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_reverse]
      simp only [List.length_range', List.getElem_range'_1]
      omega
    rw [hleft, hright] at hsecond
    omega
  have hcge : 2 ≤ c := by omega
  have hu : t + 1 < n - 1 := by
    have hne : t + 1 ≠ n - 1 := by
      intro he
      rw [he] at htone
      have hv : p.getD (n - 1) 0 = c := by rfl
      rw [hv] at htone
      omega
    omega
  have hprefix := forced_high_prefix p hp havoid (t + 1) c
    (by omega) (by simpa [n] using hu) htone
    (by simpa only [show t + 1 - 1 = t by omega] using htval)
    (by rfl)
  by_cases hcm : c = n - 1
  · have htzero : t = 0 := by
      have htv : p.getD t 0 = n := by rw [htval, hcm]; omega
      have helem : p[t] = p[0] := by
        rw [← List.getD_eq_getElem _ 0 (by omega : t < p.length),
          ← List.getD_eq_getElem _ 0 (by omega : 0 < p.length),
          htv, hfirst]
      exact (hpnodup.getElem_inj_iff).mp helem
    constructor
    · simpa [c, n] using hcm
    · simpa [htzero] using htone
  have hcmid : c < n - 1 := by omega
  have hmaxp : ∀ y ∈ p, y ≤ p.getD 0 0 := by
    intro y hy
    rw [hfirst]
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hy)
    omega
  have hB_at (x : ℕ) (hx : 0 < x) (hle : x ≤ n) :
      q.getD (x - 1) 0 = hat p x := by
    rw [List.getD_eq_getElem _ 0 (by simp [q, n]; omega)]
    simp only [q, List.getElem_map, List.getElem_range'_1]
    congr 1
    omega
  have hcmem : c ∈ p := hp.mem_iff.mpr
    (List.mem_range'.mpr ⟨c - 1, by omega, by omega⟩)
  have hidxc : p.idxOf c = n - 1 := by
    have hi := hpnodup.idxOf_getElem (i := n - 1) (by omega : n - 1 < p.length)
    have hv : p[n - 1] = c := by
      rw [← List.getD_eq_getElem _ 0 (by omega : n - 1 < p.length)]
    rw [hv] at hi
    exact hi
  have hqn : q.getD (c - 1) 0 = n := by
    have hh := hB_at c hcpos (by omega)
    rw [hat_one_block p hmaxp c hcmem, hidxc] at hh
    rw [if_neg (by omega : ¬ n - 1 + 1 < p.length), hfirst] at hh
    exact hh
  have hcp1mem : c + 1 ∈ p := hp.mem_iff.mpr
    (List.mem_range'.mpr ⟨c, by omega, by omega⟩)
  have hidxcp1 : p.idxOf (c + 1) = t := by
    have hi := hpnodup.idxOf_getElem (i := t) (by omega : t < p.length)
    have hv : p[t] = c + 1 := by
      rw [← List.getD_eq_getElem _ 0 (by omega : t < p.length), htval]
    rw [hv] at hi
    exact hi
  have hqc : q.getD c 0 = 1 := by
    have hh := hB_at (c + 1) (by omega) (by omega)
    have hidx : c + 1 - 1 = c := by omega
    rw [hidx, hat_one_block p hmaxp (c + 1) hcp1mem, hidxcp1] at hh
    rw [if_pos (by omega : t + 1 < p.length), htone] at hh
    exact hh
  have hpsecond : p.getD 1 0 = n - 1 := by
    have hprefixlen : t + 1 = n - c := by
      have hh := congrArg List.length hprefix
      simp at hh
      omega
    have ht2 : 1 < t + 1 := by omega
    have hh := congrArg (fun l : List ℕ => l.getD 1 0) hprefix
    have htake : (p.take (t + 1)).getD 1 0 = p.getD 1 0 := by
      rw [List.getD_eq_getElem _ 0 (by simp; omega),
        List.getD_eq_getElem _ 0 (by omega : 1 < p.length)]
      simp only [List.getElem_take]
    rw [htake] at hh
    have hreverse : ((List.range' (c + 1) (n - c)).reverse).getD 1 0 =
        n - 1 := by
      rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_reverse]
      simp only [List.length_range', List.getElem_range'_1]
      omega
    rw [hreverse] at hh
    exact hh
  have hnmem : n ∈ p := hp.mem_iff.mpr
    (List.mem_range'.mpr ⟨n - 1, by omega, by omega⟩)
  have hidxn : p.idxOf n = 0 := by
    have hi := hpnodup.idxOf_getElem (i := 0) (by omega : 0 < p.length)
    have hv : p[0] = n := by
      rw [← List.getD_eq_getElem _ 0 (by omega : 0 < p.length), hfirst]
    rw [hv] at hi
    exact hi
  have hqlast : q.getD (n - 1) 0 = n - 1 := by
    have hh := hB_at n (by omega) (by omega)
    rw [show n - 1 = n - 1 by rfl,
      hat_one_block p hmaxp n hnmem, hidxn] at hh
    rw [if_pos (by omega : 0 + 1 < p.length)] at hh
    simpa only [show 0 + 1 = 1 by omega, hpsecond] using hh
  exact False.elim (middle_cycle_conflict p q n c hqperm (by omega) hcge hcmid
    hqn hqc hqlast hpr (by rfl))

end D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Boundary
