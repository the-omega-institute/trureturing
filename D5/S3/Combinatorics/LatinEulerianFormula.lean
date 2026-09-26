/- GID: D5/S3/Combinatorics/LatinEulerianFormula
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LatinEulerianFormula
   mirror-E: none(waiver:direct-cyclic-shift-ascent-identity)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Swapped cyclic row squares have an explicit ascent formula. -/

import D5.S3.Combinatorics.LatinEulerianCounting
import D5.S3.Combinatorics.LatinEulerianShiftCount
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LatinEulerianMultiples

/-- The symbol permutation interchanging zero and one. -/
def swapFin (n : ℕ) (hn : 2 ≤ n) : Equiv.Perm (Fin n) :=
  Equiv.swap (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n)

/-- The cyclic square whose symbols zero and one are interchanged. -/
def shiftedSquare (n : ℕ) (hn : 2 ≤ n) (p : Equiv.Perm (Fin n)) :
    Fin n → Fin n → Fin n :=
  fun i c => swapFin n hn (p i + c)

theorem shifted_pair_count {n : ℕ} (hn : 3 ≤ n) (h2 : 2 ≤ n)
    (a b : Fin n) (hab : a ≠ b) :
    let d : Fin n := b - a
    ((Finset.univ : Finset (Fin n)).filter
      (fun c => swapFin n h2 (a + c) < swapFin n h2 (b + c))).card +
        (if d.val = 1 then 1 else 0) =
      n - d.val + (if d.val = n - 1 then 1 else 0) := by
  classical
  letI : NeZero n := ⟨by omega⟩
  let e := ZMod.finEquiv n
  let d : Fin n := b - a
  have hdmap : e d = e b - e a := by simp [d, e]
  have hd0 : 0 < d.val := by
    by_contra h
    have hdval : d.val = 0 := by omega
    have hdz : e d = 0 := by
      have : d = (0 : Fin n) := Fin.ext hdval
      simp [this]
    rw [hdmap] at hdz
    exact hab ((e.injective (sub_eq_zero.mp hdz)).symm)
  have hbd (c : Fin n) : b + c = (a + c) + d := by
    apply e.injective
    simp only [map_add, hdmap]
    abel
  have htranslate : Function.Bijective (fun c : Fin n => a + c) := by
    apply Finite.injective_iff_bijective.mp
    intro x y h
    apply e.injective
    apply add_left_cancel (a := e a)
    simpa only [map_add] using congrArg e h
  have hswap (x : Fin n) : (swapFin n h2 x).val = swap01 x.val := by
    by_cases h0 : x.val = 0
    · have hx : x = (⟨0, by omega⟩ : Fin n) := Fin.ext h0
      rw [hx]
      simp [swapFin, swap01]
    by_cases h1 : x.val = 1
    · have hx : x = (⟨1, by omega⟩ : Fin n) := Fin.ext h1
      rw [hx]
      simp [swapFin, swap01]
    · have hne0 : x ≠ (⟨0, by omega⟩ : Fin n) := by
        intro h
        have hv : x.val = 0 := congrArg Fin.val h
        exact h0 hv
      have hne1 : x ≠ (⟨1, by omega⟩ : Fin n) := by
        intro h
        have hv : x.val = 1 := congrArg Fin.val h
        exact h1 hv
      change ((Equiv.swap (⟨0, by omega⟩ : Fin n)
        (⟨1, by omega⟩ : Fin n)) x).val = swap01 x.val
      rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]
      simp [swap01, h0, h1]
  have hcount1 :
      ((Finset.univ : Finset (Fin n)).filter
        (fun c => swapFin n h2 (a + c) < swapFin n h2 (b + c))).card =
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => swapFin n h2 x < swapFin n h2 (x + d))).card := by
    apply Finset.card_bijective (fun c : Fin n => a + c) htranslate
    intro c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hbd c]
  have hcount2 :
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => swapFin n h2 x < swapFin n h2 (x + d))).card =
      shiftedAscents n d.val := by
    have hpred (x : Fin n) :
        (swapFin n h2 x < swapFin n h2 (x + d)) ↔
          swap01 x.val < swap01 ((x.val + d.val) % n) := by
      change (swapFin n h2 x).val < (swapFin n h2 (x + d)).val ↔ _
      rw [hswap x, hswap (x + d), Fin.val_add]
    have hfilter : ((Finset.univ : Finset (Fin n)).filter
        (fun x => swapFin n h2 x < swapFin n h2 (x + d))) =
        (Finset.univ : Finset (Fin n)).filter
          (fun x => swap01 x.val < swap01 ((x.val + d.val) % n)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hpred x
    rw [hfilter]
    unfold shiftedAscents
    apply Finset.card_bij (fun x _ => x.val)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨x.isLt, hx⟩
    · intro x hx y hy h
      exact Fin.ext h
    · intro y hy
      have hyn : y < n := (Finset.mem_filter.mp hy).1 |> Finset.mem_range.mp
      refine ⟨⟨y, hyn⟩, ?_, rfl⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
        (Finset.mem_filter.mp hy).2
  change ((Finset.univ : Finset (Fin n)).filter
      (fun c => swapFin n h2 (a + c) < swapFin n h2 (b + c))).card +
        (if d.val = 1 then 1 else 0) =
      n - d.val + (if d.val = n - 1 then 1 else 0)
  rw [hcount1, hcount2]
  exact shifted_ascent_count hn hd0 d.isLt

/-- Read a permutation at a natural index modulo its order. -/
def rowAt {n : ℕ} (hn : 0 < n) (p : Equiv.Perm (Fin n)) (j : ℕ) : Fin n :=
  p ⟨j % n, Nat.mod_lt _ hn⟩

/-- The cyclic difference between consecutive permutation entries. -/
def rowDelta {n : ℕ} (hn : 0 < n) (p : Equiv.Perm (Fin n)) (j : ℕ) : Fin n :=
  rowAt hn p (j + 1) - rowAt hn p j

/-- Ordinary ascents of the row permutation, counted in the integers. -/
def ordinaryAscents {n : ℕ} (hn : 0 < n) (p : Equiv.Perm (Fin n)) : ℤ :=
  ∑ j ∈ Finset.range (n - 1),
    if rowAt hn p j < rowAt hn p (j + 1) then 1 else 0

/-- Forward cyclic unit steps of the row permutation. -/
def forwardUnits {n : ℕ} (hn : 0 < n) (p : Equiv.Perm (Fin n)) : ℤ :=
  ∑ j ∈ Finset.range (n - 1), if (rowDelta hn p j).val = 1 then 1 else 0

/-- Backward cyclic unit steps of the row permutation. -/
def backwardUnits {n : ℕ} (hn : 0 < n) (p : Equiv.Perm (Fin n)) : ℤ :=
  ∑ j ∈ Finset.range (n - 1), if (rowDelta hn p j).val = n - 1 then 1 else 0

theorem shiftedSquare_formula {n : ℕ} (hn : 3 ≤ n) (h2 : 2 ≤ n)
    (hpos : 0 < n) (p : Equiv.Perm (Fin n)) :
    (totalAscents n (shiftedSquare n h2 p) : ℤ) =
      (n : ℤ) * ordinaryAscents hpos p + (rowAt hpos p 0).val -
        (rowAt hpos p (n - 1)).val - forwardUnits hpos p + backwardUnits hpos p := by
  let L := shiftedSquare n h2 p
  have hlast : rowAscents n L (n - 1) = 0 := by
    have h : ¬ (n - 1 + 1 < n) := by omega
    simp [rowAscents, h]
  have hrows : totalAscents n L =
      ∑ j ∈ Finset.range n, rowAscents n L j := by
    classical
    simp only [totalAscents, colAscents, rowAscents, Finset.card_eq_sum_ones,
      Finset.sum_filter]
    rw [Finset.sum_comm]
  have htotal : totalAscents n L =
      ∑ j ∈ Finset.range (n - 1), rowAscents n L j := by
    rw [hrows]
    conv_lhs => arg 1; rw [show n = (n - 1) + 1 by omega]
    rw [Finset.sum_range_succ, hlast, add_zero]
  have hpair (j : ℕ) (hj : j ∈ Finset.range (n - 1)) :
      (rowAscents n L j : ℤ) =
        (if rowAt hpos p j < rowAt hpos p (j + 1) then (n : ℤ) else 0) +
          (rowAt hpos p j).val - (rowAt hpos p (j + 1)).val -
          (if (rowDelta hpos p j).val = 1 then (1 : ℤ) else 0) +
          (if (rowDelta hpos p j).val = n - 1 then (1 : ℤ) else 0) := by
    have hj' : j + 1 < n := by have := Finset.mem_range.mp hj; omega
    have hj0 : j < n := by omega
    let a := rowAt hpos p j
    let b := rowAt hpos p (j + 1)
    let d := b - a
    have hab : a ≠ b := by
      intro heq
      have hi := p.injective heq
      have hv : j % n = (j + 1) % n := congrArg Fin.val hi
      rw [Nat.mod_eq_of_lt hj0, Nat.mod_eq_of_lt hj'] at hv
      omega
    have hrow : rowAscents n L j =
        ((Finset.univ : Finset (Fin n)).filter
          (fun c => swapFin n h2 (a + c) < swapFin n h2 (b + c))).card := by
      simp [rowAscents, L, shiftedSquare, a, b, rowAt, hj',
        Nat.mod_eq_of_lt hj0, Nat.mod_eq_of_lt hj']
    have hcount : rowAscents n L j + (if d.val = 1 then 1 else 0) =
        n - d.val + (if d.val = n - 1 then 1 else 0) := by
      rw [hrow]
      exact shifted_pair_count hn h2 a b hab
    have hstep : ((n - d.val : ℕ) : ℤ) =
        (if a < b then (n : ℤ) else 0) + (a.val : ℤ) - (b.val : ℤ) := by
      have h := Fin.coe_int_sub_eq_ite b a
      have hcast : ((n - (b - a).val : ℕ) : ℤ) =
          (n : ℤ) - ((b - a).val : ℤ) := by omega
      by_cases hlt : a < b
      · simp [d, hlt, le_of_lt hlt] at h ⊢
        omega
      · have hnot : ¬ a ≤ b := by
          intro hle
          exact hab (le_antisymm hle (le_of_not_gt hlt))
        simp [d, hlt, hnot] at h ⊢
        omega
    have hcountInt : (rowAscents n L j : ℤ) +
        (if d.val = 1 then (1 : ℤ) else 0) =
        ((n - d.val : ℕ) : ℤ) +
          (if d.val = n - 1 then (1 : ℤ) else 0) := by
      exact_mod_cast hcount
    dsimp [a, b, d, rowDelta] at hstep hcountInt ⊢
    omega
  calc
    (totalAscents n (shiftedSquare n h2 p) : ℤ) =
        ∑ j ∈ Finset.range (n - 1), (rowAscents n L j : ℤ) := by
          change (totalAscents n L : ℤ) = _
          rw [htotal]
          exact Nat.cast_sum (Finset.range (n - 1)) (rowAscents n L)
    _ = ∑ j ∈ Finset.range (n - 1),
        ((if rowAt hpos p j < rowAt hpos p (j + 1) then (n : ℤ) else 0) +
          (rowAt hpos p j).val - (rowAt hpos p (j + 1)).val -
          (if (rowDelta hpos p j).val = 1 then (1 : ℤ) else 0) +
          (if (rowDelta hpos p j).val = n - 1 then (1 : ℤ) else 0)) := by
          apply Finset.sum_congr rfl
          exact hpair
    _ = (n : ℤ) * ordinaryAscents hpos p + (rowAt hpos p 0).val -
        (rowAt hpos p (n - 1)).val - forwardUnits hpos p +
        backwardUnits hpos p := by
          have htel :
              (∑ j ∈ Finset.range (n - 1), ((rowAt hpos p j).val : ℤ)) -
                (∑ j ∈ Finset.range (n - 1),
                  ((rowAt hpos p (j + 1)).val : ℤ)) =
              (rowAt hpos p 0).val - (rowAt hpos p (n - 1)).val := by
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_range_sub' (fun j => ((rowAt hpos p j).val : ℤ)) (n - 1)
          have hscale :
              (∑ j ∈ Finset.range (n - 1),
                if rowAt hpos p j < rowAt hpos p (j + 1) then (n : ℤ) else 0) =
              (n : ℤ) * ordinaryAscents hpos p := by
            rw [ordinaryAscents, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            split_ifs <;> simp
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          rw [hscale]
          simp only [forwardUnits, backwardUnits]
          omega

end D5.S3.Combinatorics.LatinEulerianMultiples
