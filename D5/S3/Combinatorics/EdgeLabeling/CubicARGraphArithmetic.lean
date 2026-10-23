/- GID: D5/S3/Combinatorics/EdgeLabeling/CubicARGraphArithmetic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/CubicARGraphArithmetic
   mirror-E: none(waiver:counting-component-of-open-problem-resolution)
   anchors: []
   utility: none
   digest: Additive triples and the strict counting bound for cubic AR labeling. -/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.EdgeLabeling.CubicARGraphArithmetic

open Finset

/-- Sorted smaller labels of an additive triple in the free interval. -/
def additivePairs (m : ℕ) : Finset (ℕ × ℕ) :=
  (range ((m - 5) / 2)).biUnion fun a =>
    (Icc (a + 4) (m - (a + 3))).image fun b => (a + 3, b)

/-- Membership is precisely the additive-triple constraint. -/
theorem mem_additivePairs {m a b : ℕ} (hm : 6 ≤ m) :
    (a, b) ∈ additivePairs m ↔ 3 ≤ a ∧ a < b ∧ a + b ≤ m := by
  simp only [additivePairs, mem_biUnion, mem_range, mem_image, mem_Icc,
    Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, j, hj, hij⟩
    rcases hij with ⟨rfl, rfl⟩
    omega
  · rintro ⟨ha, hab, hsum⟩
    refine ⟨a - 3, ?_, b, ?_, ?_⟩ <;> omega

private lemma descending_sum (r k : ℕ) (h : 2 * r ≤ k + 1) :
    (∑ a ∈ range r, (k - 2 * a)) = r * (k + 1 - r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hr : 2 * r ≤ k + 1 := by omega
    have hkr : 2 * r ≤ k := by omega
    rw [sum_range_succ, ih hr]
    have hsub : k - 2 * r + 2 * r = k := Nat.sub_add_cancel hkr
    have hsub2 : k + 1 - r + r = k + 1 := Nat.sub_add_cancel (by omega)
    have hsub3 : k + 1 - (r + 1) + (r + 1) = k + 1 :=
      Nat.sub_add_cancel (by omega)
    nlinarith

/-- The additive triples are counted by a rectangle with two consecutive side lengths. -/
private theorem card_additivePairs (m : ℕ) (hm : 6 ≤ m) :
    (additivePairs m).card = ((m - 5) / 2) * (m - 5 - (m - 5) / 2) := by
  have hd : ((range ((m - 5) / 2)) : Set ℕ).PairwiseDisjoint
      (fun a => (Icc (a + 4) (m - (a + 3))).image fun b => (a + 3, b)) := by
    intro a ha b hb hab
    apply disjoint_left.mpr
    intro p hp hq
    simp only [mem_image, mem_Icc] at hp hq
    obtain ⟨x, hx, he⟩ := hp
    obtain ⟨y, hy, hf⟩ := hq
    have : a + 3 = b + 3 := by simpa using congrArg Prod.fst (he.trans hf.symm)
    exact hab (by omega)
  rw [additivePairs, card_biUnion hd]
  have hrows : ∀ a ∈ range ((m - 5) / 2),
      ((Icc (a + 4) (m - (a + 3))).image fun b => (a + 3, b)).card =
        m - 6 - 2 * a := by
    intro a ha
    rw [card_image_of_injective]
    · rw [Nat.card_Icc]
      simp only [mem_range] at ha
      omega
    · intro x y hxy
      exact congrArg Prod.snd hxy
  rw [sum_congr rfl hrows, descending_sum]
  · congr 1
    omega
  · omega

/-- The squared form bounds the free additive-triple count without parity cases. -/
theorem four_mul_card_additivePairs_le (m : ℕ) (hm : 6 ≤ m) :
    4 * (additivePairs m).card ≤ (m - 5) ^ 2 := by
  rw [card_additivePairs m hm]
  have hsub : m - 5 - (m - 5) / 2 + (m - 5) / 2 = m - 5 :=
    Nat.sub_add_cancel (Nat.div_le_self _ _)
  have hrem : m - 5 - 2 * ((m - 5) / 2) + 2 * ((m - 5) / 2) = m - 5 :=
    Nat.sub_add_cancel (by omega)
  nlinarith [Nat.zero_le ((m - 5 - 2 * ((m - 5) / 2)) ^ 2)]

/-- The normalized bad-pair count is strictly smaller than the labeling count. -/
private theorem normalized_count_lt (m n t : ℕ) (hm : 12 ≤ m) (hrel : 3 * n = 2 * m)
    (ht : 4 * t ≤ (m - 5) ^ 2) :
    (m - 3) * (m - 4) + 2 * (2 * m - 7) * (m - 4) + 6 * (n - 3) * t <
      (m - 2) * (m - 3) * (m - 4) := by
  have hn : 8 ≤ n := by omega
  have hmul := Nat.mul_le_mul_left (2 * m - 9) ht
  have hm2 : m - 2 + 2 = m := by omega
  have hm3 : m - 3 + 3 = m := by omega
  have hm4 : m - 4 + 4 = m := by omega
  have hm5 : m - 5 + 5 = m := by omega
  have hm7 : 2 * m - 7 + 7 = 2 * m := by omega
  have hm9 : 2 * m - 9 + 9 = 2 * m := by omega
  have hn3 : n - 3 + 3 = n := by omega
  have hmz : (12 : ℤ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℤ) < (m : ℤ) ^ 2 - 14 * m + 41 := by
    nlinarith [sq_nonneg ((m : ℤ) - 12)]
  zify at ht hmul hrel hm2 hm3 hm4 hm5 hm7 hm9 hn3 ⊢
  have hnreplace : 6 * ((n - 3 : ℕ) : ℤ) = 4 * (m : ℤ) - 18 := by omega
  rw [show ((2 * m - 9 : ℕ) : ℤ) = 2 * (m : ℤ) - 9 by omega,
    show ((m - 5 : ℕ) : ℤ) = (m : ℤ) - 5 by omega] at hmul
  rw [show ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 by omega,
    show ((m - 3 : ℕ) : ℤ) = (m : ℤ) - 3 by omega,
    show ((m - 4 : ℕ) : ℤ) = (m : ℤ) - 4 by omega,
    show ((2 * m - 7 : ℕ) : ℤ) = 2 * (m : ℤ) - 7 by omega, hnreplace]
  nlinarith

/-- The factorial-weighted union bound is strict. -/
theorem bad_count_lt_factorial (m n t : ℕ) (hm : 12 ≤ m)
    (hrel : 3 * n = 2 * m) (ht : 4 * t ≤ (m - 5) ^ 2) :
    (m - 3).factorial + 2 * (2 * m - 7) * (m - 4).factorial +
      6 * (n - 3) * t * (m - 5).factorial < (m - 2).factorial := by
  have f4 : (m - 4).factorial = (m - 4) * (m - 5).factorial := by
    simpa only [show m - 5 + 1 = m - 4 by omega] using Nat.factorial_succ (m - 5)
  have f3 : (m - 3).factorial = (m - 3) * (m - 4).factorial := by
    simpa only [show m - 4 + 1 = m - 3 by omega] using Nat.factorial_succ (m - 4)
  have f2 : (m - 2).factorial = (m - 2) * (m - 3).factorial := by
    simpa only [show m - 3 + 1 = m - 2 by omega] using Nat.factorial_succ (m - 3)
  rw [f2, f3, f4]
  convert Nat.mul_lt_mul_of_pos_right (normalized_count_lt m n t hm hrel ht)
      (Nat.factorial_pos (m - 5)) using 1 <;> ring

end D5.S3.Combinatorics.EdgeLabeling.CubicARGraphArithmetic
