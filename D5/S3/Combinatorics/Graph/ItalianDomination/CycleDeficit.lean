/- GID: D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: An explicit finite binomial sum counts every labelled Italian cycle coefficient. -/

/-
admission_basis: open-problem-resolution (#23882; Proved)
escape_witness: D5.S3.Combinatorics.Graph.ItalianDomination.RootedCycleGaps.rootedRefinedCycle_card
Frozen inputs after same-delivery inlining:
  CycleItalianDominationRecurrence.IsItalian: declaration statement_id sha256:9758047395f299db1257334e19147fe19dfb182c18c34bbd41fe742fe8457078.
  ArrowWilfGapData.GapsOn: declaration statement_id sha256:2ec3e595a3a4e7925968c40d0521dfc1c8cac88956d06fc0296eb201e7fd3fb6.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27880.
proof_shape: result: content; escape_witness: D5.S3.Combinatorics.Graph.ItalianDomination.RootedCycleGaps.rootedRefinedCycle_card
-/

import D5.S3.Combinatorics.Graph.ItalianDomination.OrdinaryWords
import D5.S3.Combinatorics.Graph.ItalianDomination.RootedCycleGaps
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section

namespace D5.S3.Combinatorics.Graph.ItalianDomination.CycleDeficit

open scoped BigOperators
open D5.S3.Combinatorics.Graph.ItalianDomination.OrdinaryWords
open D5.S3.Combinatorics.Graph.ItalianDomination.RootedCycleGaps

def binom (u v : ℤ) : ℚ :=
  if 0 ≤ u ∧ 0 ≤ v then (Nat.choose u.toNat v.toNat : ℚ) else 0

def zeroFree (n j : ℕ) : ℚ :=
  let r : ℤ := (j : ℤ) - (n : ℤ)
  let s : ℤ := 2 * (n : ℤ) - (j : ℤ)
  if 0 ≤ r ∧ 2 * r ≤ (n : ℤ) ∧ 0 < s then
    (n : ℚ) / (s : ℚ) * binom s r
  else 0

def allExceptional (n j : ℕ) : ℚ :=
  if n % 3 = 0 ∧ 3 * j = 4 * n then 3 else 0

def gapTerm (n j a b : ℕ) : ℚ :=
  let c : ℤ := (j : ℤ) - 2 * (a : ℤ) - 4 * (b : ℤ)
  let t : ℤ := (n : ℤ) - (j : ℤ) + (a : ℤ) + (b : ℤ)
  let m : ℤ := t + (b : ℤ)
  if 0 ≤ c ∧ 1 ≤ t then
    (n : ℚ) / (m : ℚ) * binom m (b : ℤ) *
      binom (c + t - 1) c * binom (c + t) (a : ℤ)
  else 0

def closedForm (n j : ℕ) : ℚ :=
  zeroFree n j + allExceptional n j +
    ∑ b ∈ Finset.range (j + 1), ∑ a ∈ Finset.range (j + 1), gapTerm n j a b

def claim : Prop :=
  ∀ (n : ℕ) (j : ℕ), 3 ≤ n → j ≤ 2 * n →
    (dI n (2 * n - j) : ℚ) = closedForm n j

private theorem zeroFree_cycle_rational_count (c a : ℕ) :
    (Nat.card (ZeroFreeWords c a) : ℚ) =
      (c + a + 1 : ℚ) / (c + 1) * ((c + 1).choose a : ℚ) := by
  have hm : (c + 1 : ℚ) ≠ 0 := by exact Nat.cast_add_one_ne_zero c
  have hh := zeroFree_cycle_marking_count c a
  have hq : (c + 1 : ℚ) * (Nat.card (ZeroFreeWords c a) : ℚ) =
      (c + a + 1 : ℚ) * ((c + 1).choose a : ℚ) := by exact_mod_cast hh
  apply (mul_left_cancel₀ hm)
  rw [hq]
  field_simp

private theorem refined_cycle_rational_count {N m b c a : ℕ} (hm : 0 < m)
    (hlen : N + 1 = m + c + a + 2 * b) :
    (Nat.card (RefinedCycle N m b c a) : ℚ) =
      ((N + 1 : ℕ) : ℚ) / m * (m.choose b : ℚ) *
        ((c + (m - b) - 1).choose c : ℚ) * ((c + (m - b)).choose a : ℚ) := by
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hh := refined_cycle_marking_count hm hlen
  have hq : (m : ℚ) * (Nat.card (RefinedCycle N m b c a) : ℚ) =
      ((N + 1 : ℕ) : ℚ) * ((m.choose b : ℚ) *
        ((c + (m - b) - 1).choose c : ℚ) * ((c + (m - b)).choose a : ℚ)) := by
    exact_mod_cast hh
  apply (mul_left_cancel₀ hmq)
  rw [hq]
  field_simp
  <;> ring

private theorem allExceptional_refined_card (m : ℕ) (hm : 0 < m) :
    Nat.card (RefinedCycle (3 * m - 1) m m 0 0) = 3 := by
  have hlen : 3 * m - 1 + 1 = m + 0 + 0 + 2 * m := by omega
  have hh := refined_cycle_marking_count hm hlen
  simp only [Nat.sub_self, Nat.zero_add, Nat.zero_sub, Nat.choose_zero_right,
    Nat.choose_self, Nat.mul_one] at hh
  exact Nat.eq_of_mul_eq_mul_left hm (hh.trans (by omega))

private theorem binom_nat (u v : ℕ) : binom (u : ℤ) (v : ℤ) = (u.choose v : ℚ) := by
  exact Rat.ext rfl rfl

private theorem zeroFree_parameters (s r : ℕ) (hs : 0 < s) (hr : r ≤ s) :
    zeroFree (s + r) (s + 2 * r) = ((s + r : ℕ) : ℚ) / s * (s.choose r : ℚ) := by
  have hR : ((s + 2 * r : ℕ) : ℤ) - ((s + r : ℕ) : ℤ) = r := by push_cast; ring
  have hS : 2 * ((s + r : ℕ) : ℤ) - ((s + 2 * r : ℕ) : ℤ) = s := by push_cast; ring
  have hguard : 0 ≤ (r : ℤ) ∧ 2 * (r : ℤ) ≤ ((s + r : ℕ) : ℤ) ∧ 0 < (s : ℤ) := by
    exact_mod_cast (show 0 ≤ r ∧ 2 * r ≤ s + r ∧ 0 < s by omega)
  simp only [zeroFree, hR, hS, if_pos hguard, binom_nat, Int.cast_natCast]

private theorem gapTerm_parameters (m b c a : ℕ) (hb : b < m) :
    gapTerm (m + c + a + 2 * b) (c + 2 * a + 4 * b) a b =
      ((m + c + a + 2 * b : ℕ) : ℚ) / m * (m.choose b : ℚ) *
        ((c + (m - b) - 1).choose c : ℚ) * ((c + (m - b)).choose a : ℚ) := by
  have hC : ((c + 2 * a + 4 * b : ℕ) : ℤ) - 2 * (a : ℤ) - 4 * (b : ℤ) = c := by
    push_cast; ring
  have hT : ((m + c + a + 2 * b : ℕ) : ℤ) - ((c + 2 * a + 4 * b : ℕ) : ℤ) +
      (a : ℤ) + (b : ℤ) = ((m - b : ℕ) : ℤ) := by
    rw [Nat.cast_sub (Nat.le_of_lt hb)]
    push_cast
    ring
  have ht : 1 ≤ m - b := by exact Nat.le_sub_of_add_le' hb
  have hguard : 0 ≤ (c : ℤ) ∧ 1 ≤ ((m - b : ℕ) : ℤ) := by exact_mod_cast (show 0 ≤ c ∧ 1 ≤ m - b by omega)
  have hM : ((m - b : ℕ) : ℤ) + (b : ℤ) = m := by exact_mod_cast Nat.sub_add_cancel (Nat.le_of_lt hb)
  have htop : (c : ℤ) + ((m - b : ℕ) : ℤ) - 1 = ((c + (m - b) - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (show 1 ≤ c + (m - b) by omega)]
    push_cast
    ring
  simp only [gapTerm, hC, hT, if_pos hguard, hM, htop]
  rw [show (c : ℤ) + ((m - b : ℕ) : ℤ) = ((c + (m - b) : ℕ) : ℤ) by push_cast; rfl]
  simp only [binom_nat, Int.cast_natCast]

private theorem refined_cycle_gapTerm {N m b c a : ℕ} (hb : b < m)
    (hlen : N + 1 = m + c + a + 2 * b) :
    (Nat.card (RefinedCycle N m b c a) : ℚ) =
      gapTerm (N + 1) (c + 2 * a + 4 * b) a b := by
  rw [refined_cycle_rational_count (by omega) hlen, hlen, gapTerm_parameters m b c a hb]

private abbrev NoZeroCoefficient (n j : ℕ) :=
  {y : Fin n → Fin 3 // IsDeficit y ∧ (∑ i, (y i).val) = j ∧ ¬ ∃ i, y i = 0}

private abbrev PositiveCoefficient (n j : ℕ) :=
  {y : Fin n → Fin 3 // IsDeficit y ∧ (∑ i, (y i).val) = j ∧ ∃ i, y i = 0}

private abbrev PositiveRefined (n j a b : ℕ) :=
  {y : Fin n → Fin 3 // IsDeficit y ∧ (∑ i, (y i).val) = j ∧ (∃ i, y i = 0) ∧
    doubleTwoCount y = b ∧ labelCount y 2 - 2 * doubleTwoCount y = a}

private theorem coefficient_zero_partition (n j : ℕ) (hj : j ≤ 2 * n) :
    dI n (2 * n - j) = Nat.card (NoZeroCoefficient n j) + Nat.card (PositiveCoefficient n j) := by
  classical
  rw [dI_eq_deficit_card n j hj]
  let S : Finset (Fin n → Fin 3) := Finset.univ.filter (fun y => IsDeficit y ∧ (∑ i, (y i).val) = j)
  have hh := Finset.card_filter_add_card_filter_not (s := S) (p := fun y => ∃ i, y i = 0)
  simpa only [S, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter,
    NoZeroCoefficient, PositiveCoefficient, and_assoc, Nat.add_comm] using hh.symm

private theorem positive_coefficient_partition (N j : ℕ) :
    Nat.card (PositiveCoefficient (N + 1) j) =
      ∑ b ∈ Finset.range (j + 1), ∑ a ∈ Finset.range (j + 1),
        Nat.card (PositiveRefined (N + 1) j a b) := by
  classical
  let P : (Fin (N + 1) → Fin 3) → Prop := fun y =>
    IsDeficit y ∧ (∑ i, (y i).val) = j ∧ ∃ i, y i = 0
  let S := Finset.univ.filter P
  let f : (Fin (N + 1) → Fin 3) → ℕ × ℕ := fun y =>
    (doubleTwoCount y, labelCount y 2 - 2 * doubleTwoCount y)
  let T := (Finset.range (j + 1)) ×ˢ (Finset.range (j + 1))
  have hm : (S : Set (Fin (N + 1) → Fin 3)).MapsTo f T := by
    intro y hy
    have hh := (Finset.mem_filter.mp hy).2
    have hparams := zeroContaining_parameter_equations y hh.1 hh.2.2 hh.2.1
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by dsimp [f]; omega),
      Finset.mem_range.mpr (by dsimp [f]; omega)⟩
  have hc := Finset.card_eq_sum_card_fiberwise hm
  rw [Finset.sum_product] at hc
  simpa [S, T, f, P, Nat.card_eq_fintype_card, Fintype.card_subtype,
    PositiveCoefficient, PositiveRefined, Finset.filter_filter, and_assoc] using hc

private theorem positive_refined_equiv_pred {N j a b : ℕ} (y : Fin (N + 1) → Fin 3)
    (hy : IsDeficit y) (hw : (∑ i, (y i).val) = j) (hz : ∃ i, y i = 0)
    (hb : doubleTwoCount y = b) (ha : labelCount y 2 - 2 * doubleTwoCount y = a) :
    labelCount y 2 = a + 2 * b ∧
      (labelCount y 1 : ℤ) = (j : ℤ) - 2 * (a : ℤ) - 4 * (b : ℤ) ∧
      (labelCount y 0 : ℤ) = ((N + 1 : ℕ) : ℤ) - (j : ℤ) + (a : ℤ) + 2 * (b : ℤ) := by
  have hbound := zeroContaining_inventory_bounds y hy hz
  have hcount := labelCount_sum y
  have hweight := weight_eq_labelCount y
  rw [hw] at hweight
  rw [hb] at ha hbound
  constructor
  · omega
  · omega

private theorem labelCount_zero_iff {n : ℕ} (y : Fin n → Fin 3) :
    labelCount y 0 = 0 ↔ ∀ i, y i ≠ 0 := by
  classical
  simp [labelCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

private def noZeroParameterEquiv (c a : ℕ) :
    NoZeroCoefficient (c + a + 1) (c + 1 + 2 * a) ≃ ZeroFreeWords c a :=
  Equiv.subtypeEquivRight (fun y => by
    constructor
    · intro hy
      have hz : ∀ i, y i ≠ 0 := by simpa only [not_exists] using hy.2.2
      have hc0 := (labelCount_zero_iff y).mpr hz
      have hs := labelCount_sum y
      have hw := weight_eq_labelCount y
      rw [hy.2.1] at hw
      refine ⟨hz, hy.1, ?_, ?_⟩ <;> omega
    · intro hy
      refine ⟨hy.2.1, ?_, ?_⟩
      · rw [weight_eq_labelCount, hy.2.2.1, hy.2.2.2]
      · simpa only [not_exists] using hy.1)

private theorem noZero_parameter_count (c a : ℕ) :
    (Nat.card (NoZeroCoefficient (c + a + 1) (c + 1 + 2 * a)) : ℚ) =
      ((c + a + 1 : ℕ) : ℚ) / (c + 1) * ((c + 1).choose a : ℚ) := by
  rw [Nat.card_congr (noZeroParameterEquiv c a), zeroFree_cycle_rational_count]
  simp only [Nat.cast_add, Nat.cast_one]

private theorem noZero_count_constraints {n j : ℕ} (y : NoZeroCoefficient n j) :
    n ≤ j ∧ j + labelCount y.val 1 = 2 * n ∧
      labelCount y.val 2 ≤ labelCount y.val 1 := by
  have hz : ∀ i, y.val i ≠ 0 := by simpa only [not_exists] using y.prop.2.2
  have hc0 := (labelCount_zero_iff y.val).mpr hz
  have hs := labelCount_sum y.val
  have hw := weight_eq_labelCount y.val
  have hle := zeroFree_twos_le_ones y.val hz y.prop.1
  rw [y.prop.2.1] at hw
  omega

private theorem noZeroCoefficient_card {N j : ℕ} (hj : j ≤ 2 * (N + 1)) :
    (Nat.card (NoZeroCoefficient (N + 1) j) : ℚ) = zeroFree (N + 1) j := by
  by_cases hlow : j < N + 1
  · letI : IsEmpty (NoZeroCoefficient (N + 1) j) := ⟨fun y => by
      have hh := noZero_count_constraints y
      omega⟩
    have hr : ¬ (0 ≤ (j : ℤ) - ((N + 1 : ℕ) : ℤ) ∧
        2 * ((j : ℤ) - ((N + 1 : ℕ) : ℤ)) ≤ ((N + 1 : ℕ) : ℤ) ∧
        0 < 2 * ((N + 1 : ℕ) : ℤ) - (j : ℤ)) := by omega
    have hcard : Nat.card (NoZeroCoefficient (N + 1) j) = 0 := by exact Nat.card_of_isEmpty
    rw [hcard]
    simp only [Nat.cast_zero]
    unfold zeroFree
    rw [if_neg hr]
  by_cases htop : j = 2 * (N + 1)
  · letI : IsEmpty (NoZeroCoefficient (N + 1) j) := ⟨fun y => by
      have hh := noZero_count_constraints y
      have hs := labelCount_sum y.val
      have hz : labelCount y.val 0 = 0 := (labelCount_zero_iff y.val).mpr
        (by simpa only [not_exists] using y.prop.2.2)
      have hw := weight_eq_labelCount y.val
      rw [y.prop.2.1] at hw
      omega⟩
    have hcard : Nat.card (NoZeroCoefficient (N + 1) j) = 0 := by exact Nat.card_of_isEmpty
    have hr : ¬ (0 ≤ (j : ℤ) - ((N + 1 : ℕ) : ℤ) ∧
        2 * ((j : ℤ) - ((N + 1 : ℕ) : ℤ)) ≤ ((N + 1 : ℕ) : ℤ) ∧
        0 < 2 * ((N + 1 : ℕ) : ℤ) - (j : ℤ)) := by omega
    rw [hcard]
    simp only [Nat.cast_zero]
    unfold zeroFree
    rw [if_neg hr]
  have hs : 0 < 2 * (N + 1) - j := by omega
  let c := 2 * (N + 1) - j - 1
  let a := j - (N + 1)
  have hn : N + 1 = c + a + 1 := by dsimp [c, a]; omega
  have hj' : j = c + 1 + 2 * a := by dsimp [c, a]; omega
  rw [hn, hj', noZero_parameter_count]
  by_cases ha : a ≤ c + 1
  · have he : c + a + 1 = (c + 1) + a := by exact Nat.add_right_comm c a 1
    rw [he, zeroFree_parameters (c + 1) a (by omega) ha]
    simp only [Nat.cast_add, Nat.cast_one]
  · have hchoose : (c + 1).choose a = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hR : ((c + 1 + 2 * a : ℕ) : ℤ) - ((c + a + 1 : ℕ) : ℤ) = a := by push_cast; ring
    have hguard : ¬ (0 ≤ (a : ℤ) ∧ 2 * (a : ℤ) ≤ ((c + a + 1 : ℕ) : ℤ) ∧
        0 < 2 * ((c + a + 1 : ℕ) : ℤ) - ((c + 1 + 2 * a : ℕ) : ℤ)) := by omega
    have hz : zeroFree (c + a + 1) (c + 1 + 2 * a) = 0 := by
      unfold zeroFree
      rw [hR, if_neg hguard]
    rw [hz, hchoose]
    simp

private def positiveRefinedParameterEquiv {N j m b c a : ℕ} (hm : 0 < m)
    (hlen : N + 1 = m + c + a + 2 * b) (hweight : j = c + 2 * a + 4 * b) :
    PositiveRefined (N + 1) j a b ≃ RefinedCycle N m b c a :=
  Equiv.subtypeEquivRight (fun y => by
    constructor
    · intro hy
      have hbound := zeroContaining_inventory_bounds y hy.1 hy.2.2.1
      have hsum := labelCount_sum y
      have hw := weight_eq_labelCount y
      rw [hy.2.1] at hw
      refine ⟨hy.1, ?_, ?_, ?_, hy.2.2.2.1⟩ <;> omega
    · intro hy
      have hz : ∃ i, y i = 0 := by
        have hh : 0 < labelCount y 0 := by rw [hy.2.1]; exact hm
        unfold labelCount at hh
        obtain ⟨i, hi⟩ := Finset.card_pos.mp hh
        exact ⟨i, (Finset.mem_filter.mp hi).2⟩
      refine ⟨hy.1, ?_, hz, hy.2.2.2.2, ?_⟩
      · rw [weight_eq_labelCount, hy.2.2.1, hy.2.2.2.1, hweight]
        omega
      · rw [hy.2.2.2.1, hy.2.2.2.2]
        omega)

private theorem positive_refined_gapTerm {N j m b c a : ℕ} (hb : b < m)
    (hlen : N + 1 = m + c + a + 2 * b) (hweight : j = c + 2 * a + 4 * b) :
    (Nat.card (PositiveRefined (N + 1) j a b) : ℚ) = gapTerm (N + 1) j a b := by
  rw [Nat.card_congr (positiveRefinedParameterEquiv (by omega) hlen hweight), hweight]
  exact refined_cycle_gapTerm hb hlen

private theorem positive_refined_exceptional {N j b : ℕ} (hb : 0 < b)
    (hlen : N + 1 = 3 * b) (hweight : j = 4 * b) :
    Nat.card (PositiveRefined (N + 1) j 0 b) = 3 := by
  rw [Nat.card_congr (positiveRefinedParameterEquiv (m := b) (c := 0) hb
    (by omega) (by omega))]
  have hN : N = 3 * b - 1 := by exact Nat.eq_sub_of_add_eq hlen
  rw [hN]
  exact allExceptional_refined_card b hb

private def exceptionalIndicator (n j a b : ℕ) : ℚ :=
  if n = 3 * b ∧ j = 4 * b ∧ a = 0 ∧ 0 < b then 3 else 0

private theorem positive_refined_formula (N j a b : ℕ) :
    (Nat.card (PositiveRefined (N + 1) j a b) : ℚ) =
      gapTerm (N + 1) j a b + exceptionalIndicator (N + 1) j a b := by
  let C : ℤ := (j : ℤ) - 2 * (a : ℤ) - 4 * (b : ℤ)
  let T : ℤ := ((N + 1 : ℕ) : ℤ) - (j : ℤ) + (a : ℤ) + (b : ℤ)
  by_cases hg : 0 ≤ C ∧ 1 ≤ T
  · let c := C.toNat
    let m := (T + (b : ℤ)).toNat
    have hc : (c : ℤ) = C := Int.toNat_of_nonneg hg.1
    have hm : (m : ℤ) = T + (b : ℤ) := Int.toNat_of_nonneg (by omega)
    have hb : b < m := by omega
    have hn : N + 1 = m + c + a + 2 * b := by dsimp [C, T] at hc hm; omega
    have hj : j = c + 2 * a + 4 * b := by dsimp [C] at hc; omega
    have he : exceptionalIndicator (N + 1) j a b = 0 := by
      apply if_neg
      dsimp [T] at hg
      omega
    rw [he, add_zero]
    exact positive_refined_gapTerm hb hn hj
  · have hgap : gapTerm (N + 1) j a b = 0 := by
      change (if 0 ≤ C ∧ 1 ≤ T then _ else _) = _
      rw [if_neg hg]
    rw [hgap, zero_add]
    by_cases hex : Nonempty (PositiveRefined (N + 1) j a b)
    · obtain ⟨y⟩ := hex
      have hby := y.prop.2.2.2.1
      have hwy := y.prop.2.1
      have hay := y.prop.2.2.2.2
      have hp := positive_refined_equiv_pred y.val y.prop.1 y.prop.2.1
        y.prop.2.2.1 y.prop.2.2.2.1 y.prop.2.2.2.2
      have hb := zeroContaining_inventory_bounds y.val y.prop.1 y.prop.2.2.1
      have hmpos : 0 < labelCount y.val 0 := by
        unfold labelCount
        exact Finset.card_pos.mpr (by
          obtain ⟨i, hi⟩ := y.prop.2.2.1
          exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩)
      have hC : C = (labelCount y.val 1 : ℤ) := hp.2.1.symm
      have hT : T = (labelCount y.val 0 : ℤ) - (b : ℤ) := by
        dsimp [T]
        omega
      have hb0 : doubleTwoCount y.val = labelCount y.val 0 := by
        dsimp [C, T] at hg
        omega
      have hall := zeroContaining_all_exceptional y.val y.prop.1 y.prop.2.2.1 hb0
      have hn : N + 1 = 3 * b := by have := labelCount_sum y.val; omega
      have hj : j = 4 * b := by have := weight_eq_labelCount y.val; omega
      have ha : a = 0 := by omega
      have hbpos : 0 < b := by omega
      subst a
      rw [positive_refined_exceptional hbpos hn hj]
      simp [exceptionalIndicator, hn, hj, hbpos]
    · letI : IsEmpty (PositiveRefined (N + 1) j a b) := not_nonempty_iff.mp hex
      have hcard : Nat.card (PositiveRefined (N + 1) j a b) = 0 := by simp
      have he : ¬ (N + 1 = 3 * b ∧ j = 4 * b ∧ a = 0 ∧ 0 < b) := by
        rintro ⟨hn, hj, rfl, hb⟩
        have hh := positive_refined_exceptional hb hn hj
        rw [hcard] at hh
        omega
      simp [hcard, exceptionalIndicator, he]

private theorem exceptionalIndicator_sum_a (n j b : ℕ) :
    (∑ a ∈ Finset.range (j + 1), exceptionalIndicator n j a b) =
      if n = 3 * b ∧ j = 4 * b ∧ 0 < b then 3 else 0 := by
  calc
    _ = exceptionalIndicator n j 0 b := by
      apply Finset.sum_eq_single 0
      · intro a ha hne
        simp [exceptionalIndicator, hne]
      · intro h
        simp at h
    _ = _ := by simp [exceptionalIndicator]

private theorem exceptionalIndicator_sum (n j : ℕ) (hn : 3 ≤ n) :
    (∑ b ∈ Finset.range (j + 1), ∑ a ∈ Finset.range (j + 1),
      exceptionalIndicator n j a b) = allExceptional n j := by
  simp_rw [exceptionalIndicator_sum_a]
  by_cases hg : n % 3 = 0 ∧ 3 * j = 4 * n
  · have hn' : n = 3 * (n / 3) := by omega
    have hj' : j = 4 * (n / 3) := by omega
    have hbpos : 0 < n / 3 := by omega
    have hbmem : n / 3 ∈ Finset.range (j + 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single (n / 3)]
    · simp only [if_pos (show n = 3 * (n / 3) ∧ j = 4 * (n / 3) ∧ 0 < n / 3 from ⟨hn', hj', hbpos⟩), allExceptional, if_pos hg]
    · intro b hb hne
      apply if_neg
      omega
    · intro hnot
      exact (hnot hbmem).elim
  · have hall : ∀ b : ℕ, ¬ (n = 3 * b ∧ j = 4 * b ∧ 0 < b) := by
      intro b hb
      apply hg
      refine ⟨?_, ?_⟩
      · rw [hb.1]
        simp
      · omega
    simp [allExceptional, hg, hall]

theorem result : claim := by
  intro n j hn hj
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  rw [coefficient_zero_partition (N + 1) j hj, Nat.cast_add,
    positive_coefficient_partition N j]
  simp only [Nat.cast_sum]
  rw [noZeroCoefficient_card hj]
  simp_rw [positive_refined_formula]
  simp_rw [Finset.sum_add_distrib]
  rw [exceptionalIndicator_sum (N + 1) j (by omega)]
  unfold closedForm
  ring

end D5.S3.Combinatorics.Graph.ItalianDomination.CycleDeficit
