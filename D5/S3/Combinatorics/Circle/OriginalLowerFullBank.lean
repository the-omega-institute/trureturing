/- GID: D5/S3/Combinatorics/Circle/OriginalLowerFullBank
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/OriginalLowerFullBank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Original-source full-b LOWER selection and exact depleted w support. -/
module
public import D5.S3.Combinatorics.Circle.M5SourceRows
public import D5.S3.Combinatorics.Circle.SourcePrefixInventory
import all D5.S3.Combinatorics.Circle.M5SourceRows
import all D5.S3.Combinatorics.Circle.ZeroSumSubsets

/-! # A full retained bank for original LOWER sources

All words are mapped from the bounded actual physical occurrence inventory.
The least rounding coefficient preserves the entire positive b row; the
residual source recurrence determines literal retained w support.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace D5.S3.Combinatorics.Circle.OriginalLowerFullBank
open SourceWidth M5FullWordConsumer SourcePrefixInventory
open Fin.NatCast
open scoped BigOperators

structure OriginalSource (m k t L : ℕ) (a b : ℤ) (p d x : Fin k) : Prop where
  pairs : 5 ≤ m
  nonzero : ∀ i : Fin k, actualSource k t i ≠ 0
  a_positive : 0 < a
  minimum_inequalities : a < b ∧ b < 2 * a
  negative_minimum : ∀ i, actualSource k t i < 0 → a ≤ -actualSource k t i
  positive_minimum : ∀ i, 0 < actualSource k t i → b ≤ actualSource k t i
  negative_attained : ∃ i, actualSource k t i = -a
  positive_attained : ∃ i, actualSource k t i = b
  p_maximum : ∀ i, actualSource k t i ≤ actualSource k t p
  d_minimum : ∀ i, actualSource k t d ≤ actualSource k t i
  positive_count : (Finset.univ.filter (fun i : Fin k => quarter k ≤ actualSource k t i)).card = m
  negative_count : (Finset.univ.filter (fun i : Fin k => actualSource k t i ≤ -quarter k)).card = m
  x_positive_large : quarter k ≤ actualSource k t x
  incoming_d : sourceParent t x 1 = d
  p_row : OwnRow k t p L
  x_row_length : sourceLength t x 0 = L
  d_row_length : sourceLength t x 1 = L
  beta_row_length : sourceLength t x 2 = L
  gamma_row_short : sourceLength t x 3 < L
  c0_hard : 2 * a < modulus k - (2 : ℤ) ^ (L + 1) * a
  beta_alternative : 2 ≤ L ∨ sourceParent t x 2 ≠ p
  delta_positive : 0 < b - (modulus k - 2 * actualSource k t x)
  delta_hard : a - 1 < (((2 : ℤ) ^ (L + 1)) ^ 2 + 1) *
    (b - (modulus k - 2 * actualSource k t x))
  b1_hard : 2 * a - 1 ≤ sourceSeed t x 3
  w_bounds : a ≤ modulus k - 2 * actualSource k t (sourceParent t x 4) ∧
    modulus k - 2 * actualSource k t (sourceParent t x 4) ≤ 2 * a - 3
  w_hard : sourceSeed t x 2 + (b - (modulus k - 2 * actualSource k t x)) <
    modulus k - 2 * actualSource k t (sourceParent t x 4)
  w_row_length : sourceLength t x 4 = L - 1
  nonET : ∃ i : Fin k, sourceOffset t x 7 ≤ i.val ∧
    actualSource k t (advance x i.val) < 0 ∧
    |actualSource k t (advance x i.val)| < quarter k
  u_above_z : modulus k - 2 * actualSource k t x <
    modulus k - 2 * actualSource k t (sourceParent t x 6)
  power_branch :
    ((2 : ℤ) ^ (sourceLength t x 6 + 1) = (2 : ℤ) ^ (L + 1) / 2 ∧
      4 ≤ (2 : ℤ) ^ (L + 1) / 2) ∨
    (2 : ℤ) ^ (sourceLength t x 6 + 1) ≤ (2 : ℤ) ^ (L + 1) / 4
/-- Computed numerical coordinates of the unchanged physical source. -/
structure Coordinates where
  N : ℤ
  Q : ℤ
  C : ℤ
  a : ℤ
  b : ℤ
  q : ℤ
  H : ℤ
  z : ℤ
  n : ℤ
  Δ : ℤ
  b1 : ℤ
  r : ℤ
  w : ℤ
  v : ℤ
  e : ℤ
  u : ℤ
  F : ℤ
  y : ℤ
  a0 : ℤ

/-- Coordinates are computed directly; no selector or gate is an input. -/
def sourceCoordinates {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (_h : OriginalSource m k t L a b p d x) : Coordinates where
  N := modulus k
  Q := quarter k
  C := halfCapacity k
  a := a
  b := b
  q := (2 : ℤ) ^ L
  H := (2 : ℤ) ^ (L + 1)
  z := sourceSeed t x 0
  n := sourceSeed t x 2
  Δ := b - sourceSeed t x 0
  b1 := sourceSeed t x 3
  r := (2 : ℤ) ^ sourceLength t x 3
  w := sourceSeed t x 4
  v := sourceSeed t x 5
  e := (2 : ℤ) ^ sourceLength t x 5
  u := sourceSeed t x 6
  F := (2 : ℤ) ^ (sourceLength t x 6 + 1)
  y := sourceSeed t x 7
  a0 := sourceSeed t x 8

private theorem source_count {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) :
    2 ≤ k ∧ (largeOffsets t x).card = (2 * m) := by
  have hm_pairs := h.pairs
  have hkm : m ≤ k := by
    have hh := (Finset.univ.filter
      (fun i : Fin k => quarter k ≤ actualSource k t i)).card_le_univ
    simpa only [h.positive_count, Fintype.card_fin] using hh
  have hm := h.pairs
  have hk : 2 ≤ k := by omega
  have hQ := (modulus_quarter k hk).2.2.2
  let pos := Finset.univ.filter (fun i : Fin k => quarter k ≤ actualSource k t i)
  let neg := Finset.univ.filter (fun i : Fin k => actualSource k t i ≤ -quarter k)
  have hd : Disjoint pos neg := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [pos, neg, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    omega
  have hu : (Finset.univ.filter
      (fun i : Fin k => quarter k ≤ |actualSource k t i|)) = pos ∪ neg := by
    ext i
    simp only [pos, neg, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rw [le_abs]
    omega
  refine ⟨hk, ?_⟩
  rw [large_offsets_card x, hu, Finset.card_union_of_disjoint hd]
  simpa only [two_mul] using congrArg₂ (· + ·) h.positive_count h.negative_count

private theorem source_parent_zero {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) : sourceParent t x 0 = x := by
  have hm_pairs := h.pairs
  have hc := (source_count h).2
  have hz := cut_zero x (rfl : (largeOffsets t x).card = (largeOffsets t x).card)
    (by omega) (h.x_positive_large.trans (le_abs_self _))
  change advance x (cut x (largeOffsets t x).card rfl 0) = x
  rw [hz]
  rfl

private theorem source_own_row {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) (i : ℕ) (hi : i < (2 * m)) :
    OwnRow k t (sourceParent t x i) (sourceLength t x i) := by
  have hm_pairs := h.pairs
  have hc := (source_count h).2
  have hx : quarter k ≤ |actualSource k t x| :=
    h.x_positive_large.trans (le_abs_self _)
  have hr := cut_own_row x (rfl : (largeOffsets t x).card = (largeOffsets t x).card)
    hx i (by omega)
  simpa only [sourceParent, sourceOffset, sourceLength] using hr

private theorem source_parent_next {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) (i : ℕ) (hi : i < (2 * m)) :
    advance (sourceParent t x i) (sourceLength t x i + 1) = sourceParent t x (i + 1) := by
  have hm_pairs := h.pairs
  have hc := (source_count h).2
  have hlt := cut_strict x (rfl : (largeOffsets t x).card = (largeOffsets t x).card)
    (show i < i + 1 by omega) (by omega)
  have he : sourceOffset t x i + (sourceLength t x i + 1) = sourceOffset t x (i + 1) := by
    dsimp only [sourceOffset, sourceLength] at *
    omega
  simp only [sourceParent, advance_add, he]

private theorem source_parent_boundary {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) : sourceParent t x (2 * m) = x := by
  have hm_pairs := h.pairs
  have hc := (source_count h).2
  have he : sourceOffset t x (2 * m) = k := by
    simp only [sourceOffset, cut, hc, lt_self_iff_false, dite_false]
  simp only [sourceParent, he, advance_cycle]

private theorem source_parent_sign {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) (i : ℕ) (hi : i ≤ (2 * m)) :
    if i % 2 = 0 then 0 < actualSource k t (sourceParent t x i)
      else actualSource k t (sourceParent t x i) < 0 := by
  have hm_pairs := h.pairs
  have hk := (source_count h).1
  induction i with
  | zero =>
    simp only [Nat.zero_mod, ite_true, source_parent_zero h]
    exact lt_of_lt_of_le (modulus_quarter k hk).2.2.2 h.x_positive_large
  | succ i ih =>
    have ih' := ih (by omega)
    have hr := source_own_row h i (by omega)
    have hn := source_parent_next h i (by omega)
    by_cases he : i % 2 = 0
    · have hne : (i + 1) % 2 ≠ 0 := by omega
      simp only [he, ite_true] at ih'
      simp only [hne, ite_false]
      rw [← hn]
      exact row_positive_terminal hk hr ih'
    · have hnz : (i + 1) % 2 = 0 := by omega
      simp only [he, ite_false] at ih'
      simp only [hnz, ite_true]
      rw [← hn]
      exact row_negative_terminal hk hr ih'

private theorem source_parent_large {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) (i : ℕ) (hi : i ≤ (2 * m)) :
    quarter k ≤ |actualSource k t (sourceParent t x i)| := by
  have hm_pairs := h.pairs
  by_cases hin : i < (2 * m)
  · exact (source_own_row h i hin).parent_large
  · have he : i = (2 * m) := by omega
    simpa only [he, source_parent_boundary h] using
      h.x_positive_large.trans (le_abs_self _)

private theorem source_seed_formula {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) (i : ℕ) (hi : i ≤ (2 * m)) :
    sourceSeed t x i =
      if i % 2 = 0 then modulus k - 2 * actualSource k t (sourceParent t x i)
        else modulus k + 2 * actualSource k t (sourceParent t x i) := by
  have hm_pairs := h.pairs
  have hk := (source_count h).1
  have hlarge := source_parent_large h i hi
  have hsign := source_parent_sign h i hi
  by_cases he : i % 2 = 0
  · simp only [he, ite_true] at hsign ⊢
    rw [abs_of_pos hsign] at hlarge
    have hs := source_positive_step k t hk _ hlarge
    rw [sourceSeed, abs_of_neg hs.2, hs.1]
    ring
  · simp only [he, ite_false] at hsign ⊢
    rw [abs_of_neg hsign] at hlarge
    have hs := source_negative_step k t hk (sourceParent t x i) (by omega)
    rw [sourceSeed, abs_of_pos hs.2, hs.1]
    ring

private theorem source_terminal_formula {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) (i : ℕ) (hi : i < (2 * m)) :
    actualSource k t (sourceParent t x (i + 1)) =
      if i % 2 = 0 then -(2 : ℤ) ^ sourceLength t x i * sourceSeed t x i
        else (2 : ℤ) ^ sourceLength t x i * sourceSeed t x i := by
  have hm_pairs := h.pairs
  have hk := (source_count h).1
  have hs := source_parent_sign h i (by omega)
  have hl := source_parent_large h i (by omega)
  rw [← source_parent_next h i hi, row_terminal hk (source_own_row h i hi)]
  by_cases he : i % 2 = 0
  · simp only [he, ite_true] at hs ⊢
    rw [abs_of_pos hs] at hl
    have hn := (source_positive_step k t hk _ hl).2
    rw [sourceSeed, abs_of_neg hn]
    ring
  · simp only [he, ite_false] at hs ⊢
    rw [abs_of_neg hs] at hl
    have hn := (source_negative_step k t hk (sourceParent t x i) (by omega)).2
    rw [sourceSeed, abs_of_pos hn]

private theorem source_seed_recurrence {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) (i : ℕ) (hi : i < (2 * m)) :
    sourceSeed t x (i + 1) = modulus k -
      (2 : ℤ) ^ (sourceLength t x i + 1) * sourceSeed t x i := by
  have hm_pairs := h.pairs
  rw [source_seed_formula h (i + 1) (by omega), source_terminal_formula h i hi]
  by_cases he : i % 2 = 0
  · have hn : (i + 1) % 2 ≠ 0 := by omega
    simp only [he, hn, ite_true, ite_false, pow_succ]
    ring
  · have hn : (i + 1) % 2 = 0 := by omega
    simp only [he, hn, ite_true, ite_false, pow_succ]
    ring

private theorem source_seed_one {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) : sourceSeed t x 1 = b := by
  have hm_pairs := h.pairs
  have hk := (source_count h).1
  have hd := (source_extrema k t hk a b h.a_positive
    (lt_trans h.a_positive h.minimum_inequalities.1) h.negative_minimum
    h.positive_minimum h.negative_attained h.positive_attained p d
    h.p_maximum h.d_minimum).2.2.2
  have hs := source_seed_formula h 1 (by omega)
  simp only [Nat.one_mod, one_ne_zero, ite_false, h.incoming_d] at hs
  omega

private theorem source_seed_minimum {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) (i : ℕ) (hi : i ≤ (2 * m)) :
    if i % 2 = 0 then a ≤ sourceSeed t x i else b ≤ sourceSeed t x i := by
  have hm_pairs := h.pairs
  have hk := (source_count h).1
  have hs := source_parent_sign h i hi
  have hl := source_parent_large h i hi
  by_cases he : i % 2 = 0
  · simp only [he, ite_true] at hs ⊢
    rw [abs_of_pos hs] at hl
    have hn := (source_positive_step k t hk _ hl).2
    simpa only [sourceSeed, abs_of_neg hn] using h.negative_minimum _ hn
  · simp only [he, ite_false] at hs ⊢
    rw [abs_of_neg hs] at hl
    have hn := (source_negative_step k t hk (sourceParent t x i) (by omega)).2
    simpa only [sourceSeed, abs_of_pos hn] using h.positive_minimum _ hn

private theorem source_seed_odd {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) (i : ℕ) (hi : i ≤ (2 * m)) :
    sourceSeed t x i % 2 = 1 := by
  have hm_pairs := h.pairs
  have hk := (source_count h).1
  have hN := (modulus_quarter k hk).1
  rw [source_seed_formula h i hi]
  split_ifs <;> omega

private theorem source_core {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) :
    let H := (2 : ℤ) ^ (L + 1)
    let z := sourceSeed t x 0
    let n := sourceSeed t x 2
    let Δ := b - z
    8 ≤ H ∧ 2 ≤ L ∧ 2 ≤ Δ ∧ Δ % 2 = 0 ∧
      modulus k = H * z + b ∧ modulus k = H * b + n ∧
      z = n + (H - 1) * Δ ∧ b = n + H * Δ ∧
      sourceSeed t x 3 = n + H ^ 2 * Δ ∧
      a ≤ n ∧ n < z ∧ z < b ∧ H * Δ < n := by
  have hm_pairs := h.pairs
  let H := (2 : ℤ) ^ (L + 1)
  let z := sourceSeed t x 0
  let n := sourceSeed t x 2
  let Δ := b - z
  change 8 ≤ H ∧ 2 ≤ L ∧ 2 ≤ Δ ∧ Δ % 2 = 0 ∧
    modulus k = H * z + b ∧ modulus k = H * b + n ∧
    z = n + (H - 1) * Δ ∧ b = n + H * Δ ∧
    sourceSeed t x 3 = n + H ^ 2 * Δ ∧
    a ≤ n ∧ n < z ∧ z < b ∧ H * Δ < n
  have hz : z = modulus k - 2 * actualSource k t x := by
    simpa only [z, Nat.zero_mod, ite_true, source_parent_zero h] using
      source_seed_formula h 0 (by omega)
  have hF : 2 ≤ (2 : ℤ) ^ (sourceLength t x 6 + 1) := by
    rw [pow_succ]
    have hp : (1 : ℤ) ≤ 2 ^ sourceLength t x 6 :=
      one_le_pow₀ (by omega)
    omega
  have hH : 8 ≤ H := by
    dsimp only [H]
    rcases h.power_branch with ⟨_, hh⟩ | hh <;> omega
  have hL : 2 ≤ L := by
    by_contra hn
    have hl : L = 0 ∨ L = 1 := by omega
    rcases hl with rfl | rfl <;> norm_num [H] at hH
  have h0 : b = modulus k - H * z := by
    simpa only [Nat.zero_add, h.x_row_length, source_seed_one h, H, z] using
      source_seed_recurrence h 0 (by omega)
  have h1 : n = modulus k - H * b := by
    simpa only [h.d_row_length, source_seed_one h, H, n] using
      source_seed_recurrence h 1 (by omega)
  have h2 : sourceSeed t x 3 = modulus k - H * n := by
    simpa only [h.beta_row_length, H, n] using
      source_seed_recurrence h 2 (by omega)
  have hΔ : 0 < Δ := by simpa only [Δ, hz] using h.delta_positive
  have hoddz := source_seed_odd h 0 (by omega)
  have hoddb : b % 2 = 1 := by
    simpa only [source_seed_one h] using source_seed_odd h 1 (by omega)
  have hΔeven : Δ % 2 = 0 := by dsimp only [Δ, z]; omega
  have hΔ2 : 2 ≤ Δ := by omega
  have hn : a ≤ n := by
    simpa only [n, Nat.reduceMod, ite_true] using source_seed_minimum h 2 (by omega)
  have hb : b < 2 * a := h.minimum_inequalities.2
  have hzb : z = n + (H - 1) * Δ := by dsimp only [Δ]; nlinarith only [h0, h1]
  have hbn : b = n + H * Δ := by dsimp only [Δ]; nlinarith only [h0, h1]
  have hb1 : sourceSeed t x 3 = n + H ^ 2 * Δ := by
    nlinarith only [h1, h2, congrArg (fun v : ℤ => H * v) hbn]
  refine ⟨hH, hL, hΔ2, hΔeven, by omega, by omega, hzb, hbn, hb1, hn, ?_, ?_, ?_⟩
  · nlinarith only [hzb, hH, hΔ2]
  · dsimp only [Δ] at hΔ
    omega
  · nlinarith only [hbn, hb, hn]

private theorem source_partition {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) :
    ((List.range (2 * m)).flatMap (fun i => sourceParent t x i ::
      rowLabels (sourceParent t x i) (sourceLength t x i))).Perm (List.finRange k) := by
  have hm_pairs := h.pairs
  let M := (largeOffsets t x).card
  have hc : M = (2 * m) := (source_count h).2
  have hm : 0 < M := by omega
  have hx := h.x_positive_large.trans (le_abs_self _)
  have hp := cut_arc_partition x (rfl : (largeOffsets t x).card = M) hm hx
  have he : ((List.range M).flatMap (fun i =>
      arc x (cut x M rfl i) (cut x M rfl (i + 1) - cut x M rfl i))) =
      ((List.range M).flatMap (fun i => sourceParent t x i ::
        rowLabels (sourceParent t x i) (sourceLength t x i))) := by
    apply List.flatMap_congr
    intro i hi
    have hil : i < M := List.mem_range.mp hi
    have hlt := cut_strict x (rfl : (largeOffsets t x).card = M)
      (show i < i + 1 by omega) (by omega)
    have hlen : cut x M rfl (i + 1) - cut x M rfl i = sourceLength t x i + 1 := by
      dsimp only [sourceLength, sourceOffset]
      change cut x M rfl (i + 1) - cut x M rfl i =
        cut x M rfl (i + 1) - cut x M rfl i - 1 + 1
      dsimp only [M] at hlt ⊢
      omega
    rw [hlen, arc_row]
    rfl
  rw [he] at hp
  simpa only [hc] using hp

private def sourcePrefixArithmetic {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) : PrefixArithmetic := by
  have hm_pairs := h.pairs
  let N := modulus k
  let Q := quarter k
  let C := halfCapacity k
  let q := (2 : ℤ) ^ L
  let H := (2 : ℤ) ^ (L + 1)
  let z := sourceSeed t x 0
  let n := sourceSeed t x 2
  let Δ := b - z
  let b1 := sourceSeed t x 3
  let r := (2 : ℤ) ^ sourceLength t x 3
  let w := sourceSeed t x 4
  let v := sourceSeed t x 5
  let e := (2 : ℤ) ^ sourceLength t x 5
  let u := sourceSeed t x 6
  let F := (2 : ℤ) ^ (sourceLength t x 6 + 1)
  let y := sourceSeed t x 7
  have hk := (source_count h).1
  obtain ⟨hH8, hL2, hΔ2, hΔeven, hNz, hNb, hzn, hbn, hb1n, hna, hnz, hzb, hΔn⟩ :=
    source_core h
  have hNQ : N = 4 * Q - 1 := (modulus_quarter k hk).1
  have hCQ : C = 2 * Q - 1 := (modulus_quarter k hk).2.1
  have hQ : 0 < Q := (modulus_quarter k hk).2.2.2
  have hHq : H = 2 * q := by dsimp only [H, q]; rw [pow_succ]; ring
  have hHpow : H = 4 * (2 : ℤ) ^ (L - 1) := by
    dsimp only [H]
    rw [show L + 1 = (L - 1) + 2 by omega, pow_add]
    norm_num
    ring
  have hHdiv : H / 4 = (2 : ℤ) ^ (L - 1) := by omega
  have hHcases : H = 8 ∨ H = 16 ∨ 32 ≤ H := by
    by_cases hL : L = 2
    · left; simp [H, hL]
    · by_cases hL3 : L = 3
      · right; left; simp [H, hL3]
      · right; right
        have hh := pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2)
          (show 5 ≤ L + 1 by omega)
        norm_num at hh
        exact hh
  have hzraw : z = N - 2 * actualSource k t x := by
    simpa only [z, Nat.zero_mod, ite_true, source_parent_zero h] using
      source_seed_formula h 0 (by omega)
  have hwraw : w = N - 2 * actualSource k t (sourceParent t x 4) := by
    simpa only [w, Nat.reduceMod, ite_true] using source_seed_formula h 4 (by omega)
  have huraw : u = N - 2 * actualSource k t (sourceParent t x 6) := by
    simpa only [u, Nat.reduceMod, ite_true] using source_seed_formula h 6 (by omega)
  have hwsource : w = N - 2 * r * b1 := by
    have hh := source_seed_recurrence h 3 (by omega)
    rw [pow_succ] at hh
    change w = N - (r * 2) * b1 at hh
    nlinarith only [hh]
  have hvsource : v = N - q * w := by
    have hh := source_seed_recurrence h 4 (by omega)
    rw [h.w_row_length, Nat.sub_add_cancel (show 1 ≤ L by omega)] at hh
    exact hh
  have husource : u = N - 2 * e * v := by
    have hh := source_seed_recurrence h 5 (by omega)
    rw [pow_succ] at hh
    change u = N - (e * 2) * v at hh
    nlinarith only [hh]
  have hysource : y = N - F * u := source_seed_recurrence h 6 (by omega)
  have hr1 : 1 ≤ r := one_le_pow₀ (by omega)
  have hrH : r ≤ H / 4 := by
    rw [hHdiv]
    exact pow_le_pow_right₀ (by omega) (show sourceLength t x 3 ≤ L - 1 by
      have hh := h.gamma_row_short
      omega)
  have he1 : 1 ≤ e := one_le_pow₀ (by omega)
  have hF2 : 2 ≤ F := by
    dsimp only [F]
    rw [pow_succ]
    have hh : (1 : ℤ) ≤ 2 ^ sourceLength t x 6 := one_le_pow₀ (by omega)
    omega
  have hext := source_extrema k t hk a b h.a_positive
    (lt_trans h.a_positive h.minimum_inequalities.1) h.negative_minimum
    h.positive_minimum h.negative_attained h.positive_attained p d
    h.p_maximum h.d_minimum
  have ht : actualSource k t (sourceParent t x 6) = e * v := by
    simpa only [Nat.reduceMod, one_ne_zero, ite_false] using source_terminal_formula h 5 (by omega)
  have hTmax : 2 * e * v ≤ N - a := by
    have hh := h.p_maximum (sourceParent t x 6)
    rw [ht] at hh
    nlinarith only [hh, hext.2.2.1]
  have hUvalue : F * u = -2 * actualSource k t (sourceParent t x 7) := by
    have hh := source_terminal_formula h 6 (by omega)
    norm_num only [Nat.reduceMod, ite_true] at hh
    dsimp only [F]
    rw [pow_succ]
    nlinarith only [hh]
  have hUneg : actualSource k t (sourceParent t x 7) < 0 := by
    simpa only [Nat.reduceMod, one_ne_zero, ite_false] using source_parent_sign h 7 (by omega)
  have hUthreshold : N + 1 ≤ 2 * F * u := by
    have hh := source_parent_large h 7 (by omega)
    rw [abs_of_neg hUneg] at hh
    nlinarith only [hh, hUvalue, hNQ]
  have hUmax : F * u ≤ H * z := by
    have hh := h.d_minimum (sourceParent t x 7)
    nlinarith only [hh, hUvalue, hext.2.2.2, hNz]
  have hubound : u ≤ C := by
    exact abs_le.mpr (source_bounds k t hk (advance (sourceParent t x 6) 1))
  have hvb : b ≤ v := by
    simpa only [Nat.reduceMod, one_ne_zero, ite_false] using source_seed_minimum h 5 (by omega)
  have hyb : b ≤ y := by
    simpa only [Nat.reduceMod, one_ne_zero, ite_false] using source_seed_minimum h 7 (by omega)
  have hwb := h.w_bounds
  have hwh := h.w_hard
  have hua := h.u_above_z
  have hδhard := h.delta_hard
  rw [← hwraw] at hwb
  rw [← hzraw, ← hwraw] at hwh
  rw [← hzraw, ← huraw] at hua
  rw [← hzraw] at hδhard
  exact {
    N := N, Q := Q, C := C, a := a, b := b, q := q, H := H,
    z := z, n := n, Δ := Δ, b1 := b1, r := r, w := w, v := v, e := e,
    u := u, F := F, y := y,
    N_quarter := hNQ, C_quarter := hCQ, Q_positive := hQ,
    H_q := hHq, H_four := by omega, H_eight := hH8, H_cases := hHcases,
    a_positive := h.a_positive, ab := h.minimum_inequalities,
    n_minimum := hna, nzb := ⟨hnz, hzb⟩,
    delta_two := hΔ2, delta_even := hΔeven, delta_n := hΔn,
    N_z := hNz, N_b := hNb, z_n := hzn, b_n := hbn, b1_n := hb1n,
    c0_hard := h.c0_hard, delta_hard := hδhard, b1_hard := h.b1_hard,
    w_bounds := hwb, w_hard := hwh, r_bounds := ⟨hr1, hrH⟩,
    w_source := hwsource, v_source := hvsource, v_minimum := hvb,
    e_one := he1, u_source := husource, T_maximum := hTmax,
    F_two := hF2, U_threshold := hUthreshold, U_maximum := hUmax,
    u_above := hua, u_bound := hubound, branch := h.power_branch,
    y_source := hysource, y_minimum := hyb,
    odd_z := source_seed_odd h 0 (by omega),
    odd_n := source_seed_odd h 2 (by omega),
    odd_b := by simpa only [source_seed_one h] using source_seed_odd h 1 (by omega),
    odd_w := source_seed_odd h 4 (by omega),
    odd_u := source_seed_odd h 6 (by omega) }

private def physical {k t : ℕ} (x : Fin k) :
    Occ (fun i : ℕ => sourceLength t x i) → Fin k
  | .inl i => sourceParent t x i
  | .inr ⟨i, j⟩ => advance (sourceParent t x i) (j.val + 1)

private def occurrences (M : ℕ) (len : ℕ → ℕ) : List (Occ len) :=
  (List.range M).flatMap (fun i => Sum.inl i :: List.ofFn (fun j => Sum.inr ⟨i, j⟩))

private theorem mem_occurrences {M : ℕ} {len : ℕ → ℕ} {o : Occ len} :
    o ∈ occurrences M len ↔ (match o with | .inl i => i < M | .inr p => p.1 < M) := by
  rcases o with i | ⟨i, j⟩
  · simp [occurrences]
  · simp [occurrences]

private theorem physical_inventory {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) :
    ((occurrences (2 * m) (fun i => sourceLength t x i)).map (physical x)).Perm
      (List.finRange k) := by
  have hp := source_partition h
  have he : (occurrences (2 * m) (fun i => sourceLength t x i)).map (physical x) =
      (List.range (2 * m)).flatMap (fun i => sourceParent t x i ::
        rowLabels (sourceParent t x i) (sourceLength t x i)) := by
    simp only [occurrences, List.map_flatMap, List.map_cons, List.map_ofFn,
      physical, rowLabels, Function.comp_apply]
    rfl
  rw [he]
  exact hp

private theorem physical_injective_on {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) :
    Set.InjOn (physical (t := t) x)
      {o | o ∈ occurrences (2 * m) (fun i => sourceLength t x i)} := by
  have hn := (physical_inventory h).nodup_iff.mpr (List.nodup_finRange k)
  exact fun o ho o' ho' he => List.inj_on_of_nodup_map hn ho ho' he

private def sourceData {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) : RowData naturalRows (sourcePrefixArithmetic h) := by
  classical
  let len := fun i : ℕ => sourceLength t x i
  let f := fun o : Occ len => actualSource k t (physical x o)
  let base := fun i : ℕ => actualSource k t (advance (sourceParent t x i) 1)
  have hm_pairs := h.pairs
  have hk := (source_count h).1
  have hbase (i : ℕ) (hi : i < 2 * m) : base i =
      if i % 2 = 0 then -sourceSeed t x i else sourceSeed t x i := by
    have hs := source_parent_sign h i (by omega)
    have hl := source_parent_large h i (by omega)
    by_cases hi : i % 2 = 0
    · simp only [hi, ite_true] at hs ⊢
      rw [abs_of_pos hs] at hl
      have hn := (source_positive_step k t hk _ hl).2
      dsimp only [base, sourceSeed]
      rw [abs_of_neg hn, neg_neg]
    · simp only [hi, ite_false] at hs ⊢
      rw [abs_of_neg hs] at hl
      have hn := (source_negative_step k t hk (sourceParent t x i) (by omega)).2
      dsimp only [base, sourceSeed]
      rw [abs_of_pos hn]
  have hp4 : (2 : ℤ) ^ len 4 = (sourcePrefixArithmetic h).H / 4 := by
    have hL := (source_core h).2.1
    change (2 : ℤ) ^ sourceLength t x 4 = (2 : ℤ) ^ (L + 1) / 4
    rw [h.w_row_length, show L + 1 = (L - 1) + 2 by omega, pow_add]
    norm_num
  refine {
    len := len, f := f, base := base,
    values := ?_, small := ?_, bound := ?_,
    base0 := ?_, base1 := ?_, base2 := ?_, base3 := ?_,
    base4 := ?_, base5 := ?_, base6 := ?_,
    pow0 := ?_, pow1 := ?_, pow2 := ?_, pow3 := rfl, pow4 := hp4,
    pow5 := rfl, pow6 := ?_,
    large0 := ?_, large1 := ?_, large2 := ?_, large3 := ?_,
    large4 := ?_, large5 := ?_, large6 := ?_ }
  · intro i j
    by_cases hi : i < 2 * m
    · exact row_value hk (source_own_row h i hi) j.val (Nat.le_of_lt j.isLt)
    · have hz : sourceLength t x i = 0 := by
        have hc := (source_count h).2
        simp [sourceLength, sourceOffset, cut, hc, hi, show ¬ i + 1 < 2 * m by omega]
      have hj := j.isLt
      change j.val < sourceLength t x i at hj
      omega
  · intro i j
    by_cases hi : i < 2 * m
    · exact Int.le_sub_one_of_lt ((source_own_row h i hi).small j.val j.isLt)
    · have hz : sourceLength t x i = 0 := by
        have hc := (source_count h).2
        simp [sourceLength, sourceOffset, cut, hc, hi, show ¬ i + 1 < 2 * m by omega]
      have hj := j.isLt
      change j.val < sourceLength t x i at hj
      omega
  · intro i
    exact abs_le.mpr (source_bounds k t hk (sourceParent t x i))
  · change base 0 = -sourceSeed t x 0
    simpa only [Nat.zero_mod, ite_true] using hbase 0 (by omega)
  · change base 1 = b
    have hb := hbase 1 (by omega)
    norm_num only [Nat.reduceMod, one_ne_zero, ite_false] at hb
    rw [hb, source_seed_one h]
  · change base 2 = -sourceSeed t x 2
    simpa only [Nat.reduceMod, ite_true] using hbase 2 (by omega)
  · change base 3 = sourceSeed t x 3
    simpa only [Nat.reduceMod, one_ne_zero, ite_false] using hbase 3 (by omega)
  · change base 4 = -sourceSeed t x 4
    simpa only [Nat.reduceMod, ite_true] using hbase 4 (by omega)
  · change base 5 = sourceSeed t x 5
    simpa only [Nat.reduceMod, one_ne_zero, ite_false] using hbase 5 (by omega)
  · change base 6 = -sourceSeed t x 6
    simpa only [Nat.reduceMod, ite_true] using hbase 6 (by omega)
  · change (2 : ℤ) ^ sourceLength t x 0 = (2 : ℤ) ^ L
    rw [h.x_row_length]
  · change (2 : ℤ) ^ sourceLength t x 1 = (2 : ℤ) ^ L
    rw [h.d_row_length]
  · change (2 : ℤ) ^ sourceLength t x 2 = (2 : ℤ) ^ L
    rw [h.beta_row_length]
  · change 2 * (2 : ℤ) ^ sourceLength t x 6 = (2 : ℤ) ^ (sourceLength t x 6 + 1)
    rw [pow_succ]; ring
  · change 2 * actualSource k t (sourceParent t x 0) = modulus k - sourceSeed t x 0
    have hh := source_seed_formula h 0 (by omega)
    norm_num only [Nat.zero_mod, ite_true] at hh
    omega
  · change actualSource k t (sourceParent t x 1) = -(2 : ℤ) ^ L * sourceSeed t x 0
    simpa only [Nat.zero_mod, ite_true, h.x_row_length, neg_mul] using
      source_terminal_formula h 0 (by omega)
  · change actualSource k t (sourceParent t x 2) = (2 : ℤ) ^ L * b
    simpa only [Nat.one_mod, one_ne_zero, ite_false, h.d_row_length, source_seed_one h] using
      source_terminal_formula h 1 (by omega)
  · change actualSource k t (sourceParent t x 3) = -(2 : ℤ) ^ L * sourceSeed t x 2
    simpa only [Nat.reduceMod, ite_true, h.beta_row_length, neg_mul] using
      source_terminal_formula h 2 (by omega)
  · change actualSource k t (sourceParent t x 4) =
      (2 : ℤ) ^ sourceLength t x 3 * sourceSeed t x 3
    simpa only [Nat.reduceMod, one_ne_zero, ite_false] using
      source_terminal_formula h 3 (by omega)
  · change actualSource k t (sourceParent t x 5) =
      -((sourcePrefixArithmetic h).H / 4) * sourceSeed t x 4
    rw [← hp4]
    change actualSource k t (sourceParent t x 5) =
      -(2 : ℤ) ^ sourceLength t x 4 * sourceSeed t x 4
    simpa only [Nat.reduceMod, ite_true, neg_mul] using
      source_terminal_formula h 4 (by omega)
  · change 2 * actualSource k t (sourceParent t x 6) = modulus k - sourceSeed t x 6
    have hh := source_seed_formula h 6 (by omega)
    norm_num only [Nat.reduceMod, ite_true] at hh
    omega

private def fullKeep {D : PrefixArithmetic} (R : RowData naturalRows D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (Sz : Finset (Fin (R.len 0))) : Finset (Occ R.len) :=
  rowMask R.len 2 Sn ∪ rowMask R.len 4 Sw ∪ fullRow R 1 ∪ rowMask R.len 0 Sz

private theorem fullKeep_available {D : PrefixArithmetic} (R : RowData naturalRows D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (Sz : Finset (Fin (R.len 0))) : fullKeep R Sn Sw Sz ⊆ bank R Sn Sw := by
  obtain ⟨hn, hw, hz, hb, hv⟩ := bank_parts R Sn Sw
  exact Finset.union_subset (Finset.union_subset (Finset.union_subset hn hw) hb)
    ((rowMask_mono R.len 0 (Finset.subset_univ Sz)).trans hz)

private theorem fullKeep_sum {D : PrefixArithmetic} (R : RowData naturalRows D) (A : ℤ) (c : ℕ)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (Sz : Finset (Fin (R.len 0)))
    (hn : weight Sn = A) (hw : weight Sw = D.H / 4 - A)
    (hz : weight Sz = (c : ℤ)) :
    -(∑ o ∈ fullKeep R Sn Sw Sz, R.f o) =
      A * D.n + (D.H / 4 - A) * D.w - (D.q - 1) * D.b + (c : ℤ) * D.z := by
  have hd1 : Disjoint (rowMask R.len 2 Sn ∪ rowMask R.len 4 Sw) (fullRow R 1) := by
    simp only [fullRow, Finset.disjoint_union_left]
    constructor <;> apply rowMask_disjoint <;> decide
  have hd0 : Disjoint (rowMask R.len 2 Sn ∪ rowMask R.len 4 Sw ∪ fullRow R 1)
      (rowMask R.len 0 Sz) := by
    simp only [fullRow, Finset.disjoint_union_left]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> apply rowMask_disjoint <;> decide
  rw [fullKeep, Finset.sum_union hd0, Finset.sum_union hd1,
    two_rows_sum R 2 4 Sn Sw (by decide), row_sum, fullRow_sum,
    hn, hw, hz, (show R.base 0 = -D.z from R.base0), (show R.base 1 = D.b from R.base1), (show R.base 2 = -D.n from R.base2), (show R.base 4 = -D.w from R.base4), (show (2 : ℤ) ^ R.len 1 = D.q from R.pow1)]
  ring

private theorem fullKeep_complement {D : PrefixArithmetic} (R : RowData naturalRows D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (Sz : Finset (Fin (R.len 0))) :
    bank R Sn Sw \ fullKeep R Sn Sw Sz = rowMask R.len 0 Szᶜ ∪ fullRow R 5 := by
  classical
  ext o
  rcases o with i | ⟨i, j⟩
  · simp [bank, fullKeep, fullRow]
  · by_cases hi0 : i = 0
    · subst i; simp [bank, fullKeep, fullRow]
    · by_cases hi1 : i = 1
      · subst i; simp [bank, fullKeep, fullRow]
      · by_cases hi2 : i = 2
        · subst i; simp [bank, fullKeep, fullRow]
        · by_cases hi4 : i = 4
          · subst i; simp [bank, fullKeep, fullRow]
          · by_cases hi5 : i = 5
            · subst i; simp [bank, fullKeep, fullRow]
            · simp (disch := omega) [bank, fullKeep, fullRow]

private theorem lower_above_two_b (D : PrefixArithmetic) (hF : D.F ≤ D.H / 4) :
    2 * D.b < D.u := by
  obtain ⟨hn, hz, hb, hw, hv, hu, hG, hq, hHw, hwb, hza⟩ := arithmetic_geometry D
  have h4 : 4 * D.F ≤ D.H := by have hH := D.H_four; omega
  have hm := mul_le_mul_of_nonneg_right h4 (le_of_lt hu)
  have hHu : 2 * (D.N + 1) ≤ D.H * D.u := by
    nlinarith only [hm, D.U_threshold]
  by_contra hbad
  have hm' := mul_le_mul_of_nonneg_left (le_of_not_gt hbad)
    (show 0 ≤ D.H by have hH := D.H_eight; omega)
  nlinarith only [hm', hHu, D.N_b, hn]

private theorem full_bank_selection {D : PrefixArithmetic} (R : RowData naturalRows D) (A f : ℤ)
    (hA : 1 ≤ A)
    (heq : 2 * f = D.n + D.w + D.Δ - 2 * A * (D.w - D.n))
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (hSn : weight Sn = A) (hSw : weight Sw = D.H / 4 - A)
    (hZ : 0 < wjHeight R f) (hF : D.F ≤ D.H / 4) :
    ∃ (c : ℕ) (Sz : Finset (Fin (R.len 0))) (K : TSelection R Sn Sw),
      (c : ℤ) ≤ D.q - 1 ∧ weight Sz = (c : ℤ) ∧
      K.keep = fullKeep R Sn Sw Sz ∧ K.pay = ∅ ∧
      (∀ j : ℕ, j < c →
        A * D.n + (D.H / 4 - A) * D.w - (D.q - 1) * D.b + (j : ℤ) * D.z <
          (D.u - D.z) / 2) ∧
      tSmall R K = rowMask R.len 0 Szᶜ ∪ fullRow R 5 := by
  classical
  obtain ⟨hn, hz, hb, hw, hv, hu, hG, hq, hHw, hwb, hza⟩ := arithmetic_geometry D
  obtain ⟨hell0, hW0, hell, hhi, hW, hwidth⟩ := gate_limits D
  let Dold := A * D.n + (D.H / 4 - A) * D.w - (D.q - 1) * D.b
  let ell := (D.u - D.z) / 2
  have hqb : (D.H / 4) * D.w < D.q * D.b := by
    have hw2b : D.w < 2 * D.b := by have hwa := D.w_bounds.2; have hab := D.ab; omega
    have hm := mul_pos (show 0 < D.H / 4 by omega) (sub_pos.mpr hw2b)
    have hqB := congrArg (fun q : ℤ => q * D.b) hq
    nlinarith only [hm, hqB]
  have hR : A * D.n + (D.H / 4 - A) * D.w ≤ (D.H / 4) * D.w := by
    have hm := mul_nonneg (show 0 ≤ A by omega) (show 0 ≤ D.w - D.n by have hwh := D.w_hard; have hd := D.delta_two; omega)
    nlinarith only [hm]
  have hD : Dold < D.b := by dsimp only [Dold]; nlinarith only [hR, hqb]
  have hsum : (∑ o ∈ bank R Sn Sw, R.f o) =
      -Dold - (D.q - 1) * D.z + (D.e - 1) * D.v := by
    have hd0 : Disjoint (rowMask R.len 2 Sn ∪ rowMask R.len 4 Sw) (fullRow R 0) := by
      simp only [fullRow, Finset.disjoint_union_left]
      constructor <;> apply rowMask_disjoint <;> decide
    have hd1 : Disjoint (rowMask R.len 2 Sn ∪ rowMask R.len 4 Sw ∪ fullRow R 0) (fullRow R 1) := by
      simp only [fullRow, Finset.disjoint_union_left]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> apply rowMask_disjoint <;> decide
    have hd5 : Disjoint (rowMask R.len 2 Sn ∪ rowMask R.len 4 Sw ∪ fullRow R 0 ∪ fullRow R 1)
        (fullRow R 5) := by
      simp only [fullRow, Finset.disjoint_union_left]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> apply rowMask_disjoint <;> decide
    change (∑ o ∈ rowMask R.len 2 Sn ∪ rowMask R.len 4 Sw ∪
      fullRow R 0 ∪ fullRow R 1 ∪ fullRow R 5, R.f o) =
      -Dold - (D.q - 1) * D.z + (D.e - 1) * D.v
    rw [Finset.sum_union hd5, Finset.sum_union hd1, Finset.sum_union hd0,
      two_rows_sum R 2 4 Sn Sw (by decide), fullRow_sum, fullRow_sum, fullRow_sum,
      hSn, hSw, (show (2 : ℤ) ^ R.len 0 = D.q from R.pow0), (show (2 : ℤ) ^ R.len 1 = D.q from R.pow1), (show (2 : ℤ) ^ R.len 5 = D.e from R.pow5), (show R.base 0 = -D.z from R.base0), (show R.base 1 = D.b from R.base1), (show R.base 2 = -D.n from R.base2), (show R.base 4 = -D.w from R.base4), (show R.base 5 = D.v from R.base5)]
    dsimp only [Dold]
    ring
  have hledger := bank_charge R A f heq Sn Sw hSn hSw
  have hcost := mul_nonneg (sub_nonneg.mpr D.e_one) (le_of_lt hv)
  have hreach : ell ≤ Dold + (D.q - 1) * D.z := by
    rw [hsum] at hledger
    dsimp only [ell]
    nlinarith only [hledger, hell, hZ, hcost]
  have hqc : (((D.q - 1).toNat : ℕ) : ℤ) = D.q - 1 := Int.toNat_of_nonneg (by omega)
  have hex : ∃ c : ℕ, ell ≤ Dold + (c : ℤ) * D.z := by
    refine ⟨(D.q - 1).toNat, ?_⟩
    simpa only [hqc] using hreach
  let c := Nat.find hex
  have hc : ell ≤ Dold + (c : ℤ) * D.z := Nat.find_spec hex
  have hcq : (c : ℤ) ≤ D.q - 1 := by
    have hh := Nat.find_min' hex (show ell ≤ Dold + ((D.q - 1).toNat : ℤ) * D.z by
      simpa only [hqc] using hreach)
    have hcast : (c : ℤ) ≤ ((D.q - 1).toNat : ℤ) := by
      exact_mod_cast (show c ≤ (D.q - 1).toNat from hh)
    omega
  have hminimal (j : ℕ) (hj : j < c) : Dold + (j : ℤ) * D.z < ell :=
    lt_of_not_ge (Nat.find_min hex hj)
  have hu2b := lower_above_two_b D hF
  have hu2z : 2 * D.z < D.u := by have hzb := D.nzb.2; omega
  have hupper : Dold + (c : ℤ) * D.z ≤ D.u - (D.z + 1) / 2 := by
    by_cases hc0 : c = 0
    · simp only [hc0, Nat.cast_zero, zero_mul, add_zero]
      have hoz := D.odd_z
      have hzb := D.nzb.2
      omega
    · have hprev := hminimal (c - 1) (by omega)
      have hcast : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by omega
      rw [hcast] at hprev
      nlinarith only [hprev, hu2z, hell, hhi]
  obtain ⟨Sz, hSz⟩ := mask_exists (R.len 0) (c : ℤ) (by omega)
    (by rw [(show (2 : ℤ) ^ R.len 0 = D.q from R.pow0)]; omega)
  let K : TSelection R Sn Sw := {
    keep := fullKeep R Sn Sw Sz
    available := fullKeep_available R Sn Sw Sz
    pay := ∅
    gate := by
      rw [fullKeep_sum R A c Sn Sw Sz hSn hSw hSz]
      simp only [weight, Finset.sum_empty, zero_mul, sub_zero]
      exact ⟨hc, hupper⟩ }
  refine ⟨c, Sz, K, hcq, hSz, rfl, rfl, hminimal, ?_⟩
  simp only [tSmall, K, rowMask, Finset.map_empty, Finset.union_empty]
  exact fullKeep_complement R Sn Sw Sz

/- Exact finite complement; no saturated beyond-boundary parent is included. -/
private def fullBank {D : PrefixArithmetic} (R : RowData naturalRows D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (Sz : Finset (Fin (R.len 0))) : Finset (Occ R.len) :=
  fullKeep R Sn Sw Sz ∪ fullRow R 6

private theorem fullBank_partition {D : PrefixArithmetic} (R : RowData naturalRows D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (Sz : Finset (Fin (R.len 0))) (K : TSelection R Sn Sw)
    (hk : K.keep = fullKeep R Sn Sw Sz) (hp : K.pay = ∅) :
    Disjoint (tUsed R K) (fullBank R Sn Sw Sz) ∧
      tUsed R K ∪ fullBank R Sn Sw Sz = (occurrences 7 R.len).toFinset := by
  classical
  have hs : tSmall R K = rowMask R.len 0 Szᶜ ∪ fullRow R 5 := by
    simp only [tSmall, hk, hp, rowMask, Finset.map_empty, Finset.union_empty]
    exact fullKeep_complement R Sn Sw Sz
  constructor
  · apply Finset.disjoint_left.mpr
    intro o ho hb
    rcases o with i | ⟨i, j⟩
    · simpa [fullBank, fullKeep, fullRow] using hb
    · by_cases hi : i < 7
      · interval_cases i <;>
          simp [tUsed, hs, wjUsed, firstParents, initialSmall, fullBank, fullKeep, fullRow] at ho hb <;> tauto
      · simp (disch := omega) [fullBank, fullKeep, fullRow] at hb
  · ext o
    rcases o with i | ⟨i, j⟩
    · by_cases hi : i < 7
      · interval_cases i <;>
          simp [tUsed, hs, wjUsed, firstParents, initialSmall, fullBank, fullKeep, fullRow, mem_occurrences]
      · simp (disch := omega) [tUsed, hs, wjUsed, firstParents, initialSmall, fullBank,
          fullKeep, fullRow, mem_occurrences, hi] <;> omega
    · by_cases hi : i < 7
      · interval_cases i <;>
          simp [tUsed, hs, wjUsed, firstParents, initialSmall, fullBank, fullKeep, fullRow,
            mem_occurrences] <;> tauto
      · simp (disch := omega) [tUsed, hs, wjUsed, firstParents, initialSmall, fullBank,
          fullKeep, fullRow, mem_occurrences, hi]

private theorem fullBank_charge {D : PrefixArithmetic} (R : RowData naturalRows D)
    (Sn : Finset (Fin (R.len 2))) (Sw : Finset (Fin (R.len 4)))
    (Sz : Finset (Fin (R.len 0))) (K : TSelection R Sn Sw)
    (hk : K.keep = fullKeep R Sn Sw Sz) (hp : K.pay = ∅) :
    2 * (tHeight R K + ∑ o ∈ fullBank R Sn Sw Sz, R.f o) = D.z + D.y := by
  have hd := (bank_row6_disjoint R Sn Sw (Finset.univ : Finset (Fin (R.len 6)))).mono_left
    (fullKeep_available R Sn Sw Sz)
  change Disjoint (fullKeep R Sn Sw Sz) (fullRow R 6) at hd
  have hs : (∑ o ∈ fullBank R Sn Sw Sz, R.f o) =
      (∑ o ∈ K.keep, R.f o) - ((2 : ℤ) ^ R.len 6 - 1) * D.u := by
    rw [fullBank, Finset.sum_union hd, fullRow_sum, (show R.base 6 = -D.u from R.base6), ← hk]
    ring
  obtain ⟨he0, hw0, he, hhi, hw, hwidth⟩ := gate_limits D
  have hpu := congrArg (fun n : ℤ => n * D.u) (show 2 * (2 : ℤ) ^ R.len 6 = D.F from R.pow6)
  rw [hs]
  dsimp only [tHeight]
  rw [hp]
  simp only [weight, Finset.sum_empty, zero_mul, sub_zero]
  nlinarith only [he, hpu, R.large6, D.y_source]

/- G8: reuse the existing natural binary-mask injectivity theorem. The new
content is the source-forced range and literal retained support decomposition. -/
private theorem weight_injective {u : ℕ} : Function.Injective (weight (u := u)) := by
  intro S T h
  apply ZeroSumSubsets.mask_injective u
  change (∑ j ∈ S, (2 : ℕ) ^ j.val) = ∑ j ∈ T, (2 : ℕ) ^ j.val
  rw [weight_nat, weight_nat] at h
  exact_mod_cast h

def liftMask {r l : ℕ} (hr : r ≤ l) (S : Finset (Fin r)) : Finset (Fin l) :=
  S.map ⟨fun j => ⟨j.val, lt_of_lt_of_le j.isLt hr⟩,
    by intro i j he; exact Fin.ext (congrArg (Fin.val (n := l)) he)⟩

private theorem weight_liftMask {r l : ℕ} (hr : r ≤ l) (S : Finset (Fin r)) :
    weight (liftMask hr S) = weight S := by
  rw [weight, liftMask, Finset.sum_map]
  rfl

private theorem mem_lift_full {r l : ℕ} (hr : r ≤ l) (j : Fin l) :
    j ∈ liftMask hr (Finset.univ : Finset (Fin r)) ↔ j.val < r := by
  constructor
  · intro hj
    obtain ⟨i, hi, he⟩ := Finset.mem_map.mp hj
    have hv : i.val = j.val := congrArg (Fin.val (n := l)) he
    omega
  · intro hj
    exact Finset.mem_map.mpr ⟨⟨j.val, hj⟩, Finset.mem_univ _, Fin.ext rfl⟩

private theorem depleted_w_decomposition {l r : ℕ} (hr : r < l) (A : ℤ)
    (hA : 1 ≤ A) (hAt : A ≤ (2 : ℤ) ^ r)
    (Sw : Finset (Fin l)) (hSw : weight Sw = (2 : ℤ) ^ l - A) :
    ∃ Slow : Finset (Fin l),
      weight Slow = (2 : ℤ) ^ r - A ∧
      (∀ j ∈ Slow, j.val < r) ∧
      Disjoint Slow {⟨r, hr⟩} ∧
      Sw = (liftMask (Nat.succ_le_of_lt hr) (Finset.univ : Finset (Fin (r + 1))))ᶜ ∪
        {⟨r, hr⟩} ∪ Slow ∧
      Slow ⊆ Sw ∧ (⟨r, hr⟩ : Fin l) ∈ Sw ∧
      (2 ≤ A → Sw ≠ Finset.univ) := by
  classical
  obtain ⟨S, hS⟩ := mask_exists r ((2 : ℤ) ^ r - A) (by omega) (by omega)
  let Slow := liftMask (Nat.le_of_lt hr) S
  let High := (liftMask (Nat.succ_le_of_lt hr) (Finset.univ : Finset (Fin (r + 1))))ᶜ
  let top : Fin l := ⟨r, hr⟩
  have hlow : ∀ j ∈ Slow, j.val < r := by
    intro j hj
    obtain ⟨i, hi, he⟩ := Finset.mem_map.mp hj
    have hv : i.val = j.val := congrArg (Fin.val (n := l)) he
    omega
  have hHigh : ∀ j ∈ High, r + 1 ≤ j.val := by
    intro j hj
    have hh := Finset.mem_compl.mp hj
    rw [mem_lift_full] at hh
    omega
  have hdht : Disjoint High {top} := by
    apply Finset.disjoint_left.mpr
    intro j hj ht
    have he := Finset.mem_singleton.mp ht
    subst j
    have hh := hHigh top hj
    change r + 1 ≤ r at hh
    omega
  have hdtl : Disjoint ({top} : Finset (Fin l)) Slow := by
    apply Finset.disjoint_left.mpr
    intro j ht hj
    have he := Finset.mem_singleton.mp ht
    subst j
    have hh := hlow top hj
    change r < r at hh
    omega
  have hdhl : Disjoint High Slow := by
    apply Finset.disjoint_left.mpr
    intro j hj hl
    have h1 := hHigh j hj
    have h2 := hlow j hl
    omega
  have hwl : weight Slow = (2 : ℤ) ^ r - A := by
    rw [weight_liftMask]
    exact hS
  have hwh : weight High = (2 : ℤ) ^ l - 2 * (2 : ℤ) ^ r := by
    rw [weight_compl, weight_liftMask, weight_full, pow_succ]
    ring
  have he : Sw = High ∪ {top} ∪ Slow := by
    apply weight_injective
    rw [hSw]
    change (2 : ℤ) ^ l - A = ∑ j ∈ High ∪ {top} ∪ Slow, (2 : ℤ) ^ j.val
    rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdhl, hdtl⟩),
      Finset.sum_union hdht]
    simp only [Finset.sum_singleton]
    change (2 : ℤ) ^ l - A = weight High + (2 : ℤ) ^ r + weight Slow
    rw [hwh, hwl]
    ring
  refine ⟨Slow, hwl, hlow, hdtl.symm, he, ?_, ?_, ?_⟩
  · rw [he]
    exact Finset.subset_union_right
  · rw [he]
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  · intro h2 hfull
    have hh := congrArg weight hfull
    rw [hSw, weight_full] at hh
    omega

private theorem source_A_le_tau {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x)
    (he : (sourcePrefixArithmetic h).e = 1) (hF : 4 ≤ (sourcePrefixArithmetic h).F)
    (hy : (sourcePrefixArithmetic h).y ≤ 2 * b - 3)
    (A : ℤ)
    (hprev : 2 * ((sourcePrefixArithmetic h).w - (sourcePrefixArithmetic h).n) * (A - 1) <
      (sourcePrefixArithmetic h).n + (sourcePrefixArithmetic h).Δ + 1) :
    A ≤ (2 : ℤ) ^ sourceLength t x 6 := by
  let D := sourcePrefixArithmetic h
  change D.e = 1 at he
  change 4 ≤ D.F at hF
  change D.y ≤ 2 * D.b - 3 at hy
  change 2 * (D.w - D.n) * (A - 1) < D.n + D.Δ + 1 at hprev
  obtain ⟨hn, hz, hb, hw, hv, hu, hG, hq, hHw, hwb, hza⟩ := arithmetic_geometry D
  let eta := D.F * D.w - (D.F + 1) * D.b
  have huEq : D.u = D.H * D.w - D.N := by
    have hh := congrArg (fun q : ℤ => q * D.w) D.H_q
    have hus := D.u_source
    rw [he] at hus
    nlinarith only [hus, D.v_source, hh]
  have heta : D.H * eta = (D.F + 1) * D.n - D.y := by
    have hys := D.y_source
    rw [huEq] at hys
    have hNb := congrArg (fun s : ℤ => (D.F + 1) * s) D.N_b
    dsimp only [eta]
    nlinarith only [hys, hNb]
  have hn2b : D.b < 2 * D.n := by have ha := D.n_minimum; have hab := D.ab.2; omega
  have heta0 : 0 < eta := by
    have hm := mul_nonneg (show 0 ≤ D.F - 4 by omega) (le_of_lt hn)
    by_contra hh
    have hm' := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ D.H by have hH := D.H_eight; omega)
      (show eta ≤ 0 by omega)
    change D.y ≤ 2 * D.b - 3 at hy
    nlinarith only [heta, hm, hm', hy, hn2b, hn]
  have hFK : D.n + D.Δ + 1 < D.F * (D.w - D.n) := by
    have hH := D.H_eight
    have hDel := D.delta_two
    have hpositive := mul_nonneg (show 0 ≤ D.F - 1 by omega)
      (show 0 ≤ D.H * D.Δ by positivity)
    have hid : D.F * (D.w - D.n) = D.b + eta + D.F * D.H * D.Δ := by
      dsimp only [eta]
      rw [D.b_n]
      ring
    have hHD := mul_nonneg (show 0 ≤ D.H - 1 by omega) (show 0 ≤ D.Δ by omega)
    nlinarith only [hid, D.b_n, heta0, hpositive, hHD, hDel]
  have hpow : D.F = 2 * (2 : ℤ) ^ sourceLength t x 6 := by
    change (2 : ℤ) ^ (sourceLength t x 6 + 1) = _
    rw [pow_succ]
    ring
  have hK : 0 < D.w - D.n := by have hh := D.w_hard; have hd := D.delta_two; omega
  by_contra hbad
  have hm := mul_nonneg (le_of_lt hK)
    (show 0 ≤ A - 1 - (2 : ℤ) ^ sourceLength t x 6 by omega)
  have hFKpow := congrArg (fun q : ℤ => q * (D.w - D.n)) hpow
  nlinarith only [hm, hprev, hFK, hFKpow]

/-- Literal physical positions in a computed source row. -/
def sourceMask {k : ℕ} (t : ℕ) (x : Fin k) (i : ℕ)
    (S : Finset (Fin (sourceLength t x i))) : Finset (Fin k) :=
  S.image (fun j => advance (sourceParent t x i) (j.val + 1))

/-- Chronological labels starting with row seven, including its parent U,
up to the actual boundary at 2m. The boundary x is excluded. -/
def futureLabels {k : ℕ} (m t : ℕ) (x : Fin k) : Finset (Fin k) :=
  (((List.range (2 * m)).filter (fun i => 7 ≤ i)).flatMap (fun i =>
    sourceParent t x i :: rowLabels (sourceParent t x i) (sourceLength t x i))).toFinset

private theorem physical_mask_image {k t : ℕ} (x : Fin k) (i : ℕ)
    (S : Finset (Fin (sourceLength t x i))) :
    (rowMask (fun j => sourceLength t x j) i S).image (physical x) = sourceMask t x i S := by
  classical
  ext z
  simp [rowMask, sourceMask, physical]

private theorem map_nodup_on {α β : Type*} (f : α → β) (l : List α)
    (hn : l.Nodup)
    (hi : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hh := List.nodup_cons.mp hn
    rw [List.map_cons, List.nodup_cons]
    constructor
    · intro hm
      obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
      have heq := hi b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self) he
      subst b
      exact hh.1 hb
    · apply ih hh.2
      intro b hb c hc he
      exact hi b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc) he

private theorem word_finset_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : α → ℤ} {C h : ℤ} {first : α} {U : Finset α}
    (pre : Prefix s C first U h) (phi : α → β) :
    (pre.word.map phi).toFinset = U.image phi := by
  ext j
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨o, ho, he⟩
    exact ⟨o, Finset.mem_toList.mp (pre.perm.mem_iff.mp ho), he⟩
  · rintro ⟨o, ho, he⟩
    exact ⟨o, pre.perm.mem_iff.mpr (Finset.mem_toList.mpr ho), he⟩

private theorem physical_future_image {m k t : ℕ} (x : Fin k) :
    (((occurrences (2 * m) (fun i => sourceLength t x i)).toFinset) \
      (occurrences 7 (fun i => sourceLength t x i)).toFinset).image (physical x) =
      futureLabels m t x := by
  classical
  ext z
  simp only [Finset.mem_image, Finset.mem_sdiff, List.mem_toFinset,
    futureLabels, List.mem_flatMap, List.mem_filter, List.mem_range,
    List.mem_cons, rowLabels, List.mem_ofFn, decide_eq_true_eq]
  constructor
  · rintro ⟨o, ⟨ho, hn⟩, he⟩
    rcases o with i | ⟨i, j⟩
    · rw [mem_occurrences] at ho hn
      exact ⟨i, ⟨ho, by omega⟩, Or.inl he.symm⟩
    · rw [mem_occurrences] at ho hn
      change i < 2 * m at ho
      change ¬i < 7 at hn
      exact ⟨i, ⟨ho, by omega⟩, Or.inr ⟨j, he⟩⟩
  · rintro ⟨i, ⟨hi, hi7⟩, he | ⟨j, he⟩⟩
    · exact ⟨Sum.inl i, ⟨mem_occurrences.mpr hi, by rw [mem_occurrences]; omega⟩, he.symm⟩
    · exact ⟨Sum.inr ⟨i, j⟩, ⟨mem_occurrences.mpr hi, by rw [mem_occurrences]; change ¬i < 7; omega⟩, he⟩

set_option maxHeartbeats 2000000 in
/-- A source-attained canonical LOWER prefix retains the entire positive b row.
In the e=1 residual it also exposes the exact low-w mask and tau occurrence.
All source quantities, including row-eight a0, are the computed actual ones. -/
theorem canonical_lower_full_bank {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x)
    (hLower : (2 : ℤ) ^ (sourceLength t x 6 + 1) ≤ (2 : ℤ) ^ (L + 1) / 4) :
    let D := sourceCoordinates h
    let s := actualSource k t
    ∃ (A f : ℤ) (c : ℕ)
      (Sn : Finset (Fin (sourceLength t x 2)))
      (Sw : Finset (Fin (sourceLength t x 4)))
      (Sz : Finset (Fin (sourceLength t x 0))) (word : List (Fin k)),
      1 ≤ A ∧ A ≤ D.H / 4 ∧ 0 ≤ f ∧ f ≤ (D.w - 1) / 2 ∧
      2 * f = D.n + D.w + D.Δ - 2 * A * (D.w - D.n) ∧
      2 * (D.w - D.n) * (A - 1) < D.n + D.Δ + 1 ∧
      D.n + D.Δ + 1 ≤ 2 * (D.w - D.n) * A ∧
      (∑ j ∈ Sn, (2 : ℤ) ^ j.val) = A ∧ (∑ j ∈ Sw, (2 : ℤ) ^ j.val) = D.H / 4 - A ∧ (∑ j ∈ Sz, (2 : ℤ) ^ j.val) = (c : ℤ) ∧
      (c : ℤ) ≤ D.q - 1 ∧
      (∀ j : ℕ, j < c → A * D.n + (D.H / 4 - A) * D.w - (D.q - 1) * D.b +
        (j : ℤ) * D.z < (D.u - D.z) / 2) ∧
      (let Kfull := sourceMask t x 2 Sn ∪ sourceMask t x 4 Sw ∪
        sourceMask t x 1 Finset.univ ∪ sourceMask t x 0 Sz ∪ sourceMask t x 6 Finset.univ
       let Dold := A * D.n + (D.H / 4 - A) * D.w - (D.q - 1) * D.b
       (D.u - D.z) / 2 ≤ Dold + (c : ℤ) * D.z ∧
       Dold + (c : ℤ) * D.z ≤ D.u - (D.z + 1) / 2 ∧
       word.Nodup ∧ word.head? = some x ∧
       (∀ j : ℕ, 0 ≤ ((word.take j).map (s)).sum ∧
         ((word.take j).map (s)).sum ≤ halfCapacity k) ∧
       Disjoint word.toFinset Kfull ∧
       word.toFinsetᶜ = Kfull ∪ futureLabels m t x ∧
       Disjoint Kfull (futureLabels m t x) ∧
       2 * ((word.map (s)).sum + ∑ i ∈ Kfull, s i) = D.z + D.y ∧
       (D.e = 1 → 4 ≤ D.F → D.y ≤ 2 * b - 3 →
         ∃ (hr : sourceLength t x 6 < sourceLength t x 4)
           (Slow : Finset (Fin (sourceLength t x 4))),
           (∑ j ∈ Slow, (2 : ℤ) ^ j.val) = (2 : ℤ) ^ sourceLength t x 6 - A ∧
           (∀ j ∈ Slow, j.val < sourceLength t x 6) ∧
           Disjoint Slow {⟨sourceLength t x 6, hr⟩} ∧
           Sw = (liftMask (Nat.succ_le_of_lt hr) Finset.univ)ᶜ ∪
             {⟨sourceLength t x 6, hr⟩} ∪ Slow ∧
           sourceMask t x 4 Slow ⊆ Kfull ∧
           advance (sourceParent t x 4) (sourceLength t x 6 + 1) ∈ Kfull ∧
           (2 ≤ A → Sw ≠ Finset.univ))) := by
  classical
  let D := sourcePrefixArithmetic h
  let R := sourceData h
  have hm := h.pairs
  obtain ⟨A, f, hA, hAG, hf, hfg, heq, hprev, hnext⟩ := canonical_mask_height D
  obtain ⟨hn, hz, hb, hw, hv, hu, hG, hq, hHw, hwb, hza⟩ := arithmetic_geometry D
  have hpow2 : (2 : ℤ) ^ R.len 2 = D.q := (show (2 : ℤ) ^ R.len 2 = D.q from R.pow2)
  have hpow4 : (2 : ℤ) ^ R.len 4 = D.H / 4 := (show (2 : ℤ) ^ R.len 4 = D.H / 4 from R.pow4)
  obtain ⟨Sn, hSn⟩ := mask_exists (R.len 2) A (by omega) (by rw [hpow2]; omega)
  obtain ⟨Sw, hSw⟩ := mask_exists (R.len 4) (D.H / 4 - A) (by omega)
    (by rw [hpow4]; omega)
  obtain ⟨⟨preJ⟩, hZ, hZv⟩ := wj_prefix R A f hA hAG hf hfg heq Sn Sw hSn hSw
  obtain ⟨c, Sz, K, hcq, hSz, hk, hp, hmin, hsmall⟩ :=
    full_bank_selection R A f hA heq Sn Sw hSn hSw hZ hLower
  obtain ⟨preT⟩ := t_extension R A f heq Sn Sw hSn hSw preJ K
  obtain ⟨hd, hpart⟩ := fullBank_partition R Sn Sw Sz K hk hp
  let phi : Occ R.len → Fin k := physical (t := t) x
  let U := tUsed R K
  let B := fullBank R Sn Sw Sz
  let All := (occurrences (2 * m) R.len).toFinset
  let Future := All \ (occurrences 7 R.len).toFinset
  have hinj := physical_injective_on h
  have hvalid (o : Occ R.len) (ho : o ∈ U ∪ B) : o ∈ All := by
    change o ∈ tUsed R K ∪ fullBank R Sn Sw Sz at ho
    rw [hpart] at ho
    have hh := mem_occurrences.mp (List.mem_toFinset.mp ho)
    apply List.mem_toFinset.mpr
    apply mem_occurrences.mpr
    rcases o with i | ⟨i, j⟩ <;> change i < 7 at hh <;> change i < 2 * m <;> omega
  have huvalid (o : Occ R.len) (ho : o ∈ preT.word) :
      o ∈ occurrences (2 * m) R.len := by
    apply List.mem_toFinset.mp
    exact hvalid o (Finset.mem_union_left _ (Finset.mem_toList.mp (preT.perm.mem_iff.mp ho)))
  have hnd : (preT.word.map phi).Nodup := by
    apply map_nodup_on phi preT.word (preT.perm.nodup_iff.mpr U.nodup_toList)
    intro o ho o' ho' he
    exact hinj (huvalid o ho) (huvalid o' ho') he
  let word := preT.word.map phi
  have hwused : word.toFinset = U.image phi := word_finset_image preT phi
  let Kfull := sourceMask t x 2 Sn ∪ sourceMask t x 4 Sw ∪ sourceMask t x 1 Finset.univ ∪
    sourceMask t x 0 Sz ∪ sourceMask t x 6 Finset.univ
  have hrowimage (i : ℕ) (S : Finset (Fin (R.len i))) :
      (rowMask R.len i S).image phi = sourceMask t x i S := physical_mask_image x i S
  have hbimage : B.image phi = Kfull := by
    simp only [B, fullBank, fullKeep, Finset.image_union, fullRow, hrowimage, Kfull]
    rfl
  have htimage : Future.image phi = futureLabels m t x := physical_future_image x
  have hbd : Disjoint word.toFinset Kfull := by
    rw [hwused, ← hbimage]
    apply Finset.disjoint_left.mpr
    intro z hz1 hz2
    obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hz1
    obtain ⟨o', ho', he⟩ := Finset.mem_image.mp hz2
    have heq := hinj (List.mem_toFinset.mp (hvalid o' (Finset.mem_union_right _ ho')))
      (List.mem_toFinset.mp (hvalid o (Finset.mem_union_left _ ho))) he
    subst o'
    exact Finset.disjoint_left.mp hd ho ho'
  have hfuture (o : Occ R.len) : o ∈ Future ↔ o ∈ All ∧ o ∉ U ∪ B := by
    simp only [Future, Finset.mem_sdiff, ← hpart]
    rfl
  have hsurj (z : Fin k) : ∃ o ∈ All, phi o = z := by
    obtain ⟨o, ho, he⟩ := List.mem_map.mp ((physical_inventory h).mem_iff.mpr (List.mem_finRange z))
    exact ⟨o, List.mem_toFinset.mpr ho, he⟩
  have hcomp : word.toFinsetᶜ = Kfull ∪ futureLabels m t x := by
    rw [hwused, ← hbimage, ← htimage]
    ext z
    obtain ⟨o, ho, rfl⟩ := hsurj z
    have himg (S : Finset (Occ R.len)) (hS : S ⊆ All) : phi o ∈ S.image phi ↔ o ∈ S := by
      constructor
      · intro hz
        obtain ⟨o', ho', he⟩ := Finset.mem_image.mp hz
        have heq := hinj (List.mem_toFinset.mp (hS ho')) (List.mem_toFinset.mp ho) he
        simpa only [heq] using ho'
      · intro hs
        exact Finset.mem_image.mpr ⟨o, hs, rfl⟩
    rw [Finset.mem_compl, Finset.mem_union,
      himg U (fun o ho => hvalid o (Finset.mem_union_left _ ho)),
      himg B (fun o ho => hvalid o (Finset.mem_union_right _ ho)),
      himg Future Finset.sdiff_subset, hfuture]
    have hdis : o ∈ U → o ∈ B → False := fun hu hb => Finset.disjoint_left.mp hd hu hb
    simp only [Finset.mem_union]
    tauto
  have hbfuture : Disjoint Kfull (futureLabels m t x) := by
    rw [← hbimage, ← htimage]
    apply Finset.disjoint_left.mpr
    intro z hz1 hz2
    obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hz1
    obtain ⟨o', ho', he⟩ := Finset.mem_image.mp hz2
    have hs := (hfuture o').mp ho'
    have heq := hinj (List.mem_toFinset.mp hs.1)
      (List.mem_toFinset.mp (hvalid o (Finset.mem_union_right _ ho))) he
    subst o'
    exact hs.2 (Finset.mem_union_right _ ho)
  have hsum : (∑ z ∈ Kfull, actualSource k t z) = ∑ o ∈ B, R.f o := by
    rw [← hbimage, Finset.sum_image]
    · rfl
    · intro o ho o' ho' he
      exact hinj (List.mem_toFinset.mp (hvalid o (Finset.mem_union_right _ ho)))
        (List.mem_toFinset.mp (hvalid o' (Finset.mem_union_right _ ho'))) he
  have hwordSum : (word.map (actualSource k t)).sum = tHeight R K := by
    change ((preT.word.map phi).map (actualSource k t)).sum = tHeight R K
    rw [List.map_map]
    exact preT.height
  have hgate := K.gate
  rw [hp, hk, fullKeep_sum R A c Sn Sw Sz hSn hSw hSz] at hgate
  simp only [weight, Finset.sum_empty, zero_mul, sub_zero] at hgate
  refine ⟨A, f, c, Sn, Sw, Sz, word, hA, hAG, hf, hfg, heq, hprev, hnext,
    hSn, hSw, hSz, hcq, hmin, hgate.1, hgate.2, hnd, ?_, ?_, hbd,
    hcomp, hbfuture, ?_, ?_⟩
  · change (preT.word.map phi).head? = some x
    rw [List.head?_map, preT.head]
    change some (sourceParent t x 0) = some x
    rw [source_parent_zero h]
  · have hl : InStrip (actualSource k t) (halfCapacity k) 0 word :=
      (inStrip_map phi (actualSource k t) (halfCapacity k) 0 preT.word).mpr preT.legal
    intro j
    simpa only [zero_add] using inStrip_prefix hl j
  · rw [hsum, hwordSum]
    exact fullBank_charge R Sn Sw Sz K hk hp
  · intro he hF hy
    have hAt := source_A_le_tau h he hF hy A hprev
    have hr : sourceLength t x 6 < sourceLength t x 4 := by
      have hpow : (2 : ℤ) ^ (sourceLength t x 6 + 1) ≤ (2 : ℤ) ^ sourceLength t x 4 := by
        change D.F ≤ (2 : ℤ) ^ R.len 4
        rw [(show (2 : ℤ) ^ R.len 4 = D.H / 4 from R.pow4)]
        exact hLower
      by_contra hh
      have hm' := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
        (show sourceLength t x 4 ≤ sourceLength t x 6 by omega)
      have hp' : (0 : ℤ) < 2 ^ sourceLength t x 6 := by positivity
      rw [pow_succ] at hpow
      nlinarith only [hpow, hm', hp']
    have hSw' : weight Sw = (2 : ℤ) ^ sourceLength t x 4 - A := by
      change weight Sw = (2 : ℤ) ^ R.len 4 - A
      rw [(show (2 : ℤ) ^ R.len 4 = D.H / 4 from R.pow4)]
      exact hSw
    obtain ⟨Slow, hwl, hlow, hdis, heqW, hsub, htop, hdeplete⟩ :=
      depleted_w_decomposition hr A hA hAt Sw hSw'
    refine ⟨hr, Slow, hwl, hlow, hdis, heqW, ?_, ?_, hdeplete⟩
    · intro z hz
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      have hjw : advance (sourceParent t x 4) (j.val + 1) ∈ sourceMask t x 4 Sw :=
        Finset.mem_image.mpr ⟨j, hsub hj, rfl⟩
      simp only [Kfull, Finset.mem_union]
      tauto
    · have hjw : advance (sourceParent t x 4) (sourceLength t x 6 + 1) ∈ sourceMask t x 4 Sw :=
        Finset.mem_image.mpr ⟨⟨sourceLength t x 6, hr⟩, htop, rfl⟩
      simp only [Kfull, Finset.mem_union]
      tauto

end D5.S3.Combinatorics.Circle.OriginalLowerFullBank
