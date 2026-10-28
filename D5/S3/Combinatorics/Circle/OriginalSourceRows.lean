/- GID: D5/S3/Combinatorics/Circle/OriginalSourceRows
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/OriginalSourceRows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Original physical source rows and their arithmetic inventory bridge. -/
module
public import D5.S3.Combinatorics.Circle.M5SourceRows
public import D5.S3.Combinatorics.Circle.SourcePrefixInventory
import all D5.S3.Combinatorics.Circle.M5SourceRows

/-! # Original physical source rows

The actual LARGE offsets partition the complete physical cycle. Their signed
recurrences supply the arithmetic and row inventory used by the LOWER prefix.
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

end D5.S3.Combinatorics.Circle.OriginalLowerFullBank
