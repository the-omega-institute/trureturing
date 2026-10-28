/- GID: D5/S3/Combinatorics/Circle/M5SourceRows
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/M5SourceRows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Original centered M5 predicates, row telescope and physical partition. -/
module
import all D5.S3.Combinatorics.Circle.ThreeRowScheduler
public import D5.S3.Combinatorics.Circle.ZeroSumSubsets
public import D5.S3.Combinatorics.Circle.ThreeParentFamily
public import Mathlib.Data.Finset.Sort
/-! # M5SourceRows -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.M5FullWordConsumer

open SourceWidth
open Fin.NatCast
open scoped BigOperators


/-- The original half-modulus capacity. -/
def halfCapacity (k : ℕ) : ℤ := ((2 : ℤ) ^ k - 2) / 2

/-- The inclusive LARGE threshold of the original source. -/
def quarter (k : ℕ) : ℤ := (2 : ℤ) ^ (k - 2)

/-- Physical iteration, without quotienting a possibly shorter value orbit. -/
def advance {k : ℕ} (x : Fin k) (j : ℕ) : Fin k := (finRotate k)^[j] x

/-- The literal SMALL interior after a physical parent. -/
def rowLabels {k : ℕ} (x : Fin k) (len : ℕ) : List (Fin k) :=
  List.ofFn (fun j : Fin len => advance x (j.val + 1))

/-- An own row is specified directly by original-source thresholds. Its seed
is the successor of its parent, including when its SMALL interior is empty. -/
structure OwnRow (k t : ℕ) (x : Fin k) (len : ℕ) : Prop where
  proper : len < k
  parent_large : quarter k ≤ |actualSource k t x|
  small : ∀ j < len, |actualSource k t (advance x (j + 1))| < quarter k
  terminal_large : quarter k ≤ |actualSource k t (advance x (len + 1))|

private theorem modulus_quarter (k : ℕ) (hk : 2 ≤ k) :
    modulus k = 4 * quarter k - 1 ∧ halfCapacity k = 2 * quarter k - 1 ∧
      modulus k / 2 = halfCapacity k ∧ 0 < quarter k := by
  have he : k = (k - 2) + 2 := by omega
  have hp : (2 : ℤ) ^ k = 4 * (2 : ℤ) ^ (k - 2) := by
    conv_lhs => rw [he, pow_add]
    ring
  have hq := pow_pos (by norm_num : (0 : ℤ) < 2) (k - 2)
  dsimp [modulus, quarter, halfCapacity]
  rw [hp]
  omega

private theorem source_step (k t : ℕ) (hk : 0 < k) (i : Fin k) :
    actualSource k t (finRotate k i) = doubleStep (modulus k) (actualSource k t i) := by
  have h := (ZeroSumSubsets.source_cycle hk t).2.2 i
  unfold doubleStep
  split_ifs at * <;> omega

private theorem source_small_step (k t : ℕ) (hk : 2 ≤ k) (i : Fin k)
    (hi : |actualSource k t i| < quarter k) :
    actualSource k t (finRotate k i) = 2 * actualSource k t i := by
  rw [source_step k t (by omega) i]
  have hN := (modulus_quarter k hk).1
  have hb := abs_lt.mp hi
  dsimp [doubleStep]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

private theorem advance_succ {k : ℕ} (x : Fin k) (j : ℕ) :
    advance x (j + 1) = finRotate k (advance x j) := by
  exact Function.iterate_succ_apply' _ _ _

private theorem advance_eq {k : ℕ} [NeZero k] (x : Fin k) (j : ℕ) :
    advance x j = x + (j : Fin k) := by
  induction j with
  | zero => simp [advance]
  | succ j ih =>
    rw [advance_succ, ih, finRotate_apply]
    simp [Nat.cast_add, add_assoc]

private theorem advance_cycle {k : ℕ} (x : Fin k) : advance x k = x := by
  have := x.neZero
  simp [advance_eq]

private theorem physical_cycle_perm {k : ℕ} (x : Fin k) :
    (List.ofFn (fun j : Fin k => advance x j.val)).Perm (List.finRange k) := by
  have := x.neZero
  have he : (fun j : Fin k => advance x j.val) = (finCycle x : Fin k → Fin k) := by
    funext j
    simp [advance_eq, finCycle_apply, add_comm]
  rw [he, List.ofFn_eq_map]
  exact (finCycle x).map_finRange_perm

private theorem row_value {k t : ℕ} (hk : 2 ≤ k) {x : Fin k} {len : ℕ}
    (hr : OwnRow k t x len) (j : ℕ) (hj : j ≤ len) :
    actualSource k t (advance x (j + 1)) =
      (2 : ℤ) ^ j * actualSource k t (advance x 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [advance_succ x (j + 1), source_small_step k t hk _ (hr.small j (by omega)),
      ih (by omega), pow_succ]
    ring

private theorem source_bounds (k t : ℕ) (hk : 2 ≤ k) (i : Fin k) :
    -halfCapacity k ≤ actualSource k t i ∧ actualSource k t i ≤ halfCapacity k := by
  obtain ⟨hN, hC, hhalf, hQ⟩ := modulus_quarter k hk
  have hNpos : 0 < modulus k := by omega
  have hodd : modulus k % 2 = 1 := by omega
  simpa only [actualSource, hhalf] using
    centered_bounds hNpos hodd ((2 : ℤ) ^ i.val * (t : ℤ))

private theorem source_positive_step (k t : ℕ) (hk : 2 ≤ k) (i : Fin k)
    (hi : quarter k ≤ actualSource k t i) :
    actualSource k t (advance i 1) = 2 * actualSource k t i - modulus k ∧
      actualSource k t (advance i 1) < 0 := by
  have hN := (modulus_quarter k hk).1
  have hC := (modulus_quarter k hk).2.1
  have hb := source_bounds k t hk i
  have hs := source_step k t (by omega) i
  have hrotate : advance i 1 = finRotate k i := rfl
  rw [hrotate, hs, doubleStep, ite_eq_left (by omega)]
  constructor <;> omega

private theorem source_negative_step (k t : ℕ) (hk : 2 ≤ k) (i : Fin k)
    (hi : actualSource k t i ≤ -quarter k) :
    actualSource k t (advance i 1) = 2 * actualSource k t i + modulus k ∧
      0 < actualSource k t (advance i 1) := by
  have hN := (modulus_quarter k hk).1
  have hC := (modulus_quarter k hk).2.1
  have hQ := (modulus_quarter k hk).2.2.2
  have hb := source_bounds k t hk i
  have hs := source_step k t (by omega) i
  have hrotate : advance i 1 = finRotate k i := rfl
  rw [hrotate, hs, doubleStep, ite_eq_right (by omega), ite_eq_left (by omega)]
  constructor <;> omega

private theorem row_terminal {k t : ℕ} (hk : 2 ≤ k) {x : Fin k} {len : ℕ}
    (hr : OwnRow k t x len) :
    actualSource k t (advance x (len + 1)) =
      (2 : ℤ) ^ len * actualSource k t (advance x 1) :=
  row_value hk hr len (le_refl _)

private theorem negative_minimum_parent (k t : ℕ) (hk : 2 ≤ k) (a : ℤ)
    (ha : 0 < a) (hmin : ∀ i, actualSource k t i < 0 → a ≤ -actualSource k t i)
    (hatt : ∃ i, actualSource k t i = -a) :
    ∃ p : Fin k, quarter k ≤ actualSource k t p ∧
      2 * actualSource k t p = modulus k - a := by
  obtain ⟨i, hi⟩ := hatt
  let p := (finRotate k).symm i
  have hb := source_bounds k t hk p
  have hC := (modulus_quarter k hk).2.1
  have hN := (modulus_quarter k hk).1
  have hs := source_step k t (by omega) p
  have hp : finRotate k p = i := (finRotate k).apply_symm_apply i
  rw [hp, hi, doubleStep] at hs
  by_cases hpos : modulus k < 4 * actualSource k t p
  · rw [ite_eq_left hpos] at hs
    exact ⟨p, by omega, by omega⟩
  · rw [ite_eq_right hpos] at hs
    by_cases hneg : 4 * actualSource k t p < -modulus k
    · rw [ite_eq_left hneg] at hs
      omega
    · rw [ite_eq_right hneg] at hs
      have hm := hmin p (by omega)
      omega

private theorem positive_minimum_parent (k t : ℕ) (hk : 2 ≤ k) (b : ℤ)
    (hb : 0 < b) (hmin : ∀ i, 0 < actualSource k t i → b ≤ actualSource k t i)
    (hatt : ∃ i, actualSource k t i = b) :
    ∃ d : Fin k, actualSource k t d ≤ -quarter k ∧
      -2 * actualSource k t d = modulus k - b := by
  obtain ⟨i, hi⟩ := hatt
  let d := (finRotate k).symm i
  have hd := source_bounds k t hk d
  have hC := (modulus_quarter k hk).2.1
  have hN := (modulus_quarter k hk).1
  have hs := source_step k t (by omega) d
  have hpred : finRotate k d = i := (finRotate k).apply_symm_apply i
  rw [hpred, hi, doubleStep] at hs
  by_cases hpos : modulus k < 4 * actualSource k t d
  · rw [ite_eq_left hpos] at hs
    omega
  · rw [ite_eq_right hpos] at hs
    by_cases hneg : 4 * actualSource k t d < -modulus k
    · rw [ite_eq_left hneg] at hs
      exact ⟨d, by omega, by omega⟩
    · rw [ite_eq_right hneg] at hs
      have hm := hmin d (by omega)
      omega

private theorem source_extrema (k t : ℕ) (hk : 2 ≤ k) (a b : ℤ)
    (ha : 0 < a) (hb : 0 < b)
    (hamin : ∀ i, actualSource k t i < 0 → a ≤ -actualSource k t i)
    (hbmin : ∀ i, 0 < actualSource k t i → b ≤ actualSource k t i)
    (haatt : ∃ i, actualSource k t i = -a)
    (hbatt : ∃ i, actualSource k t i = b) (p d : Fin k)
    (hpmax : ∀ i, actualSource k t i ≤ actualSource k t p)
    (hdmin : ∀ i, actualSource k t d ≤ actualSource k t i) :
    quarter k ≤ actualSource k t p ∧ actualSource k t d ≤ -quarter k ∧
      2 * actualSource k t p = modulus k - a ∧
      -2 * actualSource k t d = modulus k - b := by
  obtain ⟨p', hp', hpa⟩ := negative_minimum_parent k t hk a ha hamin haatt
  obtain ⟨d', hd', hdb⟩ := positive_minimum_parent k t hk b hb hbmin hbatt
  have hpp := hpmax p'
  have hdd := hdmin d'
  have hp : quarter k ≤ actualSource k t p := by omega
  have hd : actualSource k t d ≤ -quarter k := by omega
  obtain ⟨hsp, hspneg⟩ := source_positive_step k t hk p hp
  obtain ⟨hsd, hsdpos⟩ := source_negative_step k t hk d hd
  have hma := hamin (advance p 1) hspneg
  have hmb := hbmin (advance d 1) hsdpos
  exact ⟨hp, hd, by omega, by omega⟩

private theorem advance_add {k : ℕ} (x : Fin k) (i j : ℕ) :
    advance (advance x i) j = advance x (i + j) := by
  have := x.neZero
  simp [advance_eq, Nat.cast_add, add_assoc]

private def arc {k : ℕ} (x : Fin k) (start len : ℕ) : List (Fin k) :=
  List.ofFn (fun i : Fin len => advance x (start + i.val))

private theorem arc_append {k : ℕ} (x : Fin k) (start u v : ℕ) :
    arc x start u ++ arc x (start + u) v = arc x start (u + v) := by
  apply List.ext_getElem
  · simp [arc]
  · intro i hi hi'
    by_cases hu : i < u
    · rw [List.getElem_append_left (by simpa [arc] using hu)]
      simp [arc]
    · rw [List.getElem_append_right (by simpa [arc] using (show u ≤ i by omega))]
      simp only [arc, List.length_ofFn, List.getElem_ofFn]
      congr 1
      omega

private theorem arc_row {k : ℕ} (x : Fin k) (start len : ℕ) :
    arc x start (len + 1) = advance x start :: rowLabels (advance x start) len := by
  simp only [arc, List.ofFn_succ, Fin.val_zero, Nat.add_zero,
    rowLabels, Fin.val_succ, advance_add]

/-- Physical offsets whose centered source values reach the inclusive threshold. -/
def largeOffsets {k : ℕ} (t : ℕ) (x : Fin k) : Finset (Fin k) :=
  Finset.univ.filter (fun i => quarter k ≤ |actualSource k t (advance x i.val)|)

private theorem large_offsets_card {k t : ℕ} (x : Fin k) :
    (largeOffsets t x).card =
      (Finset.univ.filter (fun i : Fin k => quarter k ≤ |actualSource k t i|)).card := by
  have := x.neZero
  apply Finset.card_bijective (finCycle x) (finCycle x).bijective
  intro i
  simp [largeOffsets, advance_eq, finCycle_apply, add_comm]

/-- Increasing physical LARGE offsets, extended by the original cycle boundary. -/
def cut {k t : ℕ} (x : Fin k) (m : ℕ)
    (hcard : (largeOffsets t x).card = m) (i : ℕ) : ℕ :=
  if hi : i < m then ((largeOffsets t x).orderEmbOfFin hcard ⟨i, hi⟩).val else k

private theorem cut_lt {k t m : ℕ} (x : Fin k)
    (hcard : (largeOffsets t x).card = m) (i : ℕ) (hi : i < m) :
    cut x m hcard i < k := by
  simpa only [cut, dite_eq_left hi] using
    ((largeOffsets t x).orderEmbOfFin hcard ⟨i, hi⟩).isLt

private theorem cut_le {k t m : ℕ} (x : Fin k)
    (hcard : (largeOffsets t x).card = m) (i : ℕ) :
    cut x m hcard i ≤ k := by
  by_cases hi : i < m
  · exact le_of_lt (cut_lt x hcard i hi)
  · simp [cut, hi]

private theorem cut_strict {k t m : ℕ} (x : Fin k)
    (hcard : (largeOffsets t x).card = m) {i j : ℕ} (hij : i < j) (hj : j ≤ m) :
    cut x m hcard i < cut x m hcard j := by
  have hi : i < m := by omega
  by_cases hjm : j < m
  · have hh := ((largeOffsets t x).orderEmbOfFin hcard).strictMono
      (show (⟨i, hi⟩ : Fin m) < ⟨j, hjm⟩ from hij)
    simpa only [cut, dite_eq_left hi, dite_eq_left hjm, Fin.lt_def] using hh
  · have hh := cut_lt x hcard i hi
    simpa only [cut, dite_eq_right hjm] using hh

private theorem cut_zero {k t m : ℕ} (x : Fin k)
    (hcard : (largeOffsets t x).card = m) (hm : 0 < m)
    (hx : quarter k ≤ |actualSource k t x|) : cut x m hcard 0 = 0 := by
  have := x.neZero
  have hz : (0 : Fin k) ∈ largeOffsets t x := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [Fin.val_zero, advance, Function.iterate_zero_apply] using hx
  let e := (largeOffsets t x).orderIsoOfFin hcard
  let j := e.symm ⟨0, hz⟩
  have hj : ((largeOffsets t x).orderEmbOfFin hcard j).val = 0 := by
    have hh := congrArg (fun i : largeOffsets t x => (i.val : Fin k).val)
      (e.apply_symm_apply ⟨0, hz⟩)
    exact hh
  have hle := ((largeOffsets t x).orderEmbOfFin hcard).monotone
    (show (⟨0, hm⟩ : Fin m) ≤ j from Nat.zero_le _)
  have hlev : ((largeOffsets t x).orderEmbOfFin hcard ⟨0, hm⟩).val ≤
      ((largeOffsets t x).orderEmbOfFin hcard j).val := hle
  simpa only [cut, dite_eq_left hm] using (show
    ((largeOffsets t x).orderEmbOfFin hcard ⟨0, hm⟩).val = 0 by omega)

private theorem cut_large {k t m : ℕ} (x : Fin k)
    (hcard : (largeOffsets t x).card = m) (i : ℕ) (hi : i < m) :
    quarter k ≤ |actualSource k t (advance x (cut x m hcard i))| := by
  have hh := (largeOffsets t x).orderEmbOfFin_mem hcard ⟨i, hi⟩
  simpa only [largeOffsets, Finset.mem_filter, Finset.mem_univ, true_and,
    cut, dite_eq_left hi] using hh

private theorem cut_no_large_between {k t m : ℕ} (x : Fin k)
    (hcard : (largeOffsets t x).card = m) (i z : ℕ) (hi : i < m)
    (hlo : cut x m hcard i < z) (hhi : z < cut x m hcard (i + 1)) :
    |actualSource k t (advance x z)| < quarter k := by
  have hzk : z < k := lt_of_lt_of_le hhi (cut_le x hcard _)
  by_contra hlarge
  have hz : (⟨z, hzk⟩ : Fin k) ∈ largeOffsets t x := by
    simp only [largeOffsets, Finset.mem_filter, Finset.mem_univ, true_and]
    exact le_of_not_gt hlarge
  let e := (largeOffsets t x).orderIsoOfFin hcard
  let j := e.symm ⟨⟨z, hzk⟩, hz⟩
  have hj : ((largeOffsets t x).orderEmbOfFin hcard j).val = z := by
    exact congrArg (fun v : largeOffsets t x => (v.val : Fin k).val)
      (e.apply_symm_apply ⟨⟨z, hzk⟩, hz⟩)
  have hij : i < j.val := by
    by_contra hn
    have hh := ((largeOffsets t x).orderEmbOfFin hcard).monotone
      (show j ≤ ⟨i, hi⟩ from le_of_not_gt hn)
    have hhv : ((largeOffsets t x).orderEmbOfFin hcard j).val ≤
        ((largeOffsets t x).orderEmbOfFin hcard ⟨i, hi⟩).val := hh
    simp only [cut, dite_eq_left hi] at hlo
    omega
  have hinext : i + 1 < m := by omega
  have hh := ((largeOffsets t x).orderEmbOfFin hcard).monotone
    (show (⟨i + 1, hinext⟩ : Fin m) ≤ j from hij)
  have hhv : ((largeOffsets t x).orderEmbOfFin hcard ⟨i + 1, hinext⟩).val ≤
      ((largeOffsets t x).orderEmbOfFin hcard j).val := hh
  simp only [cut, dite_eq_left hinext] at hhi
  omega

private theorem cut_own_row {k t m : ℕ} (x : Fin k)
    (hcard : (largeOffsets t x).card = m)
    (hx : quarter k ≤ |actualSource k t x|) (i : ℕ) (hi : i < m) :
    OwnRow k t (advance x (cut x m hcard i))
      (cut x m hcard (i + 1) - cut x m hcard i - 1) := by
  have hlt := cut_strict x hcard (show i < i + 1 by omega) (by omega)
  have hle := cut_le x hcard (i + 1)
  have he : cut x m hcard i +
      (cut x m hcard (i + 1) - cut x m hcard i - 1 + 1) =
      cut x m hcard (i + 1) := by omega
  refine ⟨by omega, cut_large x hcard i hi, ?_, ?_⟩
  · intro j hj
    rw [advance_add]
    apply cut_no_large_between x hcard i _ hi <;> omega
  · rw [advance_add, he]
    by_cases hn : i + 1 < m
    · exact cut_large x hcard (i + 1) hn
    · have hend : cut x m hcard (i + 1) = k := by simp [cut, hn]
      simpa only [hend, advance_cycle] using hx

private theorem cut_arc_partition {k t m : ℕ} (x : Fin k)
    (hcard : (largeOffsets t x).card = m) (hm : 0 < m)
    (hx : quarter k ≤ |actualSource k t x|) :
    ((List.range m).flatMap (fun i =>
      arc x (cut x m hcard i)
        (cut x m hcard (i + 1) - cut x m hcard i))).Perm (List.finRange k) := by
  have hzero := cut_zero x hcard hm hx
  have hprefix (n : ℕ) (hn : n ≤ m) :
      ((List.range n).flatMap (fun i =>
        arc x (cut x m hcard i)
          (cut x m hcard (i + 1) - cut x m hcard i))) =
        arc x 0 (cut x m hcard n) := by
    induction n with
    | zero => simp [hzero, arc]
    | succ n ih =>
      have hle : cut x m hcard n ≤ cut x m hcard (n + 1) :=
        le_of_lt (cut_strict x hcard (by omega) hn)
      rw [List.range_succ, List.flatMap_append, ih (by omega)]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      simpa only [Nat.zero_add, Nat.add_sub_cancel' hle] using
        arc_append x 0 (cut x m hcard n)
          (cut x m hcard (n + 1) - cut x m hcard n)
  rw [hprefix m (le_refl _), show cut x m hcard m = k by simp [cut]]
  simpa only [arc, Nat.zero_add] using physical_cycle_perm x

/-- Offset of the i-th actual LARGE occurrence after x; the boundary offset
is k. This enumeration uses physical labels, not a list of distinct values. -/
def sourceOffset {k : ℕ} (t : ℕ) (x : Fin k) (i : ℕ) : ℕ :=
  cut x (largeOffsets t x).card rfl i

/-- Actual LARGE parents, with x again only as the cyclic boundary. -/
def sourceParent {k : ℕ} (t : ℕ) (x : Fin k) (i : ℕ) : Fin k :=
  advance x (sourceOffset t x i)

/-- Number of literal SMALL labels in the indicated actual own row. -/
def sourceLength {k : ℕ} (t : ℕ) (x : Fin k) (i : ℕ) : ℕ :=
  sourceOffset t x (i + 1) - sourceOffset t x i - 1

/-- Magnitude of the actual wrapped successor; an empty row's seed is its
LARGE terminal. -/
def sourceSeed {k : ℕ} (t : ℕ) (x : Fin k) (i : ℕ) : ℤ :=
  |actualSource k t (advance (sourceParent t x i) 1)|

/-- The original positive-hard R1 M5 slice, stated entirely on the centered
source, its attained extrema, inclusive thresholds, and actual own rows. -/
structure OriginalM5 (k t L : ℕ) (a b : ℤ) (p d x : Fin k) : Prop where
  nonzero : ∀ i : Fin k, actualSource k t i ≠ 0
  a_positive : 0 < a
  minimum_inequalities : a < b ∧ b < 2 * a
  negative_minimum : ∀ i, actualSource k t i < 0 → a ≤ -actualSource k t i
  positive_minimum : ∀ i, 0 < actualSource k t i → b ≤ actualSource k t i
  negative_attained : ∃ i, actualSource k t i = -a
  positive_attained : ∃ i, actualSource k t i = b
  p_maximum : ∀ i, actualSource k t i ≤ actualSource k t p
  d_minimum : ∀ i, actualSource k t d ≤ actualSource k t i
  five_positive : (Finset.univ.filter (fun i : Fin k => quarter k ≤ actualSource k t i)).card = 5
  five_negative : (Finset.univ.filter (fun i : Fin k => actualSource k t i ≤ -quarter k)).card = 5
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
  a0_bound : sourceSeed t x 8 ≤ modulus k - 2 * actualSource k t x

private theorem source_ten {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) :
    2 ≤ k ∧ (largeOffsets t x).card = 10 := by
  have hk5 : 5 ≤ k := by
    have hh := (Finset.univ.filter
      (fun i : Fin k => quarter k ≤ actualSource k t i)).card_le_univ
    simpa only [h.five_positive, Fintype.card_fin] using hh
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
  exact congrArg₂ (· + ·) h.five_positive h.five_negative

private theorem source_parent_zero {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) : sourceParent t x 0 = x := by
  have hc := (source_ten h).2
  have hz := cut_zero x (rfl : (largeOffsets t x).card = (largeOffsets t x).card)
    (by omega) (h.x_positive_large.trans (le_abs_self _))
  change advance x (cut x (largeOffsets t x).card rfl 0) = x
  rw [hz]
  rfl

private theorem source_own_row {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) (i : ℕ) (hi : i < 10) :
    OwnRow k t (sourceParent t x i) (sourceLength t x i) := by
  have hc := (source_ten h).2
  have hx : quarter k ≤ |actualSource k t x| :=
    h.x_positive_large.trans (le_abs_self _)
  have hr := cut_own_row x (rfl : (largeOffsets t x).card = (largeOffsets t x).card)
    hx i (by omega)
  simpa only [sourceParent, sourceOffset, sourceLength] using hr

private theorem source_parent_next {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) (i : ℕ) (hi : i < 10) :
    advance (sourceParent t x i) (sourceLength t x i + 1) = sourceParent t x (i + 1) := by
  have hc := (source_ten h).2
  have hlt := cut_strict x (rfl : (largeOffsets t x).card = (largeOffsets t x).card)
    (show i < i + 1 by omega) (by omega)
  have he : sourceOffset t x i + (sourceLength t x i + 1) = sourceOffset t x (i + 1) := by
    dsimp only [sourceOffset, sourceLength] at *
    omega
  simp only [sourceParent, advance_add, he]

private theorem row_positive_terminal {k t : ℕ} (hk : 2 ≤ k) {x : Fin k} {len : ℕ}
    (hr : OwnRow k t x len) (hp : 0 < actualSource k t x) :
    actualSource k t (advance x (len + 1)) < 0 := by
  have hlarge : quarter k ≤ actualSource k t x := by
    simpa only [abs_of_pos hp] using hr.parent_large
  have hs := (source_positive_step k t hk x hlarge).2
  rw [row_terminal hk hr]
  exact mul_neg_of_pos_of_neg (by positivity) hs

private theorem row_negative_terminal {k t : ℕ} (hk : 2 ≤ k) {x : Fin k} {len : ℕ}
    (hr : OwnRow k t x len) (hp : actualSource k t x < 0) :
    0 < actualSource k t (advance x (len + 1)) := by
  have hlarge : actualSource k t x ≤ -quarter k := by
    have hh := hr.parent_large
    rw [abs_of_neg hp] at hh
    omega
  have hs := (source_negative_step k t hk x hlarge).2
  rw [row_terminal hk hr]
  exact mul_pos (by positivity) hs

private theorem source_parent_boundary {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) : sourceParent t x 10 = x := by
  have hc := (source_ten h).2
  have he : sourceOffset t x 10 = k := by
    simp only [sourceOffset, cut, hc, lt_self_iff_false, dite_false]
  simp only [sourceParent, he, advance_cycle]

private theorem source_parent_sign {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) (i : ℕ) (hi : i ≤ 10) :
    if i % 2 = 0 then 0 < actualSource k t (sourceParent t x i)
      else actualSource k t (sourceParent t x i) < 0 := by
  have hk := (source_ten h).1
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

private theorem source_parent_large {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) (i : ℕ) (hi : i ≤ 10) :
    quarter k ≤ |actualSource k t (sourceParent t x i)| := by
  by_cases hin : i < 10
  · exact (source_own_row h i hin).parent_large
  · have he : i = 10 := by omega
    simpa only [he, source_parent_boundary h] using
      h.x_positive_large.trans (le_abs_self _)

private theorem source_seed_formula {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) (i : ℕ) (hi : i ≤ 10) :
    sourceSeed t x i =
      if i % 2 = 0 then modulus k - 2 * actualSource k t (sourceParent t x i)
        else modulus k + 2 * actualSource k t (sourceParent t x i) := by
  have hk := (source_ten h).1
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

private theorem source_terminal_formula {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) (i : ℕ) (hi : i < 10) :
    actualSource k t (sourceParent t x (i + 1)) =
      if i % 2 = 0 then -(2 : ℤ) ^ sourceLength t x i * sourceSeed t x i
        else (2 : ℤ) ^ sourceLength t x i * sourceSeed t x i := by
  have hk := (source_ten h).1
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

private theorem source_seed_recurrence {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) (i : ℕ) (hi : i < 10) :
    sourceSeed t x (i + 1) = modulus k -
      (2 : ℤ) ^ (sourceLength t x i + 1) * sourceSeed t x i := by
  rw [source_seed_formula h (i + 1) (by omega), source_terminal_formula h i hi]
  by_cases he : i % 2 = 0
  · have hn : (i + 1) % 2 ≠ 0 := by omega
    simp only [he, hn, ite_true, ite_false, pow_succ]
    ring
  · have hn : (i + 1) % 2 = 0 := by omega
    simp only [he, hn, ite_true, ite_false, pow_succ]
    ring

private theorem source_seed_one {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) : sourceSeed t x 1 = b := by
  have hk := (source_ten h).1
  have hd := (source_extrema k t hk a b h.a_positive
    (lt_trans h.a_positive h.minimum_inequalities.1) h.negative_minimum
    h.positive_minimum h.negative_attained h.positive_attained p d
    h.p_maximum h.d_minimum).2.2.2
  have hs := source_seed_formula h 1 (by decide)
  simp only [Nat.one_mod, one_ne_zero, ite_false, h.incoming_d] at hs
  omega

private theorem source_seed_minimum {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) (i : ℕ) (hi : i ≤ 10) :
    if i % 2 = 0 then a ≤ sourceSeed t x i else b ≤ sourceSeed t x i := by
  have hk := (source_ten h).1
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

private theorem source_seed_odd {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) (i : ℕ) (hi : i ≤ 10) :
    sourceSeed t x i % 2 = 1 := by
  have hk := (source_ten h).1
  have hN := (modulus_quarter k hk).1
  rw [source_seed_formula h i hi]
  split_ifs <;> omega

private theorem source_core {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) :
    let H := (2 : ℤ) ^ (L + 1)
    let z := sourceSeed t x 0
    let n := sourceSeed t x 2
    let Δ := b - z
    8 ≤ H ∧ 2 ≤ L ∧ 2 ≤ Δ ∧ Δ % 2 = 0 ∧
      modulus k = H * z + b ∧ modulus k = H * b + n ∧
      z = n + (H - 1) * Δ ∧ b = n + H * Δ ∧
      sourceSeed t x 3 = n + H ^ 2 * Δ ∧
      a ≤ n ∧ n < z ∧ z < b ∧ H * Δ < n := by
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
      source_seed_formula h 0 (by decide)
  have hF : 2 ≤ (2 : ℤ) ^ (sourceLength t x 6 + 1) := by
    rw [pow_succ]
    have hp : (1 : ℤ) ≤ 2 ^ sourceLength t x 6 :=
      one_le_pow₀ (by decide)
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
      source_seed_recurrence h 0 (by decide)
  have h1 : n = modulus k - H * b := by
    simpa only [h.d_row_length, source_seed_one h, H, n] using
      source_seed_recurrence h 1 (by decide)
  have h2 : sourceSeed t x 3 = modulus k - H * n := by
    simpa only [h.beta_row_length, H, n] using
      source_seed_recurrence h 2 (by decide)
  have hΔ : 0 < Δ := by simpa only [Δ, hz] using h.delta_positive
  have hoddz := source_seed_odd h 0 (by decide)
  have hoddb : b % 2 = 1 := by
    simpa only [source_seed_one h] using source_seed_odd h 1 (by decide)
  have hΔeven : Δ % 2 = 0 := by dsimp only [Δ, z]; omega
  have hΔ2 : 2 ≤ Δ := by omega
  have hn : a ≤ n := by
    simpa only [n, Nat.reduceMod, ite_true] using source_seed_minimum h 2 (by decide)
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

private theorem source_partition {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalM5 k t L a b p d x) :
    ((List.range 10).flatMap (fun i => sourceParent t x i ::
      rowLabels (sourceParent t x i) (sourceLength t x i))).Perm (List.finRange k) := by
  let m := (largeOffsets t x).card
  have hc : m = 10 := (source_ten h).2
  have hm : 0 < m := by omega
  have hx := h.x_positive_large.trans (le_abs_self _)
  have hp := cut_arc_partition x (rfl : (largeOffsets t x).card = m) hm hx
  have he : ((List.range m).flatMap (fun i =>
      arc x (cut x m rfl i) (cut x m rfl (i + 1) - cut x m rfl i))) =
      ((List.range m).flatMap (fun i => sourceParent t x i ::
        rowLabels (sourceParent t x i) (sourceLength t x i))) := by
    apply List.flatMap_congr
    intro i hi
    have hil : i < m := List.mem_range.mp hi
    have hlt := cut_strict x (rfl : (largeOffsets t x).card = m)
      (show i < i + 1 by omega) (by omega)
    have hlen : cut x m rfl (i + 1) - cut x m rfl i = sourceLength t x i + 1 := by
      dsimp only [sourceLength, sourceOffset]
      change cut x m rfl (i + 1) - cut x m rfl i =
        cut x m rfl (i + 1) - cut x m rfl i - 1 + 1
      dsimp only [m] at hlt ⊢
      omega
    rw [hlen, arc_row]
    rfl
  rw [he] at hp
  simpa only [hc] using hp


end D5.S3.Combinatorics.Circle.M5FullWordConsumer
