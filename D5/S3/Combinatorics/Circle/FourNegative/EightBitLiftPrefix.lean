/- GID: D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftPrefix
   generality: I
   mirror-B: none(waiver:consumed-by-eight-bit-physical-lift)
   mirror-E: none(waiver:dependent-physical-source-audit)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Literal physical eight-bit insertion and its charge-prefix proof. -/
import D5.S3.Combinatorics.Circle.FourNegative.EightBitLiftLocal

/-! # Canonical states of complete physical prefixes -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.EightBitPhysicalLift

open SourceWidth PeriodicShortening PeriodicShorteningArithmetic RunFirstEarTransport
open scoped BigOperators

def fullFirst (k : ℕ) : Fin (k + 1) → ℤ :=
  Fin.lastCases 0 (actualSource k 85)

def fullCharge (k : ℕ) : Fin (k + 1) → ℤ :=
  Fin.lastCases 0 (charge k 85)

def fullWeight (k : ℕ) : Fin (k + 1) → ℤ :=
  Fin.lastCases 0 (fun i => (2 : ℤ) ^ i.val)

def lowWeight {k : ℕ} (j : Fin (k + 1)) : ℤ :=
  if j.val < 8 then 2 ^ j.val else 0

def earIndicator {k : ℕ} (j : Fin (k + 1)) : ℤ :=
  if j.val = k then 1 else 0

def firstState {k : ℕ} (l : List (Fin (k + 1))) : ℤ :=
  256 * (l.map (fullFirst k)).sum - 255 * (l.map (fullCharge k)).sum +
    85 * (l.map lowWeight).sum

def secondState {k : ℕ} (l : List (Fin (k + 1))) : ℤ :=
  256 * (l.map (actualSource (k + 1) 170)).sum -
    255 * (l.map (fullCharge k)).sum - 21675 * (l.map earIndicator).sum +
    170 * (l.map lowWeight).sum

def JointWord (k : ℕ) (w : List (Fin (k + 1))) : Prop :=
  w.Perm (List.finRange (k + 1)) ∧
    (w.map (fullFirst k)).sum = 0 ∧
    (w.map (actualSource (k + 1) 170)).sum = 0 ∧
    ∀ n, 0 ≤ ((w.take n).map (fullFirst k)).sum ∧
      ((w.take n).map (fullFirst k)).sum ≤ modulus k / 2 ∧
      0 ≤ ((w.take n).map (actualSource (k + 1) 170)).sum ∧
      ((w.take n).map (actualSource (k + 1) 170)).sum ≤ modulus k

theorem dimension_room (k : ℕ) (hk : 8 ≤ k) :
    85 ≤ 2 ^ (k - 1) - 1 := by
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 7 ≤ k - 1 by omega)
  norm_num at hp
  omega

theorem full_source_rows (k : ℕ) (hk : 8 ≤ k) (j : Fin (k + 1)) :
    0 ≤ fullCharge k j ∧
    fullFirst k j = 85 * fullWeight k j - modulus k * fullCharge k j ∧
    actualSource (k + 1) 170 j =
      2 * fullFirst k j - fullCharge k j + 85 * earIndicator j := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [fullFirst, fullCharge, fullWeight, Fin.lastCases_last,
      earIndicator, Fin.val_last, if_pos rfl]
    constructor
    · norm_num
    constructor
    · ring
    · have h := (digit_data (k + 1) 170 (by omega) (by
          have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 8 ≤ k by omega)
          simp only [Nat.add_sub_cancel] 
          norm_num at hp; omega) (Fin.last k)).2.1
      have hc : charge (k + 1) 170 (Fin.last k) = 85 := by norm_num [charge]
      rw [hc] at h
      simp only [Fin.val_last, pow_succ] at h
      simp only [ite_true]
      convert h using 1 <;> ring
  · have h := digit_data k 85 (by omega) (dimension_room k hk) i
    have heq : actualSource (k + 1) 170 i.castSucc =
        actualSource (k + 1) 85 ⟨i.val + 1, by omega⟩ := by
      unfold actualSource
      simp only [Fin.val_castSucc, Fin.val_mk, pow_succ]
      congr 1
      ring
    simp only [fullFirst, fullCharge, fullWeight, Fin.lastCases_castSucc,
      earIndicator, Fin.val_castSucc, if_neg (show i.val ≠ k by omega)]
    rw [heq, h.2.2]
    exact ⟨h.1, by simpa [modulus, mul_comm] using h.2.1, by ring⟩

theorem full_prefix_rows (k : ℕ) (hk : 8 ≤ k) (l : List (Fin (k + 1))) :
    (l.map (fullFirst k)).sum = 85 * (l.map (fullWeight k)).sum -
      modulus k * (l.map (fullCharge k)).sum ∧
    (l.map (actualSource (k + 1) 170)).sum =
      2 * (l.map (fullFirst k)).sum - (l.map (fullCharge k)).sum +
        85 * (l.map earIndicator).sum := by
  induction l with
  | nil => simp
  | cons j l ih =>
      have h := full_source_rows k hk j
      simp only [List.map_cons, List.sum_cons]
      constructor
      · rw [h.2.1, ih.1]; ring
      · rw [h.2.2, ih.2]; ring

theorem full_charge_total (k : ℕ) (hk : 8 ≤ k) :
    ((List.finRange (k + 1)).map (fullCharge k)).sum = 85 := by
  rw [List.finRange_succ_last, List.map_append, List.sum_append]
  simp only [List.map_map, Function.comp_def, fullCharge, Fin.lastCases_castSucc,
    Fin.lastCases_last, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  rw [← List.sum_toFinset _ (List.nodup_finRange k), List.toFinset_finRange]
  exact charge_sum k 85 (by omega) (dimension_room k hk)

theorem indicator_total (k : ℕ) :
    ((List.finRange (k + 1)).map (earIndicator (k := k))).sum = 1 := by
  rw [List.finRange_succ_last, List.map_append, List.sum_append]
  have hz : (List.finRange k).map (fun i => earIndicator i.castSucc) =
      List.replicate k (0 : ℤ) := by
    have h := List.map_eq_replicate_iff.mpr (fun (i : Fin k) (_ : i ∈ List.finRange k) =>
      show earIndicator i.castSucc = (0 : ℤ) by simp [earIndicator, ne_of_lt i.isLt])
    simpa only [List.length_finRange] using h
  simp only [List.map_map, Function.comp_def]
  rw [hz]
  simp [earIndicator]

theorem prefix_nonnegative_le {α : Type*} (w : List α) (f : α → ℤ)
    (hf : ∀ j, 0 ≤ f j) (n : ℕ) :
    0 ≤ ((w.take n).map f).sum ∧ ((w.take n).map f).sum ≤ (w.map f).sum := by
  have h0 (l : List α) : 0 ≤ (l.map f).sum := by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
    exact hf j
  have he := congrArg (fun l : List α => (l.map f).sum) (List.take_append_drop n w)
  simp only [List.map_append, List.sum_append] at he
  exact ⟨h0 _, by linarith [h0 (w.drop n)]⟩

theorem full_prefix_inventory (k : ℕ) (hk : 8 ≤ k)
    (w : List (Fin (k + 1))) (hw : w.Perm (List.finRange (k + 1))) (n : ℕ) :
    (0 ≤ ((w.take n).map (fullCharge k)).sum ∧
      ((w.take n).map (fullCharge k)).sum ≤ 85) ∧
    (0 ≤ ((w.take n).map earIndicator).sum ∧
      ((w.take n).map earIndicator).sum ≤ 1) := by
  have hc := prefix_nonnegative_le w (fullCharge k)
    (fun j => (full_source_rows k hk j).1) n
  have he := prefix_nonnegative_le w earIndicator (fun j => by
    simp only [earIndicator]; split_ifs <;> norm_num) n
  rw [(hw.map _).sum_eq, full_charge_total k hk] at hc
  rw [(hw.map _).sum_eq, indicator_total k] at he
  exact ⟨hc, he⟩


theorem low_weight_total (k : ℕ) (hk : 8 ≤ k) :
    ((List.finRange (k + 1)).map (lowWeight (k := k))).sum = 255 := by
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  change (∑ i : Fin (k + 1), if i.val < 8 then (2 : ℤ) ^ i.val else 0) = 255
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < 8 then (2 : ℤ) ^ i else 0)]
  have he : (∑ i ∈ Finset.range (k + 1), if i < 8 then (2 : ℤ) ^ i else 0) =
      ∑ i ∈ Finset.range 8, (2 : ℤ) ^ i := by
    rw [← Finset.sum_subset (show Finset.range 8 ⊆ Finset.range (k + 1) by
      intro i hi; simp only [Finset.mem_range] at *; omega)
      (by intro i hi hn; simp only [Finset.mem_range] at hn; simp [hn])]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  rw [he]
  norm_num [Finset.sum_range_succ]

theorem weight_decomposition (k : ℕ) (hk : 8 ≤ k) (j : Fin (k + 1)) :
    fullWeight k j = lowWeight j +
      256 * ((fullWeight k j - lowWeight j) / 256) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [fullWeight, lowWeight, show ¬ k < 8 by omega]
  · simp only [fullWeight, Fin.lastCases_castSucc, lowWeight, Fin.val_castSucc]
    by_cases hi : i.val < 8
    · simp [hi]
    · have he : (2 : ℤ) ^ i.val = 256 * 2 ^ (i.val - 8) := by
        rw [show i.val = (i.val - 8) + 8 by omega, pow_add]
        norm_num
        ring
      simp [hi, he]

theorem prefix_weight_decomposition (k : ℕ) (hk : 8 ≤ k)
    (l : List (Fin (k + 1))) :
    (l.map (fullWeight k)).sum = (l.map lowWeight).sum + 256 *
      (l.map (fun j => (fullWeight k j - lowWeight j) / 256)).sum := by
  induction l with
  | nil => simp
  | cons j l ih =>
      simp only [List.map_cons, List.sum_cons]
      calc
        fullWeight k j + (l.map (fullWeight k)).sum =
          (lowWeight j + 256 * ((fullWeight k j - lowWeight j) / 256)) +
            ((l.map lowWeight).sum + 256 *
              (l.map (fun j => (fullWeight k j - lowWeight j) / 256)).sum) :=
          congrArg₂ (· + ·) (weight_decomposition k hk j) ih
        _ = _ := by ring

theorem integer_canonical_endpoint (k : ℕ) (hk : 9 ≤ k)
    (F Y C u Q e : ℤ)
    (hF : 0 ≤ F ∧ F ≤ modulus k / 2)
    (hY : 0 ≤ Y ∧ Y ≤ modulus k)
    (hC : 0 ≤ C ∧ C ≤ 85) (hu : 0 ≤ u ∧ u ≤ 255)
    (hbase : F = 85 * (u + 256 * Q) - modulus k * C)
    (hrel : Y = 2 * F - C + 85 * e) :
    0 ≤ 256 * F - 255 * C + 85 * u ∧
      256 * F - 255 * C + 85 * u ≤ targetH k ∧
      0 ≤ 256 * Y - 255 * C - 21675 * e + 170 * u ∧
      256 * Y - 255 * C - 21675 * e + 170 * u ≤ targetN k := by
  let B : ℤ := 2 ^ (k - 1)
  let q : ℤ := 2 ^ (k - 9)
  have hB : B = 256 * q := by
    dsimp [B, q]
    rw [show k - 1 = (k - 9) + 8 by omega, pow_add]
    norm_num
    ring
  have hN : modulus k = 2 * B - 1 := by
    unfold modulus
    rw [show k = (k - 1) + 1 by omega, pow_succ]
    dsimp [B]
    ring
  have hH : modulus k / 2 = B - 1 := by rw [hN]; omega
  let r := u + 255 * Q - 6 * q * C
  have hr : u + 3 * F - 3 * C = 256 * r := by
    rw [hbase, hN, hB]
    dsimp [r]
    ring
  have hr0 : 0 ≤ r := by omega
  have hrmax : r ≤ 3 * q := by rw [hH, hB] at hF; omega
  have hx : 256 * F - 255 * C + 85 * u = F + 21760 * r := by omega
  have hz : 256 * Y - 255 * C - 21675 * e + 170 * u = Y + 43520 * r := by omega
  rw [hx, hz, targetH, hH, (target_bounds k (by omega)).1, hN]
  rw [hH] at hF
  rw [hN] at hY
  simp only [hB] at *
  omega

theorem canonical_complete_prefix (k : ℕ) (hk : 8 ≤ k)
    (w : List (Fin (k + 1))) (hw : JointWord k w) (n : ℕ) :
    0 ≤ firstState (w.take n) ∧ firstState (w.take n) ≤ targetH k ∧
    0 ≤ secondState (w.take n) ∧ secondState (w.take n) ≤ targetN k ∧
    (k = 8 → firstState (w.take n) ≤ 21845) := by
  have hrange := hw.2.2.2 n
  have hinv := full_prefix_inventory k hk w hw.1 n
  have hlow := prefix_nonnegative_le w lowWeight (fun j => by
    simp only [lowWeight]; split_ifs <;> positivity) n
  rw [(hw.1.map _).sum_eq, low_weight_total k hk] at hlow
  have hrows := full_prefix_rows k hk (w.take n)
  have hweight := prefix_weight_decomposition k hk (w.take n)
  by_cases hk8 : k = 8
  · subst k
    have hweights : (w.take n).map (fullWeight 8) = (w.take n).map lowWeight := by
      apply List.map_congr_left
      intro j _
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [fullWeight, Fin.lastCases_last, lowWeight, Fin.val_last]
        norm_num
      · simp [fullWeight, lowWeight, i.isLt]
    rw [hweights] at hrows
    let F := ((w.take n).map (fullFirst 8)).sum
    let Y := ((w.take n).map (actualSource 9 170)).sum
    let C := ((w.take n).map (fullCharge 8)).sum
    let u := ((w.take n).map lowWeight).sum
    let e := ((w.take n).map earIndicator).sum
    change 0 ≤ F ∧ F ≤ 127 ∧ 0 ≤ Y ∧ Y ≤ 255 at hrange
    change F = 85 * u - 255 * C ∧ Y = 2 * F - C + 85 * e at hrows
    have hF : F = 0 ∨ F = 85 := by omega
    change 0 ≤ 256 * F - 255 * C + 85 * u ∧
      256 * F - 255 * C + 85 * u ≤ 32767 ∧
      0 ≤ 256 * Y - 255 * C - 21675 * e + 170 * u ∧
      256 * Y - 255 * C - 21675 * e + 170 * u ≤ 65535 ∧
      (8 = 8 → 256 * F - 255 * C + 85 * u ≤ 21845)
    rcases hF with hF | hF <;> omega
  · have hk9 : 9 ≤ k := by omega
    have hbase := hrows.1
    rw [hweight] at hbase
    have he := integer_canonical_endpoint k hk9 _ _ _ _ _ _
      ⟨hrange.1, hrange.2.1⟩ ⟨hrange.2.2.1, hrange.2.2.2⟩
      hinv.1 hlow hbase hrows.2
    exact ⟨he.1, he.2.1, he.2.2.1, he.2.2.2, by omega⟩

end D5.S3.Combinatorics.Circle.FourNegative.EightBitPhysicalLift
