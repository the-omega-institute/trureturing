import D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Endpoint
import D5.S3.Combinatorics.Circle.PeriodicShorteningArithmetic
import D5.S3.Combinatorics.Circle.RunFirstEarTransport
import D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift

/- GID: D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftArithmetic
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Literal phase-stable physical source rows for eight-bit insertion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.EightBitPhysicalLift

open SourceWidth PeriodicShortening PeriodicShorteningArithmetic
open RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift
open D5.S3.Combinatorics.Circle.SparseNecklaceRounding
open scoped BigOperators

/-! The target label map used by the insertion-only lift.  The first eight
labels are the inserted physical labels and every old label is shifted by
eight. -/
def liftOldLabel {k : ℕ} (i : Fin (k + 1)) : Fin (k + 9) :=
  ⟨i.val + 8, by have hi := i.isLt; omega⟩

def liftFreshLabel (k : ℕ) : Fin (k + 9) :=
  liftOldLabel (Fin.last k)

def liftNewLabel {k : ℕ} (i : Fin 8) : Fin (k + 9) :=
  ⟨i.val, by omega⟩

def insertionMask (T : ℕ) : ℕ := T % 256

def targetN (k : ℕ) : ℤ := modulus (k + 8)

def targetH (k : ℕ) : ℤ := 256 * (modulus k / 2) + 255

def canonicalFirst (k : ℕ) (F C : ℤ) (T : ℕ) : ℤ :=
  256 * F - 255 * C + 85 * (insertionMask T)

def canonicalSecond (k : ℕ) (Y C : ℤ) (T : ℕ) (b : Bool) : ℤ :=
  256 * Y - 255 * C - 21675 * (if b then 1 else 0) +
    170 * (insertionMask T)

def insertionDeletion {k : ℕ} (w : List (Fin (k + 9))) : List (Fin (k + 1)) :=
  w.filterMap (fun i => if h : 8 ≤ i.val then
    some ⟨i.val - 8, by omega⟩ else none)

def insertionMaskUpTo (T : ℕ) (i : Fin 8) : ℕ :=
  insertionMask (T + 2 ^ i.val)

/-! The charge is phase-stable under the eight-bit shift.  These are the
literal row identities used below; keeping them separate makes the later
prefix argument consume the actual source, rather than an assumed table. -/
theorem charge_shift_eight (k : ℕ) (i : Fin k) :
    charge (k + 8) 85 ⟨i.val + 8, by omega⟩ = charge k 85 i := by
  change (let z := (85 : ℤ) / (2 : ℤ) ^ (k + 8 - 1 - (i.val + 8));
      z / 2 + z % 2) =
    (let z := (85 : ℤ) / (2 : ℤ) ^ (k - 1 - i.val); z / 2 + z % 2)
  simp only [show k + 8 - 1 - (i.val + 8) = k - 1 - i.val by omega]

theorem target_old_first_row (k : ℕ) (hk : 8 ≤ k) (i : Fin k) :
    actualSource (k + 8) 85 ⟨i.val + 8, by omega⟩ =
      256 * actualSource k 85 i - 255 * charge k 85 i := by
  have hp : 2 ^ 7 ≤ 2 ^ (k - 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hw0 : 85 ≤ 2 ^ (k - 1) - 1 := by norm_num at hp ⊢; omega
  have hp' : 2 ^ (k - 1) ≤ 2 ^ (k + 8 - 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hw1 : 85 ≤ 2 ^ (k + 8 - 1) - 1 := by omega
  have h0 := digit_data k 85 (by omega) hw0 i
  have h1 := digit_data (k + 8) 85 (by omega) hw1
      ⟨i.val + 8, by omega⟩
  simp only [Fin.val_mk] at h0 h1 ⊢
  rw [h0.2.1, h1.2.1, charge_shift_eight]
  rw [show (2 : ℤ) ^ (i.val + 8) = (2 : ℤ) ^ 8 * 2 ^ i.val by
    rw [pow_add]; ring]
  rw [show (2 : ℤ) ^ (k + 8) = (2 : ℤ) ^ 8 * 2 ^ k by
    rw [pow_add]; ring]
  norm_num
  ring

theorem target_new_first_row (k : ℕ) (hk : 8 ≤ k) (j : Fin 8) :
    actualSource (k + 8) 85 ⟨j.val, by omega⟩ =
      85 * (2 : ℤ) ^ j.val := by
  have hp : 2 ^ 7 ≤ 2 ^ (k + 8 - 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hw : 85 ≤ 2 ^ (k + 8 - 1) - 1 := by norm_num at hp ⊢; omega
  have h := digit_data (k + 8) 85 (by omega) hw
      ⟨j.val, by omega⟩
  have he : 8 ≤ k + 8 - 1 - j.val := by omega
  have hpe : (2 : ℤ) ^ 8 ≤ 2 ^ (k + 8 - 1 - j.val) := by
    exact pow_le_pow_right₀ (by norm_num) he
  have hpe' : (85 : ℤ) < 2 ^ (k + 8 - 1 - j.val) := by
    norm_num at hpe ⊢
    omega
  have hz : (85 : ℤ) / 2 ^ (k + 8 - 1 - j.val) = 0 :=
    Int.ediv_eq_zero_of_lt (by norm_num) hpe'
  have hz' : (85 : ℤ) / 2 ^ (k + 7 - j.val) = 0 := by
    have heq : k + 8 - 1 - j.val = k + 7 - j.val := by omega
    simpa [heq] using hz
  have hc : charge (k + 8) 85 ⟨j.val, by omega⟩ = 0 := by
    simp [charge, hz']
  rw [h.2.1, hc]
  ring

theorem target_new_second_row (k : ℕ) (hk : 8 ≤ k) (j : Fin 8) :
    actualSource (k + 9) 170 ⟨j.val, by omega⟩ =
      170 * (2 : ℤ) ^ j.val := by
  have hp : 2 ^ 8 ≤ 2 ^ (k + 9 - 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hw : 170 ≤ 2 ^ (k + 9 - 1) - 1 := by norm_num at hp ⊢; omega
  have h := digit_data (k + 9) 170 (by omega) hw
      ⟨j.val, by omega⟩
  have he : 9 ≤ k + 9 - 1 - j.val := by omega
  have hpe : (2 : ℤ) ^ 9 ≤ 2 ^ (k + 9 - 1 - j.val) := by
    exact pow_le_pow_right₀ (by norm_num) he
  have hpe' : (170 : ℤ) < 2 ^ (k + 9 - 1 - j.val) := by
    norm_num at hpe ⊢
    omega
  have hz : (170 : ℤ) / 2 ^ (k + 9 - 1 - j.val) = 0 :=
    Int.ediv_eq_zero_of_lt (by norm_num) hpe'
  have hz' : (170 : ℤ) / 2 ^ (k + 8 - j.val) = 0 := by
    have heq : k + 9 - 1 - j.val = k + 8 - j.val := by omega
    simpa [heq] using hz
  have hc : charge (k + 9) 170 ⟨j.val, by omega⟩ = 0 := by
    simp [charge, hz']
  rw [h.2.1, hc]
  ring

/-! A literal insertion-only word.  The orientation function chooses the
order inside each of the eight old/new pairs; every old occurrence is mapped
by `liftOldLabel`, so the old relative order is built into the definition. -/
def physicalLiftWord {k : ℕ} (sigma : List (Fin (k + 1)))
    (orientation : Fin 8 → Bool) : List (Fin (k + 9)) :=
  sigma.flatMap (fun j =>
    if hj : j.val < 8 then
      let i : Fin 8 := ⟨j.val, hj⟩
      if orientation i then
        [liftOldLabel j, liftNewLabel i]
      else
        [liftNewLabel i, liftOldLabel j]
    else
      [liftOldLabel j])

theorem insertionDeletion_physicalLiftWord {k : ℕ}
    (sigma : List (Fin (k + 1))) (orientation : Fin 8 → Bool) :
    insertionDeletion (physicalLiftWord sigma orientation) = sigma := by
  induction sigma with
  | nil => simp [physicalLiftWord, insertionDeletion]
  | cons j js ih =>
    change insertionDeletion (_ ++ physicalLiftWord js orientation) = j :: js
    by_cases hj : j.val < 8
    · let i : Fin 8 := ⟨j.val, hj⟩
      simp only [dif_pos hj]
      have hb : insertionDeletion
          (if orientation i then [liftOldLabel j, liftNewLabel i]
           else [liftNewLabel i, liftOldLabel j]) = [j] := by
        by_cases ho : orientation i <;>
          simp [ho, insertionDeletion, liftOldLabel, liftNewLabel, hj, i]
      simp only [insertionDeletion, List.filterMap_append]
      have hb' := hb
      simp only [insertionDeletion] at hb'
      have ih' := ih
      simp only [insertionDeletion] at ih'
      rw [hb', ih']
      rfl
    · simp only [dif_neg hj]
      have hb : insertionDeletion [liftOldLabel j] = [j] := by
        simp [insertionDeletion, liftOldLabel, hj]
      simp only [insertionDeletion, List.filterMap_append]
      have hb' := hb
      simp only [insertionDeletion] at hb'
      have ih' := ih
      simp only [insertionDeletion] at ih'
      rw [hb', ih']
      rfl

theorem target_bounds (k : ℕ) (hk : 2 ≤ k) :
    targetN k = 256 * modulus k + 255 ∧
    targetH k = 256 * (modulus k / 2) + 255 := by
  unfold targetN targetH
  constructor
  · unfold modulus
    rw [show k + 8 = k + 8 by rfl, pow_add]
    norm_num
    ring
  · rfl

theorem insertion_mask_range (T : ℕ) :
    0 ≤ (insertionMask T : ℤ) ∧ (insertionMask T : ℤ) ≤ 255 := by
  unfold insertionMask
  have h := Nat.mod_lt T (by decide : 0 < 256)
  omega

theorem canonical_endpoint_formula (k : ℕ) (F Y C : ℤ) (T : ℕ) (b : Bool)
    (hRel : Y = 2 * F - C + 85 * (if b then 1 else 0)) :
    canonicalSecond k Y C T b =
      2 * canonicalFirst k F C T - C + 85 * (if b then 1 else 0) := by
  unfold canonicalFirst canonicalSecond
  rw [hRel]
  by_cases hb : b
  · simp [hb]
    ring
  · simp [hb]
    ring

theorem canonical_endpoint_lift
    (k : ℕ) (F Y C : ℤ) (T : ℕ) (b : Bool) (r : ℤ)
    (hF : 0 ≤ F ∧ F ≤ modulus k / 2)
    (hY : 0 ≤ Y ∧ Y ≤ modulus k)
    (hC : 0 ≤ C ∧ C ≤ 85)
    (hRel : Y = 2 * F - C + 85 * (if b then 1 else 0))
    (hr : (insertionMask T : ℤ) + 3 * F - 3 * C = 256 * r)
    (hr0 : 0 ≤ r)
    (hroomF : 21760 * r ≤ targetH k - modulus k / 2)
    (hroomY : 43520 * r ≤ targetN k - modulus k) :
    0 ≤ canonicalFirst k F C T ∧
      canonicalFirst k F C T ≤ targetH k ∧
      0 ≤ canonicalSecond k Y C T b ∧
      canonicalSecond k Y C T b ≤ targetN k := by
  have hu : 0 ≤ (insertionMask T : ℤ) := (insertion_mask_range T).1
  have hu' : (insertionMask T : ℤ) ≤ 255 := (insertion_mask_range T).2
  have hFform : canonicalFirst k F C T = F + 21760 * r := by
    unfold canonicalFirst
    calc
      256 * F - 255 * C + 85 * (insertionMask T : ℤ) =
          F + 85 * ((insertionMask T : ℤ) + 3 * F - 3 * C) := by ring
      _ = F + 21760 * r := by rw [hr]; ring
  have hYform : canonicalSecond k Y C T b = Y + 43520 * r := by
    calc
      canonicalSecond k Y C T b =
          2 * canonicalFirst k F C T - C + 85 * (if b then 1 else 0) :=
        canonical_endpoint_formula k F Y C T b hRel
      _ = 2 * (F + 21760 * r) - C + 85 * (if b then 1 else 0) := by rw [hFform]
      _ = Y + 43520 * r := by rw [hRel]; ring
  rw [hFform, hYform]
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · omega

end D5.S3.Combinatorics.Circle.FourNegative.EightBitPhysicalLift
