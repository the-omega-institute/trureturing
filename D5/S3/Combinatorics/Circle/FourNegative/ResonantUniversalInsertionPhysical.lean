/- GID: D5/S3/Combinatorics/Circle/FourNegative/ResonantUniversalInsertionPhysical
   generality: I
   mirror-B: none(waiver:universal-resonant-source)
   mirror-E: none(waiver:dependent-physical-source-audit)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Universal resonant physical insertion rows and prefix states. -/
import D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertionCorridor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion

open SourceWidth PeriodicShortening PeriodicShorteningArithmetic
open RunFirstEarTransport
open scoped BigOperators

def resonantTargetFirst (k ell seed : ℕ) : Fin (k + ell + 1) → ℤ :=
  Fin.lastCases 0 (actualSource (k + ell) seed)

def resonantTargetSecond (k ell seed : ℕ) : Fin (k + ell + 1) → ℤ :=
  actualSource (k + ell + 1) (2 * seed)

def resonantLowWeight {k ell : ℕ} (j : Fin (k + 1)) : ℤ :=
  if j.val < ell then (2 : ℤ) ^ j.val else 0

def resonantSourceWord (k seed : ℕ) (word : List (Fin (k + 1))) : Prop :=
  word.Perm (List.finRange (k + 1)) ∧
    (word.map (resonantFirst k seed)).sum = 0 ∧
    (word.map (actualSource (k + 1) (2 * seed))).sum = 0 ∧
    ∀ n, 0 ≤ ((word.take n).map (resonantFirst k seed)).sum ∧
      ((word.take n).map (resonantFirst k seed)).sum ≤ modulus k / 2 ∧
      0 ≤ ((word.take n).map (actualSource (k + 1) (2 * seed))).sum ∧
      ((word.take n).map (actualSource (k + 1) (2 * seed))).sum ≤ modulus k

def resonantTargetWord (k ell seed : ℕ) (word : List (Fin (k + ell + 1))) : Prop :=
  word.Perm (List.finRange (k + ell + 1)) ∧
    (word.map (resonantTargetFirst k ell seed)).sum = 0 ∧
    (word.map (resonantTargetSecond k ell seed)).sum = 0 ∧
    ∀ n, 0 ≤ ((word.take n).map (resonantTargetFirst k ell seed)).sum ∧
      ((word.take n).map (resonantTargetFirst k ell seed)).sum ≤
        modulus (k + ell) / 2 ∧
      0 ≤ ((word.take n).map (resonantTargetSecond k ell seed)).sum ∧
      ((word.take n).map (resonantTargetSecond k ell seed)).sum ≤ modulus (k + ell)

theorem resonant_target_old_first {w ell k m : ℕ}
    (hell : 1 ≤ ell) (hm : m = 2 ^ ell) (hw : 1 ≤ w)
    (hdiv : w ∣ m - 1) (hlarge : 3 * w + 1 ≤ m)
    (hroom : w ≤ 2 ^ (k - 1) - 1)
    (hk : 2 ≤ k) (hkl : ell ≤ k) (j : Fin (k + 1)) :
    resonantTargetFirst k ell w (liftOldLabel j) =
      (m : ℤ) * resonantFirst k w j -
        (m - 1 : ℕ) * resonantCharge k w j := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have he : liftOldLabel (k := k) (ell := ell) (Fin.last k) =
        (Fin.last (k + ell) : Fin (k + ell + 1)) := by
      apply Fin.ext
      simp [liftOldLabel]
    rw [he]
    simp [resonantTargetFirst, resonantFirst, resonantCharge]
  · have hnewroom : w ≤ 2 ^ (k + ell - 1) - 1 := by
      have hp : 2 ^ (k - 1) ≤ 2 ^ (k + ell - 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hB : 0 < 2 ^ (k - 1) := by positivity
      omega
    have h := shifted_source_row hell hm (by omega : 0 < w) hdiv hroom hnewroom hk i
    have he : liftOldLabel (k := k) (ell := ell) i.castSucc =
        (⟨i.val + ell, by omega⟩ : Fin (k + ell)).castSucc := by
      apply Fin.ext
      rfl
    rw [he]
    simpa only [resonantTargetFirst, Fin.lastCases_castSucc,
      resonantFirst, resonantCharge] using h

theorem resonant_target_new_first {w ell k m : ℕ}
    (hell : 1 ≤ ell) (hm : m = 2 ^ ell) (hroom : w ≤ 2 ^ (k - 1) - 1)
    (hk : 2 ≤ k) (i : Fin ell) :
    resonantTargetFirst k ell w (liftNewLabel i) = (w : ℤ) * 2 ^ i.val := by
  have h := resonant_low_source_row hell hm hroom hk i
  have he : liftNewLabel (k := k) (ell := ell) i =
      (⟨i.val, by omega⟩ : Fin (k + ell)).castSucc := by
    apply Fin.ext
    rfl
  rw [he]
  simpa only [resonantTargetFirst, Fin.lastCases_castSucc] using h.1

theorem resonant_target_old_charge {w ell k m : ℕ}
    (j : Fin (k + 1)) :
    resonantCharge (k + ell) w (liftOldLabel j) = resonantCharge k w j := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have he : liftOldLabel (k := k) (ell := ell) (Fin.last k) =
        (Fin.last (k + ell) : Fin (k + ell + 1)) := by
      apply Fin.ext
      simp [liftOldLabel]
    rw [he]
    simp [resonantCharge]
  · simp only [resonantCharge, Fin.lastCases_castSucc]
    have he : liftOldLabel (k := k) (ell := ell) i.castSucc =
        (⟨i.val + ell, by omega⟩ : Fin (k + ell)).castSucc := by
      apply Fin.ext
      rfl
    rw [he]
    simp only [resonantCharge, Fin.lastCases_castSucc]
    exact shifted_charge_row (k := k) (ell := ell) (w := w) i

theorem resonant_target_old_second {w ell k m : ℕ}
    (hell : 1 ≤ ell) (hm : m = 2 ^ ell) (hw : 1 ≤ w)
    (hdiv : w ∣ m - 1) (hlarge : 3 * w + 1 ≤ m)
    (hroom : w ≤ 2 ^ (k - 1) - 1)
    (hk : 2 ≤ k) (hkl : ell ≤ k) (j : Fin (k + 1)) :
    resonantTargetSecond k ell w (liftOldLabel j) =
      (m : ℤ) * actualSource (k + 1) (2 * w) j -
        (m - 1 : ℕ) * resonantCharge k w j -
        (w : ℤ) * (m - 1 : ℕ) * resonantEar k j := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have hs := (resonant_source_rows (k := k + ell) (seed := w) (by omega)
        (by
          have hp : 2 ^ (k - 1) ≤ 2 ^ (k + ell - 1) :=
            Nat.pow_le_pow_right (by decide) (by omega)
          have hB : 0 < 2 ^ (k - 1) := by positivity
          omega) (liftOldLabel (k := k) (ell := ell) (Fin.last k))).2.2
    have hf := resonant_target_old_first hell hm hw hdiv hlarge hroom hk hkl (Fin.last k)
    have hf' : resonantFirst (k + ell) w (liftOldLabel (k := k) (ell := ell) (Fin.last k)) =
        (m : ℤ) * resonantFirst k w (Fin.last k) -
          (m - 1 : ℕ) * resonantCharge k w (Fin.last k) := by
      simpa only [resonantTargetFirst, resonantFirst] using hf
    have hc := resonant_target_old_charge (w := w) (ell := ell) (k := k) (m := m)
      (Fin.last k)
    have he : resonantEar (k + ell) (liftOldLabel (k := k) (ell := ell) (Fin.last k)) =
        resonantEar k (Fin.last k) := by simp [resonantEar, liftOldLabel]
    have hb := (resonant_source_rows (k := k) (seed := w) hk hroom (Fin.last k)).2.2
    rw [hf', hc, he] at hs
    calc
      resonantTargetSecond k ell w (liftOldLabel (k := k) (ell := ell) (Fin.last k)) =
          2 * (m * resonantFirst k w (Fin.last k) -
            (m - 1 : ℕ) * resonantCharge k w (Fin.last k)) + w := by
        simpa [resonantTargetSecond, resonantCharge, resonantEar] using hs
      _ = (m : ℤ) * actualSource (k + 1) (2 * w) (Fin.last k) -
          (m - 1 : ℕ) * resonantCharge k w (Fin.last k) -
          (w : ℤ) * (m - 1 : ℕ) * resonantEar k (Fin.last k) := by
        rw [hb]
        simp [resonantCharge, resonantEar]
        norm_num [Nat.cast_sub (by omega : 1 ≤ m)]
        ring
  · have hs := (resonant_source_rows (k := k + ell) (seed := w) (by omega)
      (by
        have hp : 2 ^ (k - 1) ≤ 2 ^ (k + ell - 1) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        have hB : 0 < 2 ^ (k - 1) := by positivity
        omega) (liftOldLabel (k := k) (ell := ell) i.castSucc)).2.2
    have hf := resonant_target_old_first hell hm hw hdiv hlarge hroom hk hkl i.castSucc
    have hf' : resonantFirst (k + ell) w (liftOldLabel (k := k) (ell := ell) i.castSucc) =
        (m : ℤ) * resonantFirst k w i.castSucc -
          (m - 1 : ℕ) * resonantCharge k w i.castSucc := by
      simpa only [resonantTargetFirst, resonantFirst] using hf
    have hc := resonant_target_old_charge (w := w) (ell := ell) (k := k) (m := m)
      i.castSucc
    have he : resonantEar (k + ell) (liftOldLabel (k := k) (ell := ell) i.castSucc) =
        resonantEar k i.castSucc := by simp [resonantEar, liftOldLabel]
    have hb := (resonant_source_rows (k := k) (seed := w) hk hroom i.castSucc).2.2
    rw [hf', hc, he] at hs
    calc
      resonantTargetSecond k ell w (liftOldLabel (k := k) (ell := ell) i.castSucc) =
          2 * (m * resonantFirst k w i.castSucc -
            (m - 1 : ℕ) * resonantCharge k w i.castSucc) -
            resonantCharge k w i.castSucc := by
        have hi : i.val ≠ k := by omega
        simpa [resonantTargetSecond, resonantCharge, resonantEar, hi] using hs
      _ = (m : ℤ) * actualSource (k + 1) (2 * w) i.castSucc -
          (m - 1 : ℕ) * resonantCharge k w i.castSucc -
          (w : ℤ) * (m - 1 : ℕ) * resonantEar k i.castSucc := by
        rw [hb]
        have hi : i.val ≠ k := by omega
        simp [resonantCharge, resonantEar, hi]
        norm_num [Nat.cast_sub (by omega : 1 ≤ m)]
        ring

theorem resonant_target_new_second {w ell k : ℕ}
    (hell : 1 ≤ ell) (hroom : w ≤ 2 ^ (k - 1) - 1) (hk : 2 ≤ k)
    (i : Fin ell) :
    resonantTargetSecond k ell w (liftNewLabel i) =
      (2 * w : ℤ) * 2 ^ i.val := by
  exact resonant_low_second_row hell hroom hk i

theorem resonant_target_old_rows {w ell k m : ℕ}
    (hell : 1 ≤ ell) (hm : m = 2 ^ ell) (hw : 1 ≤ w)
    (hdiv : w ∣ m - 1) (hlarge : 3 * w + 1 ≤ m)
    (hroom : w ≤ 2 ^ (k - 1) - 1)
    (hk : 2 ≤ k) (hkl : ell ≤ k) (j : Fin (k + 1)) :
    resonantTargetFirst k ell w (liftOldLabel j) =
      (m : ℤ) * resonantFirst k w j - (m - 1 : ℕ) * resonantCharge k w j ∧
    resonantTargetSecond k ell w (liftOldLabel j) =
      (m : ℤ) * actualSource (k + 1) (2 * w) j -
        (m - 1 : ℕ) * resonantCharge k w j -
        (w : ℤ) * (m - 1 : ℕ) * resonantEar k j := by
  exact ⟨resonant_target_old_first hell hm hw hdiv hlarge hroom hk hkl j,
    resonant_target_old_second hell hm hw hdiv hlarge hroom hk hkl j⟩

theorem resonant_target_new_rows {w ell k m : ℕ}
    (hell : 1 ≤ ell) (hm : m = 2 ^ ell) (hroom : w ≤ 2 ^ (k - 1) - 1)
    (hk : 2 ≤ k) (i : Fin ell) :
    resonantTargetFirst k ell w (liftNewLabel i) = (w : ℤ) * 2 ^ i.val ∧
    resonantTargetSecond k ell w (liftNewLabel i) = (2 * w : ℤ) * 2 ^ i.val := by
  exact ⟨resonant_target_new_first hell hm hroom hk i,
    resonant_target_new_second hell hroom hk i⟩

end D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion
