/- GID: D5/S3/Combinatorics/Circle/FourNegative/ResonantUniversalInsertionWord
   generality: I
   mirror-B: none(waiver:universal-resonant-source)
   mirror-E: none(waiver:dependent-physical-source-audit)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Generic insertion words, literal deletion, and injectivity. -/
import D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertionArithmetic
import D5.S3.Combinatorics.Circle.RunFirstEarTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion

open SourceWidth PeriodicShortening PeriodicShorteningArithmetic
open RunFirstEarTransport

def liftOldLabel {k ell : ℕ} (j : Fin (k + 1)) : Fin (k + ell + 1) :=
  ⟨j.val + ell, by omega⟩

def liftNewLabel {k ell : ℕ} (i : Fin ell) : Fin (k + ell + 1) :=
  ⟨i.val, by omega⟩

def deleteLow {k ell : ℕ} (word : List (Fin (k + ell + 1))) : List (Fin (k + 1)) :=
  word.filterMap (fun j => if h : ell ≤ j.val then
    some ⟨j.val - ell, by omega⟩ else none)

def resonantBlock {k ell : ℕ} (orientation : Fin ell → Bool)
    (j : Fin (k + 1)) : List (Fin (k + ell + 1)) :=
  if hj : j.val < ell then
    let i : Fin ell := ⟨j.val, hj⟩
    if orientation i then
      [liftOldLabel j, liftNewLabel i]
    else
      [liftNewLabel i, liftOldLabel j]
  else
    [liftOldLabel j]

def resonantLiftWord {k ell : ℕ} (word : List (Fin (k + 1)))
    (orientation : Fin ell → Bool) : List (Fin (k + ell + 1)) :=
  word.flatMap (resonantBlock orientation)

theorem deleteLow_oldLabel {k ell : ℕ} (hell : 1 ≤ ell) (j : Fin (k + 1)) :
    deleteLow (k := k) (ell := ell) [liftOldLabel (k := k) (ell := ell) j] = [j] := by
  simp [deleteLow, liftOldLabel, hell]

theorem deleteLow_newLabel {k ell : ℕ} (hell : 1 ≤ ell) (i : Fin ell) :
    deleteLow (k := k) (ell := ell) [liftNewLabel (k := k) (ell := ell) i] = [] := by
  simp [deleteLow, liftNewLabel, hell]

theorem deleteLow_block {k ell : ℕ} (hell : 1 ≤ ell)
    (orientation : Fin ell → Bool) (j : Fin (k + 1)) :
    deleteLow (resonantBlock orientation j) = [j] := by
  by_cases hj : j.val < ell
  · let i : Fin ell := ⟨j.val, hj⟩
    by_cases ho : orientation i
    · simp [resonantBlock, deleteLow, liftOldLabel, liftNewLabel, hj, ho, i]
    · simp [resonantBlock, deleteLow, liftOldLabel, liftNewLabel, hj, ho, i]
  · simp only [resonantBlock, dif_neg hj]
    simp [deleteLow, liftOldLabel, hj]

theorem deleteLow_liftWord {k ell : ℕ} (hell : 1 ≤ ell)
    (word : List (Fin (k + 1))) (orientation : Fin ell → Bool) :
    deleteLow (resonantLiftWord word orientation) = word := by
  induction word with
  | nil => simp [resonantLiftWord, deleteLow]
  | cons j js ih =>
    change deleteLow (resonantBlock orientation j ++
      resonantLiftWord js orientation) = j :: js
    rw [show deleteLow (resonantBlock orientation j ++
        resonantLiftWord js orientation) =
        deleteLow (resonantBlock orientation j) ++
          deleteLow (resonantLiftWord js orientation) by
      unfold deleteLow
      rw [List.filterMap_append]]
    rw [deleteLow_block hell orientation j]
    simpa using congrArg (fun l => j :: l) ih

theorem resonantLiftWord_injective {k ell : ℕ} (hell : 1 ≤ ell)
    (orientation : Fin ell → Bool) :
    Function.Injective (fun word : List (Fin (k + 1)) =>
      resonantLiftWord word orientation) := by
  intro a b hab
  have h := congrArg (deleteLow (k := k) (ell := ell)) hab
  simpa [deleteLow_liftWord hell a orientation,
    deleteLow_liftWord hell b orientation] using h

end D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion
