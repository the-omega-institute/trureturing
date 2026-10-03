/- GID: D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductContinuants
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NarayanaStrip/CiglerStripProductContinuants
   mirror-E: none(waiver:weighted-strip-continuant-representation)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Inverse]
   utility: none
   digest: Arbitrary-weight strip continuants give the bounded series with a unit denominator. -/

import D5.S3.Combinatorics.NarayanaStrip.CiglerStripProductDefs
import Mathlib.RingTheory.PowerSeries.Inverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.NarayanaStrip.CiglerStripProductAlgebra

variable {R : Type*} [CommRing R]

def cont (a : ℕ → R) (r0 r1 : R) : ℕ → R
  | 0 => r0
  | 1 => r1
  | n + 2 => cont a r0 r1 (n + 1) - a n * cont a r0 r1 n

end D5.S3.Combinatorics.NarayanaStrip.CiglerStripProductAlgebra

namespace D5.S3.Combinatorics.NarayanaStrip.CiglerStripProductSeries

open CiglerStripExpansionDefs CiglerStripProductAlgebra

theorem continuant_representation (weights : ℕ → Polynomial ℤ) (height : ℕ)
    (recursion : ∀ (weights : ℕ → Polynomial ℤ) (bound size : ℕ),
      stripSum weights (bound + 1) (size + 1) =
        weights 0 * ∑ index ∈ Finset.range (size + 1),
          stripSum (fun height => weights (height + 1)) bound index *
            stripSum weights (bound + 1) (size - index)) :
    let a := fun k => PowerSeries.C (weights k) * PowerSeries.X
    IsUnit (cont a 1 1 (height + 1)) ∧
      cont a 1 1 (height + 1) * PowerSeries.mk (stripSum weights height) =
        cont a 0 1 (height + 1) := by
  classical
  let a (sequence : ℕ → Polynomial ℤ) (k : ℕ) : PowerSeries (Polynomial ℤ) :=
    PowerSeries.C (sequence k) * PowerSeries.X
  let E (sequence : ℕ → Polynomial ℤ) (bound : ℕ) :=
    PowerSeries.mk (stripSum sequence bound)
  have emptyCoeff (sequence : ℕ → Polynomial ℤ) (bound : ℕ) :
      stripSum sequence bound 0 = 1 := by
    simp [stripSum, IsStripDyck, heightAfter, weight]
  have emptyPath (steps : List Bool) (legal : IsStripDyck 0 steps) : steps = [] := by
    cases steps with
    | nil => rfl
    | cons first rest =>
        have firstHeight := legal.1 1 (by simp)
        cases first <;> norm_num [heightAfter] at firstHeight
  have positiveCoeff (sequence : ℕ → Polynomial ℤ) (size : ℕ) :
      stripSum sequence 0 (size + 1) = 0 := by
    unfold stripSum
    apply Finset.sum_eq_zero
    intro steps _
    apply if_neg
    intro legal
    have empty := emptyPath (List.ofFn steps) legal
    have length := congrArg List.length empty
    simp at length
  have heightZero (sequence : ℕ → Polynomial ℤ) : E sequence 0 = 1 := by
    apply PowerSeries.ext
    intro size
    cases size with
    | zero => simp [E, emptyCoeff]
    | succ size => simp [E, positiveCoeff]
  have firstReturn (sequence : ℕ → Polynomial ℤ) (bound : ℕ) :
      E sequence (bound + 1) =
        1 + a sequence 0 *
          (E (fun k => sequence (k + 1)) bound * E sequence (bound + 1)) := by
    apply PowerSeries.ext
    intro size
    cases size with
    | zero =>
        simp [E, a, emptyCoeff, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    | succ size =>
        rw [show a sequence 0 *
            (E (fun k => sequence (k + 1)) bound * E sequence (bound + 1)) =
          PowerSeries.C (sequence 0) *
            (PowerSeries.X *
              (E (fun k => sequence (k + 1)) bound * E sequence (bound + 1))) by
                dsimp only [a]
                ring]
        simp only [map_add, PowerSeries.coeff_one, Nat.succ_ne_zero, if_false,
          zero_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
        rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_eq_map, Finset.sum_map]
        simp only [E, PowerSeries.coeff_mk]
        change stripSum sequence (bound + 1) (size + 1) =
          sequence 0 * ∑ index ∈ Finset.range (size + 1),
            stripSum (fun k => sequence (k + 1)) bound index *
              stripSum sequence (bound + 1) (size - index)
        exact recursion sequence bound size
  have shift (coefficients : ℕ → PowerSeries (Polynomial ℤ)) : ∀ size : ℕ,
      cont coefficients 0 1 (size + 1) =
          cont (fun k => coefficients (k + 1)) 1 1 size ∧
        cont coefficients 1 1 (size + 1) =
          cont (fun k => coefficients (k + 1)) 1 1 size -
            coefficients 0 * cont (fun k => coefficients (k + 1)) 0 1 size := by
    intro size
    induction size using Nat.twoStepInduction with
    | zero => simp [cont]
    | one => simp [cont]
    | more size earlier later =>
        rw [show size + 2 + 1 = (size + 1) + 2 by omega]
        rw [cont.eq_3 coefficients 0 1 (size + 1),
          cont.eq_3 coefficients 1 1 (size + 1),
          cont.eq_3 (fun k => coefficients (k + 1)) 1 1 size,
          cont.eq_3 (fun k => coefficients (k + 1)) 0 1 size,
          later.1, earlier.1, later.2, earlier.2]
        constructor
        · rfl
        · ring
  have constant (sequence : ℕ → Polynomial ℤ) : ∀ size : ℕ,
      PowerSeries.constantCoeff (cont (a sequence) 1 1 size) = 1 := by
    intro size
    induction size using Nat.twoStepInduction with
    | zero => simp [cont]
    | one => simp [cont]
    | more size earlier later =>
        rw [cont, map_sub, map_mul, earlier, later]
        simp [a]
  have unit (sequence : ℕ → Polynomial ℤ) (size : ℕ) :
      IsUnit (cont (a sequence) 1 1 size) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [constant]
    exact isUnit_one
  have representation : ∀ bound : ℕ, ∀ sequence : ℕ → Polynomial ℤ,
      cont (a sequence) 1 1 (bound + 1) * E sequence bound =
        cont (a sequence) 0 1 (bound + 1) := by
    intro bound
    induction bound with
    | zero =>
        intro sequence
        rw [heightZero]
        simp [cont]
    | succ bound ih =>
        intro sequence
        let tail := fun k => sequence (k + 1)
        let denominator := cont (a tail) 1 1 (bound + 1)
        let numerator := cont (a tail) 0 1 (bound + 1)
        have tailRepresentation : denominator * E tail bound = numerator := ih tail
        have endpoints := shift (a sequence) (bound + 1)
        change cont (a sequence) 0 1 (bound + 2) = denominator ∧
          cont (a sequence) 1 1 (bound + 2) =
            denominator - a sequence 0 * numerator at endpoints
        change cont (a sequence) 1 1 (bound + 2) * E sequence (bound + 1) =
          cont (a sequence) 0 1 (bound + 2)
        rw [endpoints.1, endpoints.2]
        have balance : E sequence (bound + 1) -
            a sequence 0 * (E tail bound * E sequence (bound + 1)) = 1 :=
          sub_eq_iff_eq_add.mpr (firstReturn sequence bound)
        calc
          (denominator - a sequence 0 * numerator) * E sequence (bound + 1) =
              denominator * (E sequence (bound + 1) -
                a sequence 0 * (E tail bound * E sequence (bound + 1))) := by
                  rw [← tailRepresentation]
                  ring
          _ = denominator := by rw [balance, mul_one]
  exact ⟨unit weights (height + 1), representation height weights⟩

end D5.S3.Combinatorics.NarayanaStrip.CiglerStripProductSeries
