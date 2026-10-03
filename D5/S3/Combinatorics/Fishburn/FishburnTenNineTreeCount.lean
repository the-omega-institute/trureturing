/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenNineTreeCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenNineTreeCount
   mirror-E: none(waiver:four-state-descendant-enumeration)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.WellKnown, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Counting the four labelled descendant trees yields their root series equation. -/

import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenNineTreeCount

open Finset PowerSeries

def descendants : ℕ → ℕ → Fin 4 → ℕ
  | 0, _, _ => 1
  | height + 1, initial, kind =>
    let smaller := ∑ earlier ∈ range initial, descendants height earlier 1
    smaller + if kind = 0 then descendants height (initial + 1) 0
      else if kind = 1 then descendants height initial 1 + descendants height initial 2
      else if kind = 2 then descendants height initial 3 + descendants height initial 2
      else descendants height initial 3

theorem abstract_tree_enumeration :
    (1 - 4 * X + 5 * X ^ 2 - 3 * X ^ 3 : PowerSeries ℤ) *
      mk (fun height => (descendants height 0 0 : ℤ)) = (1 - X) ^ 3 := by
  let series : ℕ → Fin 4 → PowerSeries ℤ :=
    fun initial kind => mk (fun height => (descendants height initial kind : ℤ))
  let total : ℕ → PowerSeries ℤ :=
    fun initial => ∑ earlier ∈ range initial, series earlier 1
  let source : ℕ → PowerSeries ℤ := fun initial => 1 + X * total initial
  let denominator : PowerSeries ℤ := (1 - X) ^ 3
  let numerator : PowerSeries ℤ := 1 - X + X ^ 2
  have hrec (initial : ℕ) (kind : Fin 4) :
      series initial kind = source initial + X *
        (if kind = 0 then series (initial + 1) 0
          else if kind = 1 then series initial 1 + series initial 2
          else if kind = 2 then series initial 3 + series initial 2
          else series initial 3) := by
    ext height
    cases height with
    | zero => fin_cases kind <;> simp [series, source, descendants]
    | succ height =>
      fin_cases kind <;>
        simp [series, source, total, descendants, coeff_succ_X_mul, Nat.cast_sum]
  have hblock (initial : ℕ) :
      denominator * series initial 1 = numerator * source initial := by
    have hb := hrec initial 1
    have hc := hrec initial 2
    have hz := hrec initial 3
    simp only [show (1 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 0 by decide,
      show (2 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 0 by decide,
      show (3 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 2 by decide,
      if_true, if_false] at hb hc hz
    dsimp only [denominator, numerator]
    linear_combination (1 - X) ^ 2 * hb + X * (1 - X) * hc + X ^ 2 * hz
  have hsource (initial : ℕ) : source (initial + 1) =
      source initial + X * series initial 1 := by
    dsimp only [source, total]
    rw [sum_range_succ]
    ring
  have hsourceScaled (initial : ℕ) : denominator * source (initial + 1) =
      (denominator + X * numerator) * source initial := by
    rw [hsource]
    calc
      denominator * (source initial + X * series initial 1) =
          denominator * source initial + X * (denominator * series initial 1) := by ring
      _ = (denominator + X * numerator) * source initial := by
        rw [hblock]
        ring
  have hshiftCoefficient (height : ℕ) : ∀ initial,
      coeff height (denominator * series (initial + 1) 0) =
        coeff height ((denominator + X * numerator) * series initial 0) := by
    induction height with
    | zero =>
      intro initial
      simp [denominator, numerator, series, descendants]
    | succ height ih =>
      intro initial
      have hi := hrec initial 0
      have hiNext := hrec (initial + 1) 0
      norm_num only [Fin.reduceEq, if_true] at hi hiNext
      have hcontract : denominator * series (initial + 1) 0 -
          (denominator + X * numerator) * series initial 0 =
          X * (denominator * series (initial + 1 + 1) 0 -
            (denominator + X * numerator) * series (initial + 1) 0) := by
        calc
          _ = denominator * source (initial + 1) -
              (denominator + X * numerator) * source initial +
              X * (denominator * series (initial + 1 + 1) 0 -
                (denominator + X * numerator) * series (initial + 1) 0) := by
            rw [hi, hiNext]
            ring
          _ = _ := by rw [hsourceScaled]; ring
      have hcoeff := congrArg (coeff (height + 1)) hcontract
      simp only [map_sub, coeff_succ_X_mul] at hcoeff
      rw [ih (initial + 1), sub_self] at hcoeff
      exact sub_eq_zero.mp hcoeff
  have hshift (initial : ℕ) : denominator * series (initial + 1) 0 =
      (denominator + X * numerator) * series initial 0 := by
    ext height
    exact hshiftCoefficient height initial
  have hroot : denominator * series 0 0 =
      denominator + X * (denominator + X * numerator) * series 0 0 := by
    have hi := hrec 0 0
    norm_num only [Fin.reduceEq, if_true, zero_add] at hi
    have hz : source 0 = 1 := by simp [source, total]
    calc
      denominator * series 0 0 = denominator * (source 0 + X * series 1 0) := by
        exact congrArg (denominator * ·) hi
      _ = denominator + X * (denominator * series 1 0) := by rw [hz]; ring
      _ = _ := by rw [hshift 0]; ring
  change (1 - 4 * X + 5 * X ^ 2 - 3 * X ^ 3) * series 0 0 = denominator
  dsimp only [denominator, numerator] at hroot ⊢
  linear_combination hroot

end D5.S3.Combinatorics.Fishburn.FishburnTenNineTreeCount
