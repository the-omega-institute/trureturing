/- GID: D5/S1/Depth/WindowParity
   generality: I
   mirror-B: D5/B/S1/Depth/WindowParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact golden-window capacity and alternating parity laws. -/

import D5.S0.Carrier.GoldenRatio
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.Floor.Ring

namespace D5.S1.Depth.WindowParity

open scoped BigOperators

/-- The four-entry window exhausts zero through three, and its cardinality is
the integer floor of the cubed golden ratio. -/
theorem full_window_and_golden_capacity :
    (∀ value : Nat, value ∈ Finset.range 4 ↔
      value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 3) ∧
    (Finset.range 4).card = 4 ∧
    ⌊Real.goldenRatio ^ 3⌋ = (4 : Int) := by
  refine ⟨?_, by simp, ?_⟩
  · intro value
    simp only [Finset.mem_range]
    omega
  · have hCube : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
      calc
        Real.goldenRatio ^ 3 =
            Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
        _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
          rw [Real.goldenRatio_sq]
        _ = Real.goldenRatio ^ 2 + Real.goldenRatio := by ring
        _ = (Real.goldenRatio + 1) + Real.goldenRatio := by
          rw [Real.goldenRatio_sq]
        _ = 2 * Real.goldenRatio + 1 := by ring
    have hPhiLower : (3 : Real) / 2 < Real.goldenRatio := by
      by_contra hNotLower
      have hUpper : Real.goldenRatio ≤ (3 : Real) / 2 :=
        le_of_not_gt hNotLower
      have hProduct := mul_le_mul_of_nonneg_right hUpper
        (le_of_lt Real.goldenRatio_pos)
      nlinarith [Real.goldenRatio_sq]
    have hLower : (4 : Real) ≤ Real.goldenRatio ^ 3 := by
      rw [hCube]
      linarith
    have hUpper : Real.goldenRatio ^ 3 < (5 : Real) := by
      rw [hCube]
      linarith [Real.goldenRatio_lt_two]
    apply Int.floor_eq_iff.mpr
    constructor
    · simpa using hLower
    · norm_num
      exact hUpper

/-- The finite alternating Witt window terminates at zero exactly in even
length and leaves the alternating remainder one exactly in odd length. -/
theorem witt_window_sum_parity (length : Nat) :
    ((∑ index ∈ Finset.range length, (-1 : Int) ^ index) = 0 ↔ Even length) ∧
    ((∑ index ∈ Finset.range length, (-1 : Int) ^ index) = 1 ↔ Odd length) := by
  simp only [neg_one_geom_sum]
  by_cases hEven : Even length
  · have hNotOdd : ¬ Odd length := Nat.not_odd_iff_even.mpr hEven
    simp [hEven, hNotOdd]
  · have hOdd : Odd length := Nat.not_even_iff_odd.mp hEven
    simp [hEven, hOdd]

end D5.S1.Depth.WindowParity
