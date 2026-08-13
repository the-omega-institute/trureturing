/- GID: D5/S1/Depth/GoldenPowerRounding
   generality: I
   mirror-B: D5/B/S1/Depth/GoldenPowerRounding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The second and third golden powers have floor-ceiling pairs two-three and four-five. -/

import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Algebra.Order.Floor.Ring

namespace D5.S1.Depth.GoldenPowerRounding

/-- The exact integer rounding pairs for the golden powers that occur in the
fiber-capacity clause. -/
theorem golden_power_floor_ceil_pairs :
    ⌊Real.goldenRatio ^ 3⌋ = (4 : Int) ∧
      ⌈Real.goldenRatio ^ 3⌉ = (5 : Int) ∧
      ⌊Real.goldenRatio ^ 2⌋ = (2 : Int) ∧
      ⌈Real.goldenRatio ^ 2⌉ = (3 : Int) := by
  have hsq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 :=
    Real.goldenRatio_sq
  have hcube : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    calc
      Real.goldenRatio ^ 3 = Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio * (Real.goldenRatio + 1) := by rw [hsq]
      _ = 2 * Real.goldenRatio + 1 := by nlinarith [hsq]
  have hcube_lower : (4 : Real) < Real.goldenRatio ^ 3 := by
    rw [hcube]
    nlinarith [hsq, Real.one_lt_goldenRatio]
  have hcube_upper : Real.goldenRatio ^ 3 < (5 : Real) := by
    rw [hcube]
    linarith [Real.goldenRatio_lt_two]
  have hsq_lower : (2 : Real) < Real.goldenRatio ^ 2 := by
    rw [hsq]
    linarith [Real.one_lt_goldenRatio]
  have hsq_upper : Real.goldenRatio ^ 2 < (3 : Real) := by
    rw [hsq]
    linarith [Real.goldenRatio_lt_two]
  constructor
  · rw [Int.floor_eq_iff]
    constructor
    · exact hcube_lower.le
    · norm_num only [Int.cast_ofNat]
      exact hcube_upper
  constructor
  · rw [Int.ceil_eq_iff]
    constructor
    · norm_num only [Int.cast_ofNat]
      exact hcube_lower
    · exact hcube_upper.le
  constructor
  · rw [Int.floor_eq_iff]
    constructor
    · exact hsq_lower.le
    · norm_num only [Int.cast_ofNat]
      exact hsq_upper
  · rw [Int.ceil_eq_iff]
    constructor
    · norm_num only [Int.cast_ofNat]
      exact hsq_lower
    · exact hsq_upper.le

example : Nonempty Real := inferInstance

example : ⌊(0 : Real)⌋ ≠ (4 : Int) := by norm_num

end D5.S1.Depth.GoldenPowerRounding
