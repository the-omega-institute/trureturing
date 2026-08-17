/- GID: D5/S1/Eigenstructure/GoldenFiberCoordinates
   generality: I
   mirror-B: D5/B/S1/Eigenstructure/GoldenFiberCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact Beatty floor coordinates for the two golden fiber readings. -/

import Mathlib
import D5.S1.Deficit.ZeckendorfDisplacementReading

namespace D5.S1.Eigenstructure.GoldenFiberCoordinates

open D5.S1.Deficit.ZeckendorfDisplacementReading

noncomputable def fiberCoordinateA (v : ℕ) : ℤ :=
  2 * (displacementDecode v : ℤ) - 3 * (v : ℤ)

noncomputable def fiberCoordinateB (v : ℕ) : ℤ :=
  2 * (v : ℤ) - (displacementDecode v : ℤ)

theorem golden_fiber_coordinates (v : ℕ) (hv : 1 ≤ v) :
    fiberCoordinateA v =
        ⌊((v : ℝ) + 1) / Real.goldenRatio⌋ -
          ⌊((v : ℝ) + 1) / Real.goldenRatio ^ 2⌋ ∧
      fiberCoordinateB v = ⌊((v : ℝ) + 1) / Real.goldenRatio ^ 2⌋ ∧
      fiberCoordinateA v + fiberCoordinateB v =
        ⌊((v : ℝ) + 1) / Real.goldenRatio⌋ := by
  let x : ℝ := ((v : ℝ) + 1) * Real.goldenRatio
  have hphi_inv : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hphi_inv_sq : (Real.goldenRatio ^ 2)⁻¹ = 2 - Real.goldenRatio := by
    rw [← inv_pow, hphi_inv]
    nlinarith [Real.goldenRatio_sq]
  have hdiv_one : ((v : ℝ) + 1) / Real.goldenRatio = x - ((v : ℝ) + 1) := by
    dsimp [x]
    rw [div_eq_mul_inv, hphi_inv]
    ring
  have hdiv_two : ((v : ℝ) + 1) / Real.goldenRatio ^ 2 =
      2 * ((v : ℝ) + 1) - x := by
    dsimp [x]
    rw [div_eq_mul_inv, hphi_inv_sq]
    ring
  have hcast : ((v : ℝ) + 1) = ((v + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  have hfloor_one :
      ⌊((v : ℝ) + 1) / Real.goldenRatio⌋ =
        ⌊x⌋ - (v + 1 : ℤ) := by
    rw [hdiv_one, hcast, Int.floor_sub_natCast]
    push_cast
    rfl
  have hirr : Irrational x := by
    dsimp [x]
    rw [hcast]
    exact Real.goldenRatio_irrational.natCast_mul (by omega)
  have hfloor_strict : (⌊x⌋ : ℝ) < x := by
    exact lt_of_le_of_ne (Int.floor_le x) (Ne.symm (hirr.ne_int ⌊x⌋))
  have hfloor_complement :
      ⌊2 * ((v : ℝ) + 1) - x⌋ =
        (2 * (v + 1) : ℤ) - ⌊x⌋ - 1 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> push_cast <;> linarith [Int.lt_floor_add_one x,
      Int.floor_le x, hfloor_strict]
  have hfloor_two :
      ⌊((v : ℝ) + 1) / Real.goldenRatio ^ 2⌋ =
        (2 * (v + 1) : ℤ) - ⌊x⌋ - 1 := by
    rw [hdiv_two]
    exact hfloor_complement
  have hdecode := displacement_decode_eq_beatty_floor v
  have hdecode_x : (displacementDecode v : ℤ) = ⌊x⌋ - 1 := by
    simpa [x] using hdecode
  constructor
  · rw [fiberCoordinateA, hdecode_x, hfloor_one, hfloor_two]
    omega
  constructor
  · rw [fiberCoordinateB, hdecode_x, hfloor_two]
    omega
  · rw [fiberCoordinateA, fiberCoordinateB, hdecode_x, hfloor_one]
    ring

#print axioms golden_fiber_coordinates

end D5.S1.Eigenstructure.GoldenFiberCoordinates
