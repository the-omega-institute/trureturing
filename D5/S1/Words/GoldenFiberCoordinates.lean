/- GID: D5/S1/Words/GoldenFiberCoordinates
   generality: I
   mirror-B: D5/B/S1/Words/GoldenFiberCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden fiber coordinates are explicit differences of two Beatty readings. -/

import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Algebra.Order.Floor.Ring

/- Provenance: new floor-algebra proof over pinned mathlib's golden-ratio
   identities (`Real.inv_goldenRatio`, `Real.goldenRatio_sq`,
   `Real.goldenRatio_irrational`) and integer floor/ceiling laws. -/

namespace D5.S1.Words.GoldenFiberCoordinates

open Real

/-- The shifted golden Beatty reading used to decode a fiber index. -/
noncomputable def goldenShift (v : ℕ) : ℤ :=
  ⌊(((v : ℝ) + 1) * goldenRatio)⌋ - 1

/-- The first integral fiber coordinate. -/
noncomputable def fiberA (v : ℕ) : ℤ :=
  2 * goldenShift v - 3 * v

/-- The second integral fiber coordinate. -/
noncomputable def fiberB (v : ℕ) : ℤ :=
  2 * v - goldenShift v

private theorem inv_goldenRatio_eq : goldenRatio⁻¹ = goldenRatio - 1 := by
  rw [inv_goldenRatio]
  linarith [goldenRatio_add_goldenConj]

private theorem inv_goldenRatio_sq_eq : (goldenRatio ^ 2)⁻¹ = 2 - goldenRatio := by
  rw [← inv_pow, inv_goldenRatio_eq]
  nlinarith [goldenRatio_sq]

private theorem floor_div_goldenRatio (n : ℕ) :
    ⌊(n : ℝ) / goldenRatio⌋ = ⌊(n : ℝ) * goldenRatio⌋ - n := by
  have harg : (n : ℝ) / goldenRatio = (n : ℝ) * goldenRatio - n := by
    rw [div_eq_mul_inv, inv_goldenRatio_eq]
    ring
  rw [harg, Int.floor_sub_natCast]

private theorem floor_div_goldenRatio_sq (n : ℕ) (hn : n ≠ 0) :
    ⌊(n : ℝ) / goldenRatio ^ 2⌋ =
      2 * (n : ℤ) - ⌊(n : ℝ) * goldenRatio⌋ - 1 := by
  have harg : (n : ℝ) / goldenRatio ^ 2 =
      -(n : ℝ) * goldenRatio + (2 * (n : ℤ) : ℤ) := by
    rw [div_eq_mul_inv, inv_goldenRatio_sq_eq]
    norm_num
    ring
  have hirrational : Irrational ((n : ℝ) * goldenRatio) :=
    goldenRatio_irrational.natCast_mul hn
  have hnotmem : (n : ℝ) * goldenRatio ∉ Set.range ((↑) : ℤ → ℝ) := by
    rintro ⟨z, hz⟩
    exact hirrational.ne_int z hz.symm
  have hceil : ⌈(n : ℝ) * goldenRatio⌉ = ⌊(n : ℝ) * goldenRatio⌋ + 1 :=
    (Int.ceil_eq_floor_add_one_iff_notMem _).2 hnotmem
  rw [harg, Int.floor_add_intCast]
  have hneg : -(n : ℝ) * goldenRatio = -((n : ℝ) * goldenRatio) := by ring
  rw [hneg, Int.floor_neg, hceil]
  ring

/-- The two fiber coordinates, and hence their sum, are consecutive golden
Beatty readings. -/
theorem golden_fiber_coordinates (v : ℕ) (hv : 1 ≤ v) :
    fiberA v =
        ⌊((v : ℝ) + 1) / goldenRatio⌋ -
          ⌊((v : ℝ) + 1) / goldenRatio ^ 2⌋ ∧
      fiberB v = ⌊((v : ℝ) + 1) / goldenRatio ^ 2⌋ ∧
      fiberA v + fiberB v = ⌊((v : ℝ) + 1) / goldenRatio⌋ := by
  let n := v + 1
  have hn : n ≠ 0 := by omega
  have hnreal : (n : ℝ) = (v : ℝ) + 1 := by
    simp [n]
  have hnint : (n : ℤ) = (v : ℤ) + 1 := by
    simp [n]
  have hfirst := floor_div_goldenRatio n
  have hsecond := floor_div_goldenRatio_sq n hn
  rw [hnreal] at hfirst hsecond
  constructor
  · rw [fiberA, goldenShift, hfirst, hsecond, hnint]
    ring
  constructor
  · rw [fiberB, goldenShift, hsecond, hnint]
    ring
  · rw [fiberA, fiberB, goldenShift, hfirst, hnint]
    ring

end D5.S1.Words.GoldenFiberCoordinates
