/- GID: D5/S1/Words/Mechanical/GoldenFiberPrefixCount
   generality: I
   mirror-B: D5/B/S1/Words/Mechanical/GoldenFiberPrefixCount
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: Positive-indexed golden fiber letters have an exact floor prefix count. -/

import D5.S1.Words.Mechanical.MechanicalGoldenBridge

namespace D5.S1.Words.Mechanical.GoldenFiberPrefixCount

open D5.S1.Words

/-- The positive-indexed golden fiber letter is one plus its golden-word bit. -/
def goldenFiberLetter (m : Nat) : Int :=
  1 + if goldenWord (m - 1) = true then 1 else 0

/-- The first `n` positive-indexed golden fiber letters have the exact floor count. -/
theorem golden_fiber_prefix_count (n : Nat) :
    (∑ k ∈ Finset.range n, goldenFiberLetter (k + 1)) =
      ⌊Real.goldenRatio * ((n + 1 : Nat) : Real)⌋ - 1 := by
  have hslope_nonneg : 0 ≤ goldenMechanicalSlope :=
    inv_nonneg.mpr Real.goldenRatio_pos.le
  have hslope_lt_one : goldenMechanicalSlope < 1 :=
    inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hcount := lowerMechanicalWindowTrueCount_eq_floor
    (rho := 0) hslope_nonneg hslope_lt_one 1 n
  have hslope_floor : ⌊goldenMechanicalSlope⌋ = (0 : Int) :=
    Int.floor_eq_zero_iff.mpr ⟨hslope_nonneg, hslope_lt_one⟩
  have hcount' :
      (lowerMechanicalWindowTrueCount goldenMechanicalSlope 0 1 n : Int) =
        ⌊((n + 1 : Nat) : Real) * Real.goldenRatio⁻¹⌋ := by
    calc
      (lowerMechanicalWindowTrueCount goldenMechanicalSlope 0 1 n : Int) =
          ⌊((1 + n : Nat) : Real) * goldenMechanicalSlope⌋ -
            ⌊goldenMechanicalSlope⌋ := by
        simpa only [zero_add, Nat.cast_one, one_mul] using hcount
      _ = ⌊((1 + n : Nat) : Real) * goldenMechanicalSlope⌋ := by
        rw [hslope_floor, sub_zero]
      _ = ⌊((n + 1 : Nat) : Real) * Real.goldenRatio⁻¹⌋ := by
        rw [goldenMechanicalSlope, Nat.add_comm]
  have hsum :
      (∑ k ∈ Finset.range n, goldenFiberLetter (k + 1)) =
        (n : Int) +
          (lowerMechanicalWindowTrueCount goldenMechanicalSlope 0 1 n : Int) := by
    classical
    have hletter (k : Nat) :
        goldenFiberLetter (k + 1) =
          1 + if lowerMechanicalWord goldenMechanicalSlope 0 (1 + k) = true then 1 else 0 := by
      rw [goldenFiberLetter, Nat.add_sub_cancel, Nat.add_comm, lowerMechanicalWord_golden]
    rw [lowerMechanicalWindowTrueCount, Finset.natCast_card_filter]
    simp_rw [hletter]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, Nat.add_comm]
  rw [hsum, hcount']
  have hgolden : Real.goldenRatio = 1 + Real.goldenRatio⁻¹ := by
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hargument :
      Real.goldenRatio * ((n + 1 : Nat) : Real) =
        (n : Real) + 1 + ((n + 1 : Nat) : Real) * Real.goldenRatio⁻¹ := by
    calc
      Real.goldenRatio * ((n + 1 : Nat) : Real) =
          (1 + Real.goldenRatio⁻¹) * ((n + 1 : Nat) : Real) := by
        exact congrArg (fun x : Real => x * ((n + 1 : Nat) : Real)) hgolden
      _ = (n : Real) + 1 + ((n + 1 : Nat) : Real) * Real.goldenRatio⁻¹ := by
        push_cast
        ring
  rw [hargument]
  have hfloor_shift :
      ⌊(n : Real) + 1 + ((n + 1 : Nat) : Real) * Real.goldenRatio⁻¹⌋ =
        (n : Int) + 1 + ⌊((n + 1 : Nat) : Real) * Real.goldenRatio⁻¹⌋ := by
    rw [show (n : Real) + 1 + ((n + 1 : Nat) : Real) * Real.goldenRatio⁻¹ =
        (((n : Int) + 1 : Int) : Real) +
          ((n + 1 : Nat) : Real) * Real.goldenRatio⁻¹ by push_cast; rfl]
    rw [Int.floor_intCast_add]
  rw [hfloor_shift]
  omega

#print axioms golden_fiber_prefix_count

end D5.S1.Words.Mechanical.GoldenFiberPrefixCount
