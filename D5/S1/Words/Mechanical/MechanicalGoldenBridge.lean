/- GID: D5/S1/Words/Mechanical/MechanicalGoldenBridge
   generality: I
   mirror-B: D5/B/S1/Words/Mechanical/MechanicalGoldenBridge
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: The frozen golden balance theorem is a shifted lower-mechanical specialization. -/

import D5.S1.Words.GoldenBalance
import D5.S1.Words.Mechanical.MechanicalBalance

namespace D5.S1.Words.Mechanical

open D5.S1.Words

/-- At slope `1 / phi` and intercept zero, the generic letter is the frozen golden letter. -/
theorem lowerMechanicalLetter_golden (n : Nat) :
    lowerMechanicalLetter goldenMechanicalSlope 0 n = goldenMechanicalLetter n := by
  simp [lowerMechanicalLetter, goldenMechanicalLetter]

/-- The generic golden readout has the existing one-index shift of the frozen golden word. -/
theorem lowerMechanicalWord_golden (i : Nat) :
    lowerMechanicalWord goldenMechanicalSlope 0 (i + 1) = goldenWord i := by
  rw [Bool.eq_iff_iff, lowerMechanicalWord_eq_true_iff, lowerMechanicalLetter_golden]
  exact ((goldenWord_char_zeckendorf i).trans (zeckendorf_beatty_bridge i)).symm

/-- Frozen golden window counts are the shifted generic lower-mechanical window counts. -/
theorem goldenWindowTrueCount_eq_lowerMechanicalWindowTrueCount (i n : Nat) :
    goldenWindowTrueCount i n =
      lowerMechanicalWindowTrueCount goldenMechanicalSlope 0 (i + 1) n := by
  classical
  rw [goldenWindowTrueCount, lowerMechanicalWindowTrueCount]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  have hindex : i + 1 + k = i + k + 1 := by omega
  rw [hindex, lowerMechanicalWord_golden]

/-- The frozen golden balance statement, obtained directly from the generic mechanical theorem. -/
theorem goldenWord_balanced_one_mechanical (i j n : Nat) :
    |(goldenWindowTrueCount i n : Int) - (goldenWindowTrueCount j n : Int)| ≤ 1 := by
  rw [goldenWindowTrueCount_eq_lowerMechanicalWindowTrueCount,
    goldenWindowTrueCount_eq_lowerMechanicalWindowTrueCount]
  exact lowerMechanicalWord_balanced_one
    (inv_nonneg.mpr Real.goldenRatio_pos.le)
    (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio) (i + 1) (j + 1) n

private theorem golden_mechanical_prefix_example :
    List.ofFn (fun i : Fin 13 => lowerMechanicalWord goldenMechanicalSlope 0 (i + 1)) =
      [true, false, true, true, false, true, false, true, true, false, true, true, false] := by
  rw [show List.ofFn (fun i : Fin 13 => lowerMechanicalWord goldenMechanicalSlope 0 (i + 1)) =
      List.ofFn (fun i : Fin 13 => goldenWord i) by
    apply List.ofFn_inj.mpr
    funext i
    exact lowerMechanicalWord_golden i]
  decide

#print axioms lowerMechanicalLetter_golden
#print axioms lowerMechanicalWord_golden
#print axioms goldenWindowTrueCount_eq_lowerMechanicalWindowTrueCount
#print axioms goldenWord_balanced_one_mechanical

end D5.S1.Words.Mechanical
