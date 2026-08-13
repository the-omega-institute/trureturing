/- GID: D5/S0/Tower/GoldenChampionPoint
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenChampionPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify the closed form of the golden-tower champion point. -/

import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S0.Tower.GoldenChampionPoint

/-- The source's closed-form candidate point has equivalent radical and
negative-power expressions. -/
theorem golden_champion_point_identity :
    (13 / 2 : Real) - 4 * Real.goldenRatio =
        (Real.sqrt 5 - 2) ^ 2 / 2 ∧
      (Real.sqrt 5 - 2) ^ 2 / 2 = Real.goldenRatio ^ (-6 : Int) / 2 := by
  have hsqrt : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hphi_cube : Real.goldenRatio ^ 3 = 2 + Real.sqrt 5 := by
    calc
      Real.goldenRatio ^ 3 = Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
        rw [Real.goldenRatio_sq]
      _ = 2 + Real.sqrt 5 := by
        rw [Real.goldenRatio]
        nlinarith
  have hreciprocal : (Real.sqrt 5 - 2) * (2 + Real.sqrt 5) = 1 := by
    nlinarith
  constructor
  · rw [Real.goldenRatio]
    nlinarith
  · rw [zpow_neg]
    change (Real.sqrt 5 - 2) ^ 2 / 2 =
      (Real.goldenRatio ^ (6 : Nat))⁻¹ / 2
    have hphi_six : Real.goldenRatio ^ 6 = (2 + Real.sqrt 5) ^ 2 := by
      calc
        Real.goldenRatio ^ 6 = (Real.goldenRatio ^ 3) ^ 2 := by ring
        _ = (2 + Real.sqrt 5) ^ 2 := by rw [hphi_cube]
    rw [hphi_six]
    have hden : Not ((2 + Real.sqrt 5) ^ 2 = 0) := by positivity
    field_simp [hden]
    calc
      (Real.sqrt 5 - 2) ^ 2 * (2 + Real.sqrt 5) ^ 2 =
          ((Real.sqrt 5 - 2) * (2 + Real.sqrt 5)) ^ 2 := by ring
      _ = 1 := by rw [hreciprocal]; norm_num

#print axioms golden_champion_point_identity

end D5.S0.Tower.GoldenChampionPoint
