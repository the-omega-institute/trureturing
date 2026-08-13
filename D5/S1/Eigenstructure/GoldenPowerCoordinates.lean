/- GID: D5/S1/Eigenstructure/GoldenPowerCoordinates
   generality: I
   mirror-B: D5/B/S1/Eigenstructure/GoldenPowerCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Powers two and three give unique nonnegative coordinates; only this clause is closed. -/

import D5.S1.Scale.Embedding

namespace D5.S1.Eigenstructure.GoldenPowerCoordinates

open D5.S0.Carrier D5.S1.Scale

/-- Nonnegative coefficients of the second and third golden powers are unique. -/
theorem golden_power_coordinates_unique {a b c d : ℕ}
    (h : (a : ℝ) * Real.goldenRatio ^ 2 + (b : ℝ) * Real.goldenRatio ^ 3 =
      (c : ℝ) * Real.goldenRatio ^ 2 + (d : ℝ) * Real.goldenRatio ^ 3) :
    a = c ∧ b = d := by
  have hcarrier :
      (a : GoldenInt) * phi ^ 2 + (b : GoldenInt) * phi ^ 3 =
        (c : GoldenInt) * phi ^ 2 + (d : GoldenInt) * phi ^ 3 := by
    apply embedding_injective
    simpa only [map_add, map_mul, map_pow, map_natCast, embedding_phi] using h
  have hfirst := congrArg GoldenInt.a hcarrier
  have hsecond := congrArg GoldenInt.b hcarrier
  simp [pow_succ, phi] at hfirst hsecond
  omega

end D5.S1.Eigenstructure.GoldenPowerCoordinates
