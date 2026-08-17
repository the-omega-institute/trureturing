/- GID: D5/S1/Eigenstructure/GoldenExponentRays
   generality: I
   mirror-B: D5/B/S1/Eigenstructure/GoldenExponentRays
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Rational golden-exponent rays are exactly rational coordinate rays. -/

import D5.S1.Eigenstructure.GoldenPowerCoordinates
import Mathlib.Tactic.Ring

namespace D5.S1.Eigenstructure.GoldenExponentRays

open D5.S1.Eigenstructure.GoldenPowerCoordinates

/-- The real value attached to the exponent vector `(a, b)` in the basis `(phi^2, phi^3)`. -/
noncomputable def goldenExponentValue (a b : ℕ) : ℝ :=
  (a : ℝ) * Real.goldenRatio ^ 2 + (b : ℝ) * Real.goldenRatio ^ 3

/-- Two nonnegative golden-exponent vectors lie on the same rational ray exactly when their
real golden-power values do. A positive `q` is the denominator of the common scale `p / q`. -/
theorem golden_exponent_rational_ray_iff (a b c d : ℕ) :
    (∃ p q : ℕ, 0 < q ∧
      (q : ℝ) * goldenExponentValue a b = (p : ℝ) * goldenExponentValue c d) ↔
      ∃ p q : ℕ, 0 < q ∧ q * a = p * c ∧ q * b = p * d := by
  constructor
  · rintro ⟨p, q, hq, hvalue⟩
    have hcoordinates := golden_power_coordinates_unique
      (a := q * a) (b := q * b) (c := p * c) (d := p * d) (by
        calc
          ((q * a : ℕ) : ℝ) * Real.goldenRatio ^ 2 +
              ((q * b : ℕ) : ℝ) * Real.goldenRatio ^ 3 =
              (q : ℝ) * goldenExponentValue a b := by
                push_cast
                simp only [goldenExponentValue]
                ring
          _ = (p : ℝ) * goldenExponentValue c d := hvalue
          _ = ((p * c : ℕ) : ℝ) * Real.goldenRatio ^ 2 +
              ((p * d : ℕ) : ℝ) * Real.goldenRatio ^ 3 := by
                push_cast
                simp only [goldenExponentValue]
                ring)
    exact ⟨p, q, hq, hcoordinates.1, hcoordinates.2⟩
  · rintro ⟨p, q, hq, hac, hbd⟩
    refine ⟨p, q, hq, ?_⟩
    calc
      (q : ℝ) * goldenExponentValue a b =
          ((q * a : ℕ) : ℝ) * Real.goldenRatio ^ 2 +
            ((q * b : ℕ) : ℝ) * Real.goldenRatio ^ 3 := by
              push_cast
              simp only [goldenExponentValue]
              ring
      _ = ((p * c : ℕ) : ℝ) * Real.goldenRatio ^ 2 +
          ((p * d : ℕ) : ℝ) * Real.goldenRatio ^ 3 := by rw [hac, hbd]
      _ = (p : ℝ) * goldenExponentValue c d := by
            push_cast
            simp only [goldenExponentValue]
            ring

#print axioms golden_exponent_rational_ray_iff

end D5.S1.Eigenstructure.GoldenExponentRays
