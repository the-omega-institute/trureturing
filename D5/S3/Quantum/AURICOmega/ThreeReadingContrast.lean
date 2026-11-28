/- GID: D5/S3/Quantum/AURICOmega/ThreeReadingContrast
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/ThreeReadingContrast
   mirror-E: none(waiver:exact-symbolic-proof)
   anchors: []
   utility: none
   digest: Classify all contrasts against a third point for a normalized rational Gram form. -/

import Mathlib.Algebra.Order.Ring.Rat
import D5.S3.Geometry.ThreeReadingContrast

namespace D5.S3.Quantum.AURICOmega.ThreeReadingContrast

/-- At fixed mutual reading `r`, the signed differences of nonnegative readings
against a third point fill exactly the rational slice of the closed unit disk.
Positivity is tested on all rational weights for the three sampled points. -/
theorem exists_nonnegative_readings_iff (r d : ℚ) :
    (∃ a b : ℚ, 0 ≤ a ∧ 0 ≤ b ∧ a - b = d ∧
      ∀ x y z : ℚ, 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 + 2 * (r * x * y + a * x * z + b * y * z)) ↔
    r ^ 2 + d ^ 2 ≤ 1 :=
  Omega.Geometry.ThreeReadingContrast.exists_nonnegative_readings_iff r d

end D5.S3.Quantum.AURICOmega.ThreeReadingContrast
