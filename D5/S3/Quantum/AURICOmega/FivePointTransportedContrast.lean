/- GID: D5/S3/Quantum/AURICOmega/FivePointTransportedContrast
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/FivePointTransportedContrast
   mirror-E: none(waiver:exact-symbolic-proof)
   anchors: []
   utility: none
   digest: Classify rational reading differences with both local transported points. -/

import Mathlib.Algebra.Order.Field.Rat
import OmegaMath.Geometry.FivePointTransportedContrast

namespace D5.S3.Quantum.AURICOmega.FivePointTransportedContrast

/-- Both transported points can occur in one normalized nonnegative rational Gram
form. The four prescribed entries in the transported columns are b, t and a, t.
The signed difference has the stated exact range. -/
theorem exists_transported_readings_iff (t d : ℚ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∃ a b c e r : ℚ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ e ∧ 0 ≤ r ∧ a - b = d ∧
      ∀ x y z w v : ℚ, 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 + v ^ 2 +
        2 * (t * (x * y + z * w + z * v) + a * (x * z + y * v) +
          b * (y * z + x * w) + c * y * w + e * x * v + r * w * v)) ↔
    d ^ 2 ≤ if t ≤ 1 / 2 then (1 - t ^ 2) ^ 2
      else if (t - 1 / 2) ^ 2 ≤ 1 - t ^ 2 then (5 / 4 - t) ^ 2
      else (2 * t - 1) ^ 2 * (1 - t ^ 2) :=
  Omega.Geometry.FivePointTransportedContrast.exists_transported_readings_iff t d ht ht1

end D5.S3.Quantum.AURICOmega.FivePointTransportedContrast
