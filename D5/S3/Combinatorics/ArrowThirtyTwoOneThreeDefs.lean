/- GID: D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowThirtyTwoOneThreeDefs
   mirror-E: none(waiver:enumeration-of-the-arrow-pattern-32-1-to-3)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Catalan]
   utility: none
   digest: Definitions for the avoider count, its integer power series, and the Zhou--Yu cubic claim. -/

import D5.S3.Combinatorics.ArrowWilfDefs
import Mathlib.RingTheory.PowerSeries.Catalan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowThirtyTwoOneThreeDefs

open D5.S3.Combinatorics.ArrowWilfDefs

noncomputable section

local notation "X" => (PowerSeries.X : PowerSeries ℤ)

/-- The number of one-line permutations avoiding `(32; 1 → 3)`. -/
def count (n : ℕ) : ℕ :=
  (avoiders n [3, 2] [(1, 3)] 3).ncard

/-- The ordinary generating series of the avoider numbers. -/
def series : PowerSeries ℤ :=
  PowerSeries.mk fun n => (count n : ℤ)

/-- The cubic equation and its branch-uniqueness statement. -/
def claim : Prop :=
  1 + (3 * X - 2) * series + (1 - X) * (1 - 2 * X) * series ^ 2 +
      X ^ 3 * series ^ 3 = 0 ∧
    ∀ G : PowerSeries ℤ, PowerSeries.constantCoeff G = 1 →
      PowerSeries.coeff 1 G = 1 →
      1 + (3 * X - 2) * G + (1 - X) * (1 - 2 * X) * G ^ 2 +
          X ^ 3 * G ^ 3 = 0 →
        G = series

end
end D5.S3.Combinatorics.ArrowThirtyTwoOneThreeDefs
