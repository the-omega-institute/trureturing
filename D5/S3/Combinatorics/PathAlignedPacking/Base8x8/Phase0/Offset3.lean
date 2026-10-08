/- GID: D5/S3/Combinatorics/PathAlignedPacking/Base8x8/Phase0/Offset3
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PathAlignedPacking/Base8x8/Phase0/Offset3
   mirror-E: none(waiver:semilinear-packing-construction)
   anchors: []
   utility: none
   digest: Universal separation inequalities for one phase and block offset. -/

import D5.S3.Combinatorics.PathAlignedPacking.Base8x8.Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PathAlignedPacking.Base8x8.Phase0.Offset3

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Defs Metric Schemes Data

theorem safe :
    ∀ (j h : Fin (scheme.a + scheme.b)) (ka kb r q : ℤ),
      Allowed scheme ka kb → 0 ≤ r → r ≤ runLimit scheme j ka kb →
      0 ≤ q → q ≤ runLimit scheme h ka kb →
      (3 = 0 → position scheme j ka kb r ≠ position scheme h ka kb q) →
      scheme.colour ⟨0, by decide +kernel⟩ j =
        scheme.colour ⟨(0 + 3) % scheme.period,
          Nat.mod_lt _ (by decide +kernel)⟩ h →
      (scheme.colour ⟨0, by decide +kernel⟩ j : ℤ) <
        chainSep (arcA scheme ka) (arcB scheme kb)
          (0, position scheme j ka kb r) (3, position scheme h ka kb q) := by
  intro j h ka kb r q hk hr hl hq hql hne heq
  rcases hk with ⟨hka, hkb, hka0, hkb0⟩
  fin_cases j <;> fin_cases h <;>
    simp [scheme] at heq <;>
    simp [scheme, runLimit, position, arcA, arcB, chainSep, cycleSep] at * <;>
    omega

end D5.S3.Combinatorics.PathAlignedPacking.Base8x8.Phase0.Offset3
