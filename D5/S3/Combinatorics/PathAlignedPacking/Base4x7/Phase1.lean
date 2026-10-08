/- GID: D5/S3/Combinatorics/PathAlignedPacking/Base4x7/Phase1
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PathAlignedPacking/Base4x7/Phase1
   mirror-E: none(waiver:semilinear-packing-construction)
   anchors: []
   utility: none
   digest: Universal separation inequalities for one block phase. -/

import D5.S3.Combinatorics.PathAlignedPacking.Base4x7.Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PathAlignedPacking.Base4x7.Phase1

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Defs Metric Schemes Data

theorem safe :
    ∀ (d : Fin 4) (j h : Fin (scheme.a + scheme.b)) (ka kb r q : ℤ),
      Allowed scheme ka kb → 0 ≤ r → r ≤ runLimit scheme j ka kb →
      0 ≤ q → q ≤ runLimit scheme h ka kb →
      (d.val = 0 → position scheme j ka kb r ≠ position scheme h ka kb q) →
      scheme.colour ⟨1, by decide +kernel⟩ j =
        scheme.colour ⟨(1 + d.val) % scheme.period,
          Nat.mod_lt _ (by decide +kernel)⟩ h →
      (scheme.colour ⟨1, by decide +kernel⟩ j : ℤ) <
        chainSep (arcA scheme ka) (arcB scheme kb)
          (0, position scheme j ka kb r) (d.val, position scheme h ka kb q) := by
  intro d j h ka kb r q hk hr hl hq hql hne heq
  rcases hk with ⟨hka, hkb, hka0, hkb0⟩
  fin_cases d <;> fin_cases j <;> fin_cases h <;>
    simp [scheme] at heq <;>
    simp [scheme, runLimit, position, arcA, arcB, chainSep, cycleSep] at * <;>
    omega

end D5.S3.Combinatorics.PathAlignedPacking.Base4x7.Phase1
