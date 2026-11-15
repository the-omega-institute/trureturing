/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripClasses9
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripClasses9
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.finite_certificate
   digest: Exact-budget transfer for Hardin's registered defective colourings. -/

/-
admission_basis: open-problem-resolution (#30838; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229691Strip.result)
transition_counts: proof_shape=bind-only; consumers=HardinA229691Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData

/-! Counts for the indicated output-class interval. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripClasses9
open HardinA229691StripData
open HardinA229583StripData (Row Boundary horizontal antidiagonal boundary cross)
open DefectTransfer (bondDefects)

theorem transition_counts (s : Fin 27) (hs : 18 ≤ s.val ∧ s.val < 20) :
    ∀ p (d : Fin 3), Valid p d.val →
      (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
        cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s := by
  have h : s = 18 ∨ s = 19 := by omega
  rcases h with rfl | rfl
  · decide +kernel
  · decide +kernel

end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripClasses9
