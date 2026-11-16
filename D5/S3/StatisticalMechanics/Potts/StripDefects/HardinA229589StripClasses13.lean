/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripClasses13
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripClasses13
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589Strip.finite_certificate
   digest: Exact-budget transfer for Hardin's registered defective colourings. -/

/-
admission_basis: open-problem-resolution (#30838; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229589Strip.result)
transition_counts: proof_shape=bind-only; consumers=HardinA229589Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

/-! Counts for the indicated output-class interval. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses13
open HardinA229589StripData
open DefectTransfer (bondDefects)

theorem transition_counts (s : Fin 28) (hs : 26 ≤ s.val ∧ s.val < 28) :
    ∀ p (d : Fin 2), Valid p d.val →
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s := by
  have h : s = 26 ∨ s = 27 := by omega
  rcases h with rfl | rfl
  · decide +kernel
  · decide +kernel

end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses13
