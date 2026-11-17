/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/Initial/HardinA229585StripCounts7
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/Initial/HardinA229585StripCounts7
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/Initial/HardinA229585StripCounts7.initial_counts
   digest: Width-7 initial histogram on classes 56 through 63. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229585Strip.result)
initial_counts: proof_shape=bind-only; consumers=HardinA229585StripCertificate.structural_certificate
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

set_option profiler true

/-! Exact finite certificates for the width-seven one-defect strip. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Initial.HardinA229585StripCounts7
open D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)

set_option maxHeartbeats 1000000 in
theorem initial_counts (s : Fin 72) (hs : 56 ≤ s.val ∧ s.val < 64) :
    (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl (boundary r) (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s := by
  have h : s = 56 ∨ s = 57 ∨ s = 58 ∨ s = 59 ∨ s = 60 ∨ s = 61 ∨ s = 62 ∨ s = 63 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Initial.HardinA229585StripCounts7
