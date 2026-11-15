/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/Initial/HardinA229585StripCounts4
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/Initial/HardinA229585StripCounts4
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/Initial/HardinA229585StripCounts4.initial_counts
   digest: Width-7 initial histogram on classes 32 through 39. -/

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
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Initial.HardinA229585StripCounts4
open D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)

set_option maxHeartbeats 1000000 in
theorem initial_counts (s : Fin 72) (hs : 32 ≤ s.val ∧ s.val < 40) :
    (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl (boundary r) (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s := by
  have h : s = 32 ∨ s = 33 ∨ s = 34 ∨ s = 35 ∨ s = 36 ∨ s = 37 ∨ s = 38 ∨ s = 39 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Initial.HardinA229585StripCounts4
