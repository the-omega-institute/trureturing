/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripClass18
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripClass18
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531Strip.finite_certificate
   digest: Exact HDA defect transfer and Hardin's registered recurrence. -/

/-
admission_basis: open-problem-resolution (#31121; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229531Strip.result)
transition_counts: proof_shape=bind-only; consumers=HardinA229531Strip.result
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripData

/-! The exact successor count for target class 18. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass18
open HardinA229531StripData
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem transition_counts : ∀ p (d : Fin 2), Valid p d.val →
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = 18
      then (1 : ℤ) else 0) = T (cl p d.val) 18 := by
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +kernel +revert
end D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass18
