/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripClass10
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripClass10
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

/-! The exact successor count for target class 10. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass10
open HardinA229531StripData
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem transition_counts : ∀ p (d : Fin 2), Valid p d.val →
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = 10
      then (1 : ℤ) else 0) = T (cl p d.val) 10 := by
  have remaining : ∀ p (d : Fin 2), Valid p d.val →
      ¬ (D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.proper p ∧
        d.val = 0) →
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = 10
        then (1 : ℤ) else 0) = T (cl p d.val) 10 := by decide +kernel
  intro p d hp
  by_cases hz : D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.proper p ∧
      d.val = 0
  · exact inherited_transition_counts p d ⟨10, by omega⟩ ⟨hz.1, by omega⟩
  · exact remaining p d hp hz
end D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass10
