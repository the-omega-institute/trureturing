/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripClass0
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripClass0
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

/-! The exact successor count for target class 0. -/
open D5.S3.Combinatorics.TraceAvoidingArrays
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass0
open HardinA229531StripData
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem transition_counts : ∀ p (d : Fin 2), Valid p d.val →
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = 0
      then (1 : ℤ) else 0) = T (cl p d.val) 0 := by
  have cut : ∀ (p r : Row) (d : Fin 2),
      HardinThinGraphTransport.proper p ∧ d.val = 1 →
      ((bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = 0) ↔
        HardinThinGraphTransport.proper r ∧ HardinThinGraphTransport.compatible true p r ∧
          HardinA233126SquareStrip.boundaryClass (true, true) r = 1) := by decide +kernel
  have table : ∀ p (d : Fin 2),
      HardinThinGraphTransport.proper p ∧ d.val = 1 →
      HardinA233171DiagonalStrip.transfer
        (HardinA233126SquareStrip.boundaryClass (true, true) p) 1 / 32 =
          T (cl p d.val) 0 := by decide +kernel
  have remaining : ∀ p (d : Fin 2), Valid p d.val →
      ¬ (HardinThinGraphTransport.proper p ∧ d.val = 1) →
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = 0
        then (1 : ℤ) else 0) = T (cl p d.val) 0 := by decide +kernel
  intro p d hp
  by_cases hz : HardinThinGraphTransport.proper p ∧ d.val = 1
  · simp_rw [cut p _ d hz]
    have h := raw_successors p hz.1 1
    exact (Int.eq_ediv_of_mul_eq_right (by decide) h).trans (table p d hz)
  · exact remaining p d hp hz
end D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass0
