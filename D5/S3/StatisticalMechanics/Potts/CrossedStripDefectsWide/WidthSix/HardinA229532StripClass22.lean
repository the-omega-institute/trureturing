/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripClass22
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/WidthSix/HardinA229532StripClass22
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229532Strip.finite_certificate
   digest: Exact width-six one-defect HDA transfer. -/

/-
admission_basis: open-problem-resolution (#31328; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229532Strip.result)
transition_counts: proof_shape=bind-only; consumers=HardinA229532StripClasses.transition_counts
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

/-! Exact width-six HDA residual-budget transfer. -/
open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects
open D5.S3.Combinatorics.TraceAvoidingArrays
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass22
open DefectTransfer (bondDefects)
open HardinA229584StripData (Row horizontal antidiagonal)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option synthInstance.maxSize 100000
open HardinA229532StripData
open HardinA233177Canonical (Canonical)
theorem transition_counts : ∀ p (d : Fin 2), Valid p d.val → Canonical p →
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = 22
      then (1 : ℤ) else 0) = T (cl p d.val) 22 := by
  unfold Canonical
  intro p d
  fin_cases d <;> revert p <;> decide +kernel
end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripClass22
