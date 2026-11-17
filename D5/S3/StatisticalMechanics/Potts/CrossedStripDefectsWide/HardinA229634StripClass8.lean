/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClass8
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClass8
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634Strip.finite_certificate
   digest: Exact width-five two-defect HDA transfer. -/

/-
admission_basis: open-problem-resolution (#31328; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229634Strip.result)
transition_counts: proof_shape=bind-only; consumers=HardinA229634Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripCut

open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClass8
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option synthInstance.maxSize 100000
open HardinA229634StripData
open D5.S3.StatisticalMechanics.Potts.CrossedStripDefects
open HardinA229531StripData (Row horizontal between)

theorem transition_counts : ∀ p (d : Fin 3), Valid p d.val →
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = 28
      then (1 : ℤ) else 0) = T (cl p d.val) 28 := by
  intro p
  generalize h0 : p 0 = c0
  generalize h1 : p 1 = c1
  fin_cases c0 <;> fin_cases c1 <;> decide +kernel +revert
end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClass8
