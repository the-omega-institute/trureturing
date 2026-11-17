/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClass7
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClass7
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
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripData

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClass7
open DefectTransfer (bondDefects)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option synthInstance.maxSize 100000
open HardinA229634StripData
open D5.S3.StatisticalMechanics.Potts.CrossedStripDefects
open HardinA229531StripData (Row horizontal between)

theorem transition_counts : ∀ p (d : Fin 3), Valid p d.val → Canonical p →
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = 27
      then (1 : ℤ) else 0) = T (cl p d.val) 27 := by
  have remaining : ∀ p (d : Fin 3), Valid p d.val → Canonical p →
      ¬ (d.val ≤ 1 ∧ HardinA229531StripData.Valid p d.val) →
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = 27
        then (1 : ℤ) else 0) = T (cl p d.val) 27 := by
    unfold Canonical
    intro p d
    fin_cases d <;> revert p <;> decide +kernel
  intro p d hp hn
  by_cases ho : d.val ≤ 1 ∧ HardinA229531StripData.Valid p d.val
  · exact HardinA229634StripCut.old_counts p ⟨d.val, by omega⟩ ho.2 7
  · exact remaining p d hp hn ho
end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClass7
