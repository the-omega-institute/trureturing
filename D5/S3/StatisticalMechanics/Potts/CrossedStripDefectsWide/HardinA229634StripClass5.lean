/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClass5
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/HardinA229634StripClass5
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
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClass5
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
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = 25
      then (1 : ℤ) else 0) = T (cl p d.val) 25 := by
  have table : ∀ p, HardinA229531StripData.Valid p 0 →
      HardinA229531StripData.T (HardinA229531StripData.cl p 0) 11 = T (cl p 0) 25 := by
    decide +kernel
  have remaining : ∀ p (d : Fin 3), Valid p d.val →
      ¬ (d.val = 0 ∧ HardinA229531StripData.Valid p 0) →
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = 25
        then (1 : ℤ) else 0) = T (cl p d.val) 25 := by
    intro p
    generalize h0 : p 0 = c0
    generalize h1 : p 1 = c1
    fin_cases c0 <;> fin_cases c1 <;> decide +kernel +revert
  intro p d hp
  by_cases hz : d.val = 0 ∧ HardinA229531StripData.Valid p 0
  · simp only [hz.1]
    simp_rw [HardinA229634StripCut.zero_cut p _ 5]
    exact (HardinA229531StripClasses.transition_counts p 0 hz.2 11).trans (table p hz.2)
  · exact remaining p d hp hz
end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.HardinA229634StripClass5
