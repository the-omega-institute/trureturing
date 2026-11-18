/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripClasses5
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripClasses5
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697Strip.finite_certificate
   digest: Block extension for exact two-defect HA strip counts. -/

/-
admission_basis: open-problem-resolution (#31299; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229697Strip.result)
transition_counts: proof_shape=bind-only; consumers=HardinA229697Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripClasses5
open HardinA229589StripData (Row horizontal between)
open HardinA229697StripData
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- New transitions using exactly two defects. -/
theorem transition_counts (j : Fin 14) (hj : 10 ≤ j.val ∧ j.val < 12) :
    ∀ p : Row,
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ 2 ∧
        cl r (2 - (bondDefects between p r + bondDefects horizontal r r)) = j.natAdd 28
        then (1 : ℤ) else 0) = T (cl p 2) (j.natAdd 28) := by
  have h : j = 10 ∨ j = 11 := by omega
  rcases h with rfl | rfl
  · intro p
    generalize h0 : p 0 = c0
    generalize h1 : p 1 = c1
    fin_cases c0 <;> fin_cases c1 <;> decide +kernel +revert
  · intro p
    generalize h0 : p 0 = c0
    generalize h1 : p 1 = c1
    fin_cases c0 <;> fin_cases c1 <;> decide +kernel +revert

end D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripClasses5
