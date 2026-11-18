/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripClasses
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripClasses
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531Strip.finite_certificate
   digest: Exact HDA defect transfer and Hardin's registered recurrence. -/

/-
admission_basis: open-problem-resolution (#31121; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229531Strip.result)
transition_counts: proof_shape=bind-only; consumers=HardinA229531Strip.result
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass0
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass1
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass2
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass3
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass4
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass5
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass6
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass7
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass8
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass9
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass10
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass11
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass12
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass13
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass14
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass15
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass16
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass17
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass18
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClass19

/-! All target-class successor counts. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClasses
open HardinA229531StripData
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
theorem transition_counts : ∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 20,
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p d.val) s := by
  intro p d h s
  fin_cases s
  · exact HardinA229531StripClass0.transition_counts p d h
  · exact HardinA229531StripClass1.transition_counts p d h
  · exact HardinA229531StripClass2.transition_counts p d h
  · exact HardinA229531StripClass3.transition_counts p d h
  · exact HardinA229531StripClass4.transition_counts p d h
  · exact HardinA229531StripClass5.transition_counts p d h
  · exact HardinA229531StripClass6.transition_counts p d h
  · exact HardinA229531StripClass7.transition_counts p d h
  · exact HardinA229531StripClass8.transition_counts p d h
  · exact HardinA229531StripClass9.transition_counts p d h
  · exact HardinA229531StripClass10.transition_counts p d h
  · exact HardinA229531StripClass11.transition_counts p d h
  · exact HardinA229531StripClass12.transition_counts p d h
  · exact HardinA229531StripClass13.transition_counts p d h
  · exact HardinA229531StripClass14.transition_counts p d h
  · exact HardinA229531StripClass15.transition_counts p d h
  · exact HardinA229531StripClass16.transition_counts p d h
  · exact HardinA229531StripClass17.transition_counts p d h
  · exact HardinA229531StripClass18.transition_counts p d h
  · exact HardinA229531StripClass19.transition_counts p d h
end D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClasses
