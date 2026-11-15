/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripClass14
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripClass14
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripClass14.transition_counts
   digest: Transition counts for width-6 output class 14. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229584Strip.result)
transition_counts: proof_shape=bind-only; consumers=HardinA229584StripClasses7.transition_counts
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripClass14
open HardinA229584StripData
open DefectTransfer (bondDefects)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)

theorem transition_counts (s : Fin 32) (hs : 14 ≤ s.val ∧ s.val < 15) :
    ∀ p (d : Fin 2), Valid p d.val → Canonical p →
      (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
        cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s := by
  have h : s = 14 := by omega
  subst s
  intro p d
  fin_cases d <;> revert p <;> decide +kernel

end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripClass14
