/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/Budget0/Block1/HardinA229585StripClass45
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/Budget0/Block1/HardinA229585StripClass45
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/Budget0/Block1/HardinA229585StripClass45.transition_counts
   digest: Width-7 output class 45 at residual budget 0. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229585Strip.result)
transition_counts: proof_shape=bind-only; consumers=HardinA229585Strip.transition_counts
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass45
open D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)

theorem transition_counts :
    ∀ p : Boundary, Valid p 0 → Canonical p →
      (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ 0 ∧
        cl (boundary r) (0 - (cross p r + bondDefects horizontal r r)) = (45 : Fin 72)
        then (1 : ℤ) else 0) = T (cl p 0) 45 := by
  decide +kernel

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget0.Block1.HardinA229585StripClass45
