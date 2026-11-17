/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/ForwardChecks/HardinA229585StripForward3
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/ForwardChecks/HardinA229585StripForward3
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/ForwardChecks/HardinA229585StripForward3.forward_steps
   digest: Shared enumeration of exact width-seven successor classes. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229585Strip.result)
forward_steps: proof_shape=bind-only; consumers=HardinA229585StripCertificate.structural_certificate
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData

/-! Two exact steps of the forward transfer table. -/
set_option profiler true
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.ForwardChecks.HardinA229585StripForward3
open HardinA229585StripData

attribute [local irreducible] W T

theorem forward_steps (i : Fin 2) :
    W ⟨6 + i.val + 1, by omega⟩ =
      Matrix.vecMul (W ⟨6 + i.val, by omega⟩) T := by
  fin_cases i <;> decide +kernel

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.ForwardChecks.HardinA229585StripForward3
