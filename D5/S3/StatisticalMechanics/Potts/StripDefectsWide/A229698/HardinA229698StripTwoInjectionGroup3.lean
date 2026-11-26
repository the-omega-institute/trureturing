/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripTwoInjectionGroup3
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripTwoInjectionGroup3
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698Strip.finite_certificate
   digest: The two-defect extension of the five-row HA quotient. -/

/-
admission_basis: open-problem-resolution (#31594; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229698Strip.result)
rows: proof_shape=bind-only; consumers=HardinA229698StripInjection.injection_powers
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTables

/-! Exact three-colour counts on five-row HA strips with two defects. -/

namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTwoInjectionGroup3
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
open HardinA229698StripData
open HardinA229698StripTables

set_option maxRecDepth 100000
set_option Elab.async false

set_option maxHeartbeats 0 in
theorem rows (k : Fin 3) :
    S.mulVec (W ⟨9+k.val, by omega⟩) = SQ ⟨9+k.val, by omega⟩ := by
  fin_cases k <;> exact List.ofFn_inj.mp rfl

end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTwoInjectionGroup3
