/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripClassGroup1
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripClassGroup1
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698Strip.finite_certificate
   digest: The two-defect extension of the five-row HA quotient. -/

/-
admission_basis: open-problem-resolution (#31594; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229698Strip.result)
representative_rows: proof_shape=bind-only; consumers=HardinA229698StripNew.quotient_rows
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripData

/-! Exact three-colour counts on five-row HA strips with two defects. -/

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripClassGroup1
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
open D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590
open HardinA229698StripData

set_option maxRecDepth 100000
set_option Elab.async false

set_option maxHeartbeats 0 in
theorem representative_rows (i : Fin 6) (s : Fin 41) :
    (∑ c : Col, if HardinA229590StripData.cross (representatives ⟨6+i.val, by omega⟩)
      (column c) = 2 ∧ cls c = s then (1 : ℤ) else 0) =
      S ⟨6+i.val, by omega⟩ s := by
  fin_cases i <;> revert s <;> decide +kernel

end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripClassGroup1
