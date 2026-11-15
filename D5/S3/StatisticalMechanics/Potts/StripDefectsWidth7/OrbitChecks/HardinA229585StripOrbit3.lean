/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/OrbitChecks/HardinA229585StripOrbit3
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/OrbitChecks/HardinA229585StripOrbit3
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/OrbitChecks/HardinA229585StripOrbit3.canonical_next
   digest: Shared enumeration of exact width-seven successor classes. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229585Strip.result)
canonical_next: proof_shape=bind-only; consumers=OrbitCertificate.canonical_next
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbit
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

set_option profiler true

/-! One interval of canonical input classes. -/
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.OrbitChecks.HardinA229585StripOrbit3
open HardinA229585StripData HardinA229585StripOrbit
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)

set_option profiler true in
theorem canonical_next :
    ∀ p : Boundary, ∀ d : Fin 2, Valid p d.val → Canonical p →
      24 ≤ (cl p d.val).val ∧ (cl p d.val).val < 32 →
      nextClasses p d.val = images (cl p d.val) := by
  unfold Canonical
  decide +kernel

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.OrbitChecks.HardinA229585StripOrbit3
