/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA229583StripClasses6
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA229583StripClasses6
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA229583Strip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA229583StripClasses6.transition_counts
   digest: Transition counts for width-five output classes 12 and 13. -/

/-
admission_basis: consumed-helper in HardinA229583Strip.result (#30580)
escape_witness: none
transition_counts: proof_shape=bind-only; consumers=HardinA229583Strip.finite_certificate
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA229583StripData
import D5.S3.Combinatorics.TraceAvoidingArrays.DefectTransfer

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA229583StripClasses6
open HardinA229583StripData
open DefectTransfer (bondDefects)

theorem transition_counts (s : Fin 14) (hs : 12 ≤ s.val ∧ s.val < 14) :
    ∀ p (d : Fin 2), Valid p d.val →
      (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
        cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s := by
  revert s
  decide +kernel

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA229583StripClasses6
