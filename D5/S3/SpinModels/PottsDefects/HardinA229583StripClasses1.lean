/- GID: D5/S3/SpinModels/PottsDefects/HardinA229583StripClasses1
   generality: G
   mirror-B: D5/B/S3/SpinModels/PottsDefects/HardinA229583StripClasses1
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/SpinModels/PottsDefects/HardinA229583Strip.result; premises=D5/S3/SpinModels/PottsDefects/HardinA229583StripClasses1.transition_counts
   digest: Transition counts for width-five output classes 2 and 3. -/

/-
admission_basis: consumed-helper in HardinA229583Strip.result (#30580)
escape_witness: none
transition_counts: proof_shape=bind-only; consumers=HardinA229583Strip.finite_certificate
-/

import D5.S3.SpinModels.PottsDefects.HardinA229583StripData
import D5.S3.SpinModels.PottsDefects.DefectTransfer

open scoped BigOperators
namespace D5.S3.SpinModels.PottsDefects.HardinA229583StripClasses1
open HardinA229583StripData
open DefectTransfer (bondDefects)

theorem transition_counts (s : Fin 14) (hs : 2 ≤ s.val ∧ s.val < 4) :
    ∀ p (d : Fin 2), Valid p d.val →
      (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
        cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s := by
  revert s
  decide +kernel

end D5.S3.SpinModels.PottsDefects.HardinA229583StripClasses1
