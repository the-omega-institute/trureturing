/- GID: D5/S3/SpinModels/PottsDefects/HardinA229584StripClasses5
   generality: G
   mirror-B: D5/B/S3/SpinModels/PottsDefects/HardinA229584StripClasses5
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/SpinModels/PottsDefects/HardinA229584Strip.result; premises=D5/S3/SpinModels/PottsDefects/HardinA229584StripClasses5.transition_counts
   digest: Transition counts for width-6 output classes 10 and 11. -/

/-
admission_basis: consumed-helper in HardinA229584Strip.result (#30580)
escape_witness: none
transition_counts: proof_shape=bind-only; consumers=HardinA229584Strip.finite_certificate
-/

import D5.S3.SpinModels.PottsDefects.HardinA229584StripClass10
import D5.S3.SpinModels.PottsDefects.HardinA229584StripClass11
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.SpinModels.PottsDefects.HardinA229584StripData
import D5.S3.SpinModels.PottsDefects.DefectTransfer

open scoped BigOperators
namespace D5.S3.SpinModels.PottsDefects.HardinA229584StripClasses5
open HardinA229584StripData
open DefectTransfer (bondDefects)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)

theorem transition_counts (s : Fin 32) (hs : 10 ≤ s.val ∧ s.val < 12) :
    ∀ p (d : Fin 2), Valid p d.val → Canonical p →
      (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
        cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s := by
  by_cases h : s.val < 11
  · exact HardinA229584StripClass10.transition_counts s ⟨hs.1, h⟩
  · exact HardinA229584StripClass11.transition_counts s ⟨by omega, hs.2⟩

end D5.S3.SpinModels.PottsDefects.HardinA229584StripClasses5
