/- GID: D5/S3/SpinModels/PottsDefects/HardinA229584StripClasses0
   generality: G
   mirror-B: D5/B/S3/SpinModels/PottsDefects/HardinA229584StripClasses0
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/SpinModels/PottsDefects/HardinA229584Strip.result; premises=D5/S3/SpinModels/PottsDefects/HardinA229584StripClasses0.transition_counts
   digest: Transition counts for width-6 output classes 0 and 1. -/

/-
admission_basis: consumed-helper in HardinA229584Strip.result (#30580)
escape_witness: none
transition_counts: proof_shape=bind-only; consumers=HardinA229584Strip.finite_certificate
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.SpinModels.PottsDefects.HardinA229584StripData
import D5.S3.SpinModels.PottsDefects.DefectTransfer

open scoped BigOperators
namespace D5.S3.SpinModels.PottsDefects.HardinA229584StripClasses0
open HardinA229584StripData
open DefectTransfer (bondDefects)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)

theorem transition_counts (s : Fin 32) (hs : 0 ≤ s.val ∧ s.val < 2) :
    ∀ p (d : Fin 2), Valid p d.val → Canonical p →
      (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
        cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s := by
  have h : s = 0 ∨ s = 1 := by omega
  rcases h with rfl | rfl
  · decide +kernel
  · decide +kernel

end D5.S3.SpinModels.PottsDefects.HardinA229584StripClasses0
