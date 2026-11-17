/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes37
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes37
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229752.result; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Certificate.transition_counts,D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Forward.structural_certificate
   digest: Width-five exact-budget transfer measurement. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed helpers on the live path of HardinA229752.result)
class_successors: proof_shape=content; consumers=Width5.Certificate.canonical_successors
-/

import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
/-! A single output class of the canonical-boundary defect transfer. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Classes37
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
private local instance (p : Row) : Decidable
    (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p) := by
  unfold D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  infer_instance
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem class_successors : ∀ p (d : Fin 3), Valid p d.val →
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical p →
    cl p d.val = (37 : Fin 43) → successors p d.val = classList 37 := by
  have h : ∀ i : Fin (4^5), ∀ d : Fin 3,
      Valid (finFunctionFinEquiv.symm i) d.val →
      D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
        (finFunctionFinEquiv.symm i) →
      cl (finFunctionFinEquiv.symm i) d.val = (37 : Fin 43) →
      successors (finFunctionFinEquiv.symm i) d.val = classList 37 := by
    decide +kernel
  intro p
  simpa only [Equiv.symm_apply_apply] using h (finFunctionFinEquiv p)
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Classes37
