/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Pins/Terminal
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Pins/Terminal
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Coordinate certificates for the width-six transfer. -/
/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed helpers on the live path of HardinA229753.result)
certificate: proof_shape=content; consumers=Width6.Forward.structural_certificate
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
/-! Finite coordinate identities for exact-budget transfer. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Terminal
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate : ∀ p (d : Fin 3), Valid p d.val →
    terminal (cl p d.val) = (if d.val = 0 then 1 else 0) := by
  have h : ∀ (i : Fin (4^6)) (d : Fin 3), Valid (finFunctionFinEquiv.symm i) d.val →
      terminal (cl (finFunctionFinEquiv.symm i) d.val) = (if d.val = 0 then 1 else 0) := by
    decide +kernel
  intro p
  simpa only [Equiv.symm_apply_apply] using h (finFunctionFinEquiv p)

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Terminal
