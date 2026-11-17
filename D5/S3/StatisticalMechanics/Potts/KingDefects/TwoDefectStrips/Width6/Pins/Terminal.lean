/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Pins/Terminal
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Pins/Terminal
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229753.result; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Certificate.transition_counts,D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Forward.structural_certificate
   digest: Coordinate certificates for the width-six transfer. -/
/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed helpers on the live path of HardinA229753.result)
certificate: proof_shape=content; consumers=Width6.Forward.structural_certificate
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
/-! Finite coordinate identities for exact-budget transfer. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Terminal
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate : ∀ p (d : Fin 3), Valid p d.val →
    terminal (cl p d.val) = (if d.val = 0 then 1 else 0) := by
  have h : ∀ a b c e f g : Fin 4, ∀ d : Fin 3,
      Valid (![a, b, c, e, f, g] : Row) d.val →
      terminal (cl (![a, b, c, e, f, g] : Row) d.val) =
        (if d.val = 0 then 1 else 0) := by
    intro a b
    fin_cases a <;> fin_cases b <;> decide +kernel
  intro p
  have he : p = ![p 0, p 1, p 2, p 3, p 4, p 5] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact h (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Terminal
